(** * Tuple indexes with stored prefix nodes

    Indexes store cell edges, live suffix counts and terminal prefix nodes.
    For example, removing one tuple preserves a prefix shared with another tuple.
    Builds on: IndexSig and positive-key tries. *)

From Stdlib Require Import List PArith NArith PeanoNat Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig Syntax IndexSig.

Import List.ListNotations.

(** * Cardinality of updates to an edge trie *)

Module TrieCardinalityFacts.

  (** An enumerated key is exactly a key with a stored value. *)
  Lemma elements_key_iff : forall A (m : PTrieCode.t A) k,
    In k (map fst (PTrieCode.elements m)) <-> exists v, PTrieCode.get k m = Some v.
  Proof.
    intros A m k. split.
    - intro Hin. apply in_map_iff in Hin.
      destruct Hin as [[q v] [Heq Hin]]. cbn [fst] in Heq. subst q.
      exists v. now apply PTrie.elements_spec.
    - intros [v Hget]. apply in_map_iff. exists (k, v). split; [reflexivity|].
      now apply PTrie.elements_spec.
  Qed.

  (** Setting a key adds that key to the enumerated key set. *)
  Lemma elements_set_key_iff : forall A k (v : A) m q,
    In q (map fst (PTrieCode.elements (PTrieCode.set k v m))) <->
      q = k \/ In q (map fst (PTrieCode.elements m)).
  Proof.
    intros A k v m q. rewrite !elements_key_iff.
    destruct (Pos.eq_dec q k) as [Heq | Hneq].
    - subst q. rewrite PTrie.get_set_same. split.
      + intro Hget. now left.
      + intro Hin. exists v. reflexivity.
    - rewrite PTrie.get_set_other by exact Hneq. split.
      + intro Hget. now right.
      + intros [Heq | Hget]; [contradiction | exact Hget].
  Qed.

  (** Removing a key retains exactly the other enumerated keys. *)
  Lemma elements_remove_key_iff : forall A k (m : PTrieCode.t A) q,
    In q (map fst (PTrieCode.elements (PTrieCode.remove k m))) <->
      In q (map fst (PTrieCode.elements m)) /\ q <> k.
  Proof.
    intros A k m q. rewrite !elements_key_iff.
    destruct (Pos.eq_dec q k) as [Heq | Hneq].
    - subst q. rewrite PTrie.get_remove_same. split.
      + intros [v Hget]. discriminate.
      + intros [_ Hneq]. contradiction.
    - rewrite PTrie.get_remove_other by exact Hneq. tauto.
  Qed.

  (** Replacing an existing value leaves the number of edge bindings unchanged. *)
  Lemma set_present : forall A k (old v : A) m, PTrieCode.get k m = Some old ->
    length (PTrieCode.elements (PTrieCode.set k v m)) = length (PTrieCode.elements m).
  Proof.
    intros A k old v m Hget.
    assert (Hkey : In k (map fst (PTrieCode.elements m))).
    { apply elements_key_iff. now exists old. }
    assert (Hperm : Permutation (map fst (PTrieCode.elements (PTrieCode.set k v m)))
      (map fst (PTrieCode.elements m))).
    { apply NoDup_Permutation; [apply PTrie.elements_nodup | apply PTrie.elements_nodup |].
      intro q. rewrite elements_set_key_iff. split.
      - intros [Heq | Hin]; [subst q; exact Hkey | exact Hin].
      - intro Hin. now right. }
    apply Permutation_length in Hperm. now rewrite !length_map in Hperm.
  Qed.

  (** Inserting a fresh key contributes exactly one edge binding. *)
  Lemma set_absent : forall A k (v : A) m, PTrieCode.get k m = None ->
    length (PTrieCode.elements (PTrieCode.set k v m)) = S (length (PTrieCode.elements m)).
  Proof.
    intros A k v m Habsent.
    assert (Hperm : Permutation (map fst (PTrieCode.elements (PTrieCode.set k v m)))
      (k :: map fst (PTrieCode.elements m))).
    { apply NoDup_Permutation.
      - apply PTrie.elements_nodup.
      - constructor.
        + intro Hin. apply elements_key_iff in Hin. destruct Hin as [old Hget]. congruence.
        + apply PTrie.elements_nodup.
      - intro q. rewrite elements_set_key_iff. cbn [In]. intuition congruence. }
    apply Permutation_length in Hperm. cbn [length] in Hperm.
    now rewrite !length_map in Hperm.
  Qed.

  (** Removing an existing key removes exactly one edge binding. *)
  Lemma remove_present : forall A k (old : A) m, PTrieCode.get k m = Some old ->
    S (length (PTrieCode.elements (PTrieCode.remove k m))) = length (PTrieCode.elements m).
  Proof.
    intros A k old m Hget.
    assert (Hkey : In k (map fst (PTrieCode.elements m))).
    { apply elements_key_iff. now exists old. }
    assert (Hperm : Permutation (map fst (PTrieCode.elements m))
      (k :: map fst (PTrieCode.elements (PTrieCode.remove k m)))).
    { apply NoDup_Permutation.
      - apply PTrie.elements_nodup.
      - constructor.
        + intro Hin. apply elements_remove_key_iff in Hin. destruct Hin as [_ Hneq]. contradiction.
        + apply PTrie.elements_nodup.
      - intro q. cbn [In]. rewrite elements_remove_key_iff. split.
        + intro Hin. destruct (Pos.eq_dec q k) as [Heq | Hneq].
          * left. symmetry. exact Heq.
          * right. now split.
        + intros [Heq | [Hin _]]; [subst q; exact Hkey | exact Hin]. }
    apply Permutation_length in Hperm. cbn [length] in Hperm.
    rewrite !length_map in Hperm. symmetry. exact Hperm.
  Qed.

  (** Removing an absent key leaves the number of edge bindings unchanged. *)
  Lemma remove_absent : forall A k (m : PTrieCode.t A), PTrieCode.get k m = None ->
    length (PTrieCode.elements (PTrieCode.remove k m)) = length (PTrieCode.elements m).
  Proof.
    intros A k m Habsent.
    assert (Hperm : Permutation (map fst (PTrieCode.elements (PTrieCode.remove k m)))
      (map fst (PTrieCode.elements m))).
    { apply NoDup_Permutation; [apply PTrie.elements_nodup | apply PTrie.elements_nodup |].
      intro q. rewrite elements_remove_key_iff. split.
      - intros [Hin _]. exact Hin.
      - intro Hin. split; [exact Hin |]. intro Heq. subst q.
        apply elements_key_iff in Hin. destruct Hin as [old Hget]. congruence. }
    apply Permutation_length in Hperm. now rewrite !length_map in Hperm.
  Qed.

  (** Distinct entries assigned identifiers above one fit below the allocation counter. *)
  Lemma bounded_positive_length : forall A (key : A -> positive) xs bound,
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> key x = key y -> x = y) ->
    (forall x, In x xs -> (1 < key x <= bound)%positive) ->
    length xs <= Pos.to_nat bound - 1.
  Proof.
    intros A key xs bound Hnodup Hinjective Hbounded.
    assert (Hkeys : NoDup (map (fun x => Pos.to_nat (key x)) xs)).
    { apply NoDup_map_NoDup_ForallPairs; [|exact Hnodup].
      intros x y Hx Hy Heq. apply (Hinjective x y Hx Hy). now apply Pos2Nat.inj. }
    assert (Hinclude : incl (map (fun x => Pos.to_nat (key x)) xs)
      (seq 2 (Pos.to_nat bound - 1))).
    { intros n Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq Hx]]. subst n.
      destruct (Hbounded x Hx) as [Hlower Hupper].
      apply Pos2Nat.inj_lt in Hlower. apply Pos2Nat.inj_le in Hupper.
      change (1 < Pos.to_nat (key x)) in Hlower.
      pose proof (Pos2Nat.is_pos bound). apply in_seq. lia. }
    assert (Hlength : length (map (fun x => Pos.to_nat (key x)) xs) <=
      length (seq 2 (Pos.to_nat bound - 1))).
    { apply NoDup_incl_length; assumption. }
    rewrite length_map, length_seq in Hlength. exact Hlength.
  Qed.

End TrieCardinalityFacts.

Module Nat.
  TimeFun Nat.max.
End Nat.
Import Nat.

(** * Consequences of the abstract index laws *)

Module IndexFacts (V : VALUE) (I : INDEX V).
  (** A live nonempty prefix of full arity is a stored tuple. *)
  Lemma node_full_mem : forall a ix n pre, I.wf a ix -> I.node ix n pre ->
    length pre = a -> pre <> [] -> I.mem ix pre.
  Proof.
    intros a ix n pre Hwf Hnode Hlength Hnonempty.
    destruct (I.node_live a ix n pre Hwf Hnode Hnonempty) as [suf Hmember].
    pose proof (I.mem_arity a ix (pre ++ suf) Hwf Hmember) as Harity.
    rewrite length_app, Hlength in Harity.
    assert (Hsuf : length suf = 0) by lia.
    apply length_zero_iff_nil in Hsuf. subst suf.
    now rewrite app_nil_r in Hmember.
  Qed.

  (** A member extending a live prefix supplies the next child. *)
  Lemma child_of_member : forall a ix n pre c suf, I.wf a ix -> I.node ix n pre ->
    I.mem ix (pre ++ c :: suf) -> exists m, I.child ix n c = Some m.
  Proof.
    intros a ix n pre c suf Hwf Hnode Hmember.
    destruct (I.child ix n c) as [m |] eqn:Hchild.
    - now exists m.
    - exfalso.
      apply (proj1 (proj2 (I.child_spec a ix n pre c Hwf Hnode)) Hchild).
      now exists suf.
  Qed.
End IndexFacts.

Module IndexTimeFacts (V : VALUE_T) (I : INDEX_T V).
  Module C := CellKey V.

  (** Incrementing a positive counter adds at most one encoded bit. *)
  Lemma counter_bits_succ : forall p, Pos.size_nat (Pos.succ p) <= Pos.size_nat p + 1.
  Proof.
    intro p. induction p; cbn [Pos.succ Pos.size_nat]; lia.
  Qed.

  (** Navigation without a query cell pays for the counter and stored cell width. *)
  Lemma width_empty : forall ix,
    I.width ix [] <= Pos.size_nat (I.next ix) + I.max_cell_bits ix + 1.
  Proof.
    intro ix. pose proof (I.width_le ix []) as Hwidth.
    change (I.width ix [] <=
      Pos.size_nat (I.next ix + 1)%positive + 0 + I.max_cell_bits ix) in Hwidth.
    rewrite Pos.add_1_r in Hwidth.
    pose proof (counter_bits_succ (I.next ix)). lia.
  Qed.

  (** A one-cell probe adds only that cell's encoding to the stored-width budget. *)
  Lemma width_singleton : forall ix c,
    I.width ix [c] <=
      Pos.size_nat (I.next ix) + I.max_cell_bits ix + cell_bits V.encode c + 1.
  Proof.
    intros ix c. pose proof (I.width_le ix [c]) as Hwidth.
    change (I.width ix [c] <= Pos.size_nat (I.next ix + 1)%positive +
      Nat.max (cell_bits V.encode c) 0 + I.max_cell_bits ix) in Hwidth.
    rewrite Pos.add_1_r, Nat.max_0_r in Hwidth.
    pose proof (counter_bits_succ (I.next ix)). lia.
  Qed.

  (** Every enumerated child has an encoding covered by the stored cell width. *)
  Lemma child_bits : forall a ix n pre c, I.wf a ix -> I.node ix n pre ->
    In c (I.children ix n) -> cell_bits V.encode c <= I.max_cell_bits ix.
  Proof.
    intros a ix n pre c Hwf Hnode Hin.
    destruct (I.children_spec a ix n pre c Hwf Hnode) as [Hchildren _].
    destruct (proj1 Hchildren Hin) as [m Hchild].
    assert (Hchildnode : I.node ix m (pre ++ [c])).
    { apply (proj1 (proj1 (I.child_spec a ix n pre c Hwf Hnode) m)).
      exact Hchild. }
    assert (Hnonempty : pre ++ [c] <> []) by (destruct pre; discriminate).
    destruct (I.node_live a ix m (pre ++ [c]) Hwf Hchildnode Hnonempty)
      as [suf Hmember].
    eapply I.max_cell_bits_mem; [exact Hwf | exact Hmember |].
    apply in_or_app. left. apply in_or_app. right. now left.
  Qed.

  (** Distinct cells retain distinct natural-number encodings. *)
  Lemma cell_codes_nodup : forall cs, NoDup cs ->
    NoDup (map (fun c => Pos.to_nat (C.encode c)) cs).
  Proof.
    intros cs Hnodup. induction Hnodup as [| c cs Habsent Hnodup IH].
    - constructor.
    - cbn [map]. constructor; [| exact IH].
      intro Hin. apply in_map_iff in Hin as [d [Hcode Hin]].
      apply Pos2Nat.inj in Hcode. apply C.encode_inj in Hcode. subst d.
      exact (Habsent Hin).
  Qed.

  (** The distinct positive child encodings fit below the width's power of two. *)
  Lemma degree_count : forall a ix n pre, I.wf a ix -> I.node ix n pre ->
    N.to_nat (I.degree ix n) < Nat.pow 2 (I.max_cell_bits ix).
  Proof.
    intros a ix n pre Hwf Hnode.
    pose proof (proj2 (I.children_spec a ix n pre (Id 1%positive) Hwf Hnode))
      as Hnodup.
    pose proof (cell_codes_nodup _ Hnodup) as Hcodes.
    assert (Hrange : incl (map (fun c => Pos.to_nat (C.encode c)) (I.children ix n))
      (seq 1 (Nat.pow 2 (I.max_cell_bits ix) - 1))).
    { intros code Hin. apply in_map_iff in Hin as [c [<- Hin]].
      apply in_seq.
      pose proof (Pos2Nat.is_pos (C.encode c)) as Hpositive.
      pose proof (Pos.size_nat_upper (C.encode c)) as Hupper.
      pose proof (child_bits a ix n pre c Hwf Hnode Hin) as Hbits.
      assert (Hwidth : Pos.size_nat (C.encode c) <= I.max_cell_bits ix)
        by (destruct c; exact Hbits).
      pose proof (Nat.pow_le_mono_r 2 _ _ ltac:(lia) Hwidth) as Hpow.
      pose proof (Nat.pow_lower_bound 2 (I.max_cell_bits ix) ltac:(lia)) as Hnonzero.
      lia. }
    pose proof (NoDup_incl_length Hcodes Hrange) as Hlength.
    rewrite length_map, length_seq in Hlength.
    rewrite (I.degree_spec a ix n pre Hwf Hnode).
    pose proof (Nat.pow_lower_bound 2 (I.max_cell_bits ix) ltac:(lia)) as Hnonzero.
    eapply Nat.le_lt_trans; [exact Hlength |].
    apply Nat.sub_lt; [exact Hnonzero | lia].
  Qed.

  (** A stored node's degree uses no more bits than its widest child cell. *)
  Lemma degree_bits : forall a ix n pre, I.wf a ix -> I.node ix n pre ->
    N.size_nat (I.degree ix n) <= I.max_cell_bits ix.
  Proof.
    intros a ix n pre Hwf Hnode.
    pose proof (degree_count a ix n pre Hwf Hnode) as Hcount.
    destruct (I.degree ix n) as [| degree] eqn:Hdegree.
    - cbn [N.size_nat]. lia.
    - cbn [N.size_nat N.to_nat] in *.
      now apply Pos.size_nat_least.
  Qed.
End IndexTimeFacts.

(** An edge retains its original cell and the number of live suffixes below its child. *)
Record index_edge (C : Type) := IndexEdge {
  edge_cell : C;
  edge_child : positive;
  edge_count : N
}.

(** Each allocated prefix has a cell map, cached degree and terminal marker. *)
Record index_node (C : Type) := IndexNode {
  node_edges : PTrieCode.t (index_edge C);
  node_degree : N;
  node_terminal : bool
}.

(** The counter retains allocated node identifiers even after their edges are removed. *)
Record index_state (C : Type) := IndexState {
  index_counter : positive;
  index_nodes : PTrieCode.t (index_node C);
  index_cell_width : nat
}.

Arguments IndexEdge {C}.
Arguments edge_cell {C}.
Arguments edge_child {C}.
Arguments edge_count {C}.
Arguments IndexNode {C}.
Arguments node_edges {C}.
Arguments node_degree {C}.
Arguments node_terminal {C}.
Arguments IndexState {C}.
Arguments index_counter {C}.
Arguments index_nodes {C}.
Arguments index_cell_width {C}.

TimeFun edge_cell.
TimeFun edge_child.
TimeFun edge_count.
TimeFun node_edges.
TimeFun node_degree.
TimeFun node_terminal.
TimeFun index_counter.
TimeFun index_nodes.
TimeFun index_cell_width.

Module IndexCode (V : VALUE_OPS) <: INDEX_OPS V.
  Definition t := index_state (cell V.t).
  Definition empty_node : index_node (cell V.t) := IndexNode PTrieCode.empty 0%N false.
  Definition empty : t := IndexState 1%positive PTrieCode.empty 0.
  Definition next (ix : t) : positive := index_counter ix.
  Definition root (_ : t) : positive := 1%positive.

  Definition encode_cell (c : cell V.t) : positive :=
    match c with Id i => xO i | Val v => xI (V.encode v) end.

  Definition read_node (ix : t) (n : positive) : index_node (cell V.t) :=
    match PTrieCode.get n (index_nodes ix) with Some nd => nd | None => empty_node end.

  Definition child (ix : t) (n : positive) (c : cell V.t) : option positive :=
    if Pos.ltb (next ix) n then None else
      match PTrieCode.get (encode_cell c) (node_edges (read_node ix n)) with
      | Some edge => Some (edge_child edge)
      | None => None
      end.

  Definition children (ix : t) (n : positive) : list (cell V.t) :=
    if Pos.ltb (next ix) n then [] else
      map (fun entry => edge_cell (snd entry))
        (PTrieCode.elements (node_edges (read_node ix n))).

  Definition degree (ix : t) (n : positive) : N :=
    if Pos.ltb (next ix) n then 0%N else node_degree (read_node ix n).

  Fixpoint seek (ix : t) (n : positive) (r : list (cell V.t)) : option positive :=
    match r with
    | [] => Some n
    | c :: rest => match child ix n c with None => None | Some m => seek ix m rest end
    end.

  Definition contains_from (n : positive) (r : list (cell V.t)) (ix : t) : bool :=
    match seek ix n r with
    | None => false
    | Some m => node_terminal (read_node ix m)
    end.

  Definition contains (r : list (cell V.t)) (ix : t) : bool :=
    contains_from (root ix) r ix.

  Definition tuple_bits (r : list (cell V.t)) : nat :=
    fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r.

  (** Reject oversized malformed counters before performing binary arithmetic on them. *)
  Definition bounded_succ (limit : positive) (n : N) : N :=
    if N.ltb (Npos limit) n then 0%N else N.succ n.

  Definition write_node (ix : t) (n : positive) (nd : index_node (cell V.t))
      (counter : positive) : t :=
    IndexState counter (PTrieCode.set n nd (index_nodes ix)) (index_cell_width ix).

  Definition walk_state := (t * positive)%type.
  Definition start (ix : t) : walk_state := (ix, root ix).

  Definition insert_step_st (st : walk_state) (c : cell V.t) : walk_state :=
    let '(ix, n) := st in
    if Pos.ltb (next ix) n then st else
      let nd := read_node ix n in
      let code := encode_cell c in
      match PTrieCode.get code (node_edges nd) with
      | Some edge =>
        let updated := IndexEdge c (edge_child edge) (bounded_succ (next ix) (edge_count edge)) in
        (write_node ix n
          (IndexNode (PTrieCode.set code updated (node_edges nd))
            (node_degree nd) (node_terminal nd)) (next ix), edge_child edge)
      | None =>
        let m := Pos.succ (next ix) in
        (write_node ix n
          (IndexNode (PTrieCode.set code (IndexEdge c m 1%N) (node_edges nd))
            (bounded_succ (next ix) (node_degree nd)) (node_terminal nd)) m, m)
      end.

  Definition insert_step (ix : t) (n : positive) (c : cell V.t) : t :=
    fst (insert_step_st (ix, n) c).

  Definition remove_step_st (st : walk_state) (c : cell V.t) : walk_state :=
    let '(ix, n) := st in
    if Pos.ltb (next ix) n then st else
      let nd := read_node ix n in
      let code := encode_cell c in
      match PTrieCode.get code (node_edges nd) with
      | None => st
      | Some edge =>
        let nd' :=
          if N.eqb (edge_count edge) 1%N then
            IndexNode (PTrieCode.remove code (node_edges nd))
              (N.pred (node_degree nd)) (node_terminal nd)
          else
            IndexNode (PTrieCode.set code
              (IndexEdge (edge_cell edge) (edge_child edge) (N.pred (edge_count edge)))
              (node_edges nd)) (node_degree nd) (node_terminal nd) in
        (write_node ix n nd' (next ix), edge_child edge)
      end.

  Definition mark_terminal (ix : t) (n : positive) (present : bool) (bits : nat) : t :=
    let nd := read_node ix n in
    IndexState (next ix)
      (PTrieCode.set n (IndexNode (node_edges nd) (node_degree nd) present) (index_nodes ix))
      bits.

  Definition insert_finish (r : list (cell V.t)) (ix : t) (st : walk_state) : t :=
    if contains r ix then ix else
      mark_terminal (fst st) (snd st) true (Nat.max (index_cell_width ix) (tuple_bits r)).

  Definition remove_finish (r : list (cell V.t)) (ix : t) (st : walk_state) : t :=
    if contains r ix then mark_terminal (fst st) (snd st) false (index_cell_width ix) else ix.

  Definition insert (r : list (cell V.t)) (ix : t) : t :=
    insert_finish r ix (fold_left insert_step_st r (start ix)).

  Definition remove (r : list (cell V.t)) (ix : t) : t :=
    remove_finish r ix (fold_left remove_step_st r (start ix)).
End IndexCode.

Module Index (V : VALUE) <: INDEX V.
  Include IndexCode V.
  Include INDEX_SPEC V.
  Definition mem (ix : t) (r : list (cell V.t)) : Prop := contains r ix = true.
  Definition node (ix : t) (n : positive) (pre : list (cell V.t)) : Prop :=
    seek ix (root ix) pre = Some n.
  Definition stored_edge (ix : t) (n code : positive) (edge : index_edge (cell V.t)) : Prop :=
    PTrieCode.get code (node_edges (read_node ix n)) = Some edge.
  Definition edges_ok (ix : t) : Prop := forall n code edge, stored_edge ix n code edge ->
    encode_cell (edge_cell edge) = code /\ (n < edge_child edge <= next ix)%positive /\
    cell_bits V.encode (edge_cell edge) <= index_cell_width ix /\
    (0 < edge_count edge < Npos (next ix))%N.
  Definition degrees_ok (ix : t) : Prop := forall n,
    N.to_nat (node_degree (read_node ix n)) =
      length (PTrieCode.elements (node_edges (read_node ix n))) /\
    (node_degree (read_node ix n) < Npos (next ix))%N.
  Definition table_ok (ix : t) : Prop := forall n nd,
    PTrieCode.get n (index_nodes ix) = Some nd -> (n <= next ix)%positive.
  Definition paths_unique (ix : t) : Prop := forall pre pre' n,
    node ix n pre -> node ix n pre' -> pre = pre'.
  Definition parents_unique (ix : t) : Prop := forall n code edge n' code' edge',
    stored_edge ix n code edge -> stored_edge ix n' code' edge' ->
    edge_child edge = edge_child edge' -> n = n' /\ code = code'.
  Definition counted_edges (ix : t) : Prop := forall n code edge, stored_edge ix n code edge ->
    exists suffixes, NoDup suffixes /\
      (forall r, In r suffixes <-> contains_from (edge_child edge) r ix = true) /\
      edge_count edge = N.of_nat (length suffixes).
  Definition valid (ix : t) : Prop :=
    edges_ok ix /\ degrees_ok ix /\ table_ok ix /\ paths_unique ix /\
    parents_unique ix /\ counted_edges ix.
  Definition wf (a : nat) (ix : t) : Prop :=
    valid ix /\ (forall r, mem ix r -> length r = a).

  (** The tuple's maximum cell width covers every cell that occurs in it. *)
  Lemma tuple_bits_member : forall r c, In c r -> cell_bits V.encode c <= tuple_bits r.
  Proof.
    induction r as [| head r IH]; intros c Hin; [contradiction |].
    cbn [tuple_bits fold_right]. destruct Hin as [Heq | Hin].
    - subst c. apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
  Qed.

  (** The structural fields remain meaningful while a tuple walk updates its counts. *)
  Definition edge_shape (ix : t) : Prop := forall n code edge,
    stored_edge ix n code edge ->
    encode_cell (edge_cell edge) = code /\ (n < edge_child edge <= next ix)%positive.

  Definition shape (ix : t) : Prop :=
    edge_shape ix /\ table_ok ix /\ parents_unique ix.

  Lemma valid_shape : forall ix, valid ix -> shape ix.
  Proof.
    intros ix [Hedges [_ [Htable [_ [Hparents _]]]]].
    split; [| now split]. intros n code edge Hget.
    specialize (Hedges n code edge Hget). tauto.
  Qed.

  Lemma read_node_write_same : forall ix n nd counter,
    read_node (write_node ix n nd counter) n = nd.
  Proof.
    intros ix n nd counter. unfold read_node, write_node. cbn [index_nodes].
    rewrite PTrie.get_set_same. reflexivity.
  Qed.

  Lemma read_node_write_other : forall ix n q nd counter, q <> n ->
    read_node (write_node ix n nd counter) q = read_node ix q.
  Proof.
    intros ix n q nd counter Hneq. unfold read_node, write_node. cbn [index_nodes].
    now rewrite PTrie.get_set_other.
  Qed.

  Lemma read_node_above_counter : forall ix n, table_ok ix -> (next ix < n)%positive ->
    read_node ix n = empty_node.
  Proof.
    intros ix n Htable Habove. unfold read_node.
    destruct (PTrieCode.get n (index_nodes ix)) as [nd |] eqn:Hget; [| reflexivity].
    specialize (Htable n nd Hget). apply Pos.lt_nle in Habove. contradiction.
  Qed.

  (** The runtime guard is observationally redundant for well-shaped node tables. *)
  Lemma child_raw : forall ix n c, table_ok ix ->
    child ix n c =
      match PTrieCode.get (encode_cell c) (node_edges (read_node ix n)) with
      | Some edge => Some (edge_child edge)
      | None => None
      end.
  Proof.
    intros ix n c Htable. unfold child.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [| reflexivity].
    apply Pos.ltb_lt in Hguard. rewrite (read_node_above_counter ix n Htable Hguard).
    cbn [empty_node node_edges]. rewrite PTrie.get_empty. reflexivity.
  Qed.

  Lemma table_ok_write : forall ix n nd counter, table_ok ix ->
    (n <= counter)%positive -> (next ix <= counter)%positive ->
    table_ok (write_node ix n nd counter).
  Proof.
    intros ix n nd counter Htable Hnode Hcounter q out Hget.
    cbn [write_node index_nodes] in Hget. change (q <= counter)%positive.
    destruct (Pos.eq_dec q n) as [-> | Hneq]; [exact Hnode |].
    rewrite PTrie.get_set_other in Hget by exact Hneq.
    eapply Pos.le_trans; [eapply Htable; exact Hget | exact Hcounter].
  Qed.

  Lemma insert_step_counter_mono : forall st c,
    (next (fst st) <= next (fst (insert_step_st st c)))%positive.
  Proof.
    intros [ix n] c. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); cbn [fst]; [apply Pos.le_refl |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
      cbn [fst write_node next index_counter]; [apply Pos.le_refl |].
    apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  Lemma table_ok_insert_step : forall st c, table_ok (fst st) ->
    table_ok (fst (insert_step_st st c)).
  Proof.
    intros [ix n] c Htable. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [exact Htable |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
      cbn [fst]; apply table_ok_write; try assumption; try apply Pos.le_refl.
    - eapply Pos.le_trans; [exact Hguard | apply Pos.lt_le_incl, Pos.lt_succ_diag_r].
    - apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  (** Writing one edge exposes exactly that binding and retains every other binding. *)
  Lemma stored_edge_put : forall ix n code edge degree terminal counter q key out,
    stored_edge
      (write_node ix n
        (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree terminal)
        counter) q key out <->
      (q = n /\ key = code /\ out = edge) \/
      ((q <> n \/ key <> code) /\ stored_edge ix q key out).
  Proof.
    intros ix n code edge degree terminal counter q key out.
    unfold stored_edge. destruct (Pos.eq_dec q n) as [-> | Hnode].
    - rewrite read_node_write_same. cbn [node_edges].
      destruct (Pos.eq_dec key code) as [-> | Hkey].
      + rewrite PTrie.get_set_same. intuition congruence.
      + rewrite PTrie.get_set_other by exact Hkey. intuition congruence.
    - rewrite read_node_write_other by exact Hnode. intuition congruence.
  Qed.

  Lemma edge_shape_put : forall ix n code edge degree terminal counter,
    edge_shape ix -> encode_cell (edge_cell edge) = code ->
    (n < edge_child edge <= counter)%positive -> (next ix <= counter)%positive ->
    edge_shape
      (write_node ix n
        (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree terminal)
        counter).
  Proof.
    intros ix n code edge degree terminal counter Hshape Hcode Hbounds Hcounter q key out Hget.
    apply stored_edge_put in Hget as [[-> [-> ->]] | [_ Hget]].
    - split; [exact Hcode | exact Hbounds].
    - destruct (Hshape q key out Hget) as [Hencode [Hbelow Habove]].
      split; [exact Hencode |]. split; [exact Hbelow |].
      change (edge_child out <= counter)%positive. eapply Pos.le_trans; eassumption.
  Qed.

  Lemma parents_unique_put : forall ix n code edge degree terminal counter,
    parents_unique ix ->
    (forall q key out, stored_edge ix q key out -> edge_child out = edge_child edge ->
      q = n /\ key = code) ->
    parents_unique
      (write_node ix n
        (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree terminal)
        counter).
  Proof.
    intros ix n code edge degree terminal counter Hparents Hcollision p key out q key' out'
      Hget Hget' Hchild.
    apply stored_edge_put in Hget as [[-> [-> ->]] | [_ Hget]];
      apply stored_edge_put in Hget' as [[-> [-> ->]] | [_ Hget']].
    - auto.
    - destruct (Hcollision q key' out' Hget' (eq_sym Hchild)) as [-> ->]. auto.
    - now apply Hcollision in Hget.
    - eapply Hparents; eassumption.
  Qed.

  Lemma edge_shape_insert_step : forall st c, edge_shape (fst st) ->
    edge_shape (fst (insert_step_st st c)).
  Proof.
    intros [ix n] c Hshape. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [exact Hshape |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; cbn [fst].
    - apply edge_shape_put; try exact Hshape; try reflexivity; try apply Pos.le_refl.
      exact (proj2 (Hshape n (encode_cell c) edge Hget)).
    - apply edge_shape_put; try exact Hshape; try reflexivity.
      + cbn [edge_child]. split; [| apply Pos.le_refl].
        eapply Pos.le_lt_trans; [exact Hguard | apply Pos.lt_succ_diag_r].
      + apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  Lemma parents_unique_insert_step : forall st c,
    edge_shape (fst st) -> parents_unique (fst st) ->
    parents_unique (fst (insert_step_st st c)).
  Proof.
    intros [ix n] c Hshape Hparents. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hparents |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; cbn [fst]; apply parents_unique_put; [exact Hparents |..].
    - intros q key out Hout Hchild. cbn [edge_child] in Hchild.
      eapply Hparents; [exact Hout | exact Hget | exact Hchild].
    - exact Hparents.
    - intros q key out Hout Hchild. cbn [edge_child] in Hchild.
      pose proof (proj2 (proj2 (Hshape q key out Hout))) as Hbound.
      rewrite Hchild in Hbound. exfalso.
      pose proof (Pos.lt_succ_diag_r (next ix)) as Hlt. apply Pos.lt_nle in Hlt. contradiction.
  Qed.

  Lemma shape_insert_step : forall st c, shape (fst st) ->
    shape (fst (insert_step_st st c)).
  Proof.
    intros st c [Hedges [Htable Hparents]]. split.
    - now apply edge_shape_insert_step.
    - split; [now apply table_ok_insert_step |].
      now apply parents_unique_insert_step.
  Qed.

  Lemma stored_edge_drop : forall ix n code degree terminal counter q key out,
    stored_edge
      (write_node ix n
        (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree terminal)
        counter) q key out <->
      (q <> n \/ key <> code) /\ stored_edge ix q key out.
  Proof.
    intros ix n code degree terminal counter q key out.
    unfold stored_edge. destruct (Pos.eq_dec q n) as [-> | Hnode].
    - rewrite read_node_write_same. cbn [node_edges].
      destruct (Pos.eq_dec key code) as [-> | Hkey].
      + rewrite PTrie.get_remove_same. intuition discriminate.
      + rewrite PTrie.get_remove_other by exact Hkey. intuition congruence.
    - rewrite read_node_write_other by exact Hnode. intuition congruence.
  Qed.

  Lemma shape_drop : forall ix n code degree terminal counter,
    shape ix -> (n <= counter)%positive -> (next ix <= counter)%positive ->
    shape
      (write_node ix n
        (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree terminal)
        counter).
  Proof.
    intros ix n code degree terminal counter [Hedges [Htable Hparents]] Hnode Hcounter.
    split.
    - intros q key out Hget. apply stored_edge_drop in Hget as [_ Hget].
      destruct (Hedges q key out Hget) as [Hcode [Hbelow Habove]].
      split; [exact Hcode |]. split; [exact Hbelow |].
      change (edge_child out <= counter)%positive. eapply Pos.le_trans; eassumption.
    - split.
      + now apply table_ok_write.
      + intros q key out q' key' out' Hget Hget' Hchild.
        apply stored_edge_drop in Hget as [_ Hget].
        apply stored_edge_drop in Hget' as [_ Hget'].
        eapply Hparents; eassumption.
  Qed.

  Lemma table_ok_remove_step : forall st c, table_ok (fst st) ->
    table_ok (fst (remove_step_st st c)).
  Proof.
    intros [ix n] c Htable. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [exact Htable |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |]; [| exact Htable].
    destruct (N.eqb (edge_count edge) 1%N); cbn [fst];
      apply table_ok_write; try assumption; apply Pos.le_refl.
  Qed.

  Lemma shape_remove_step : forall st c, shape (fst st) ->
    shape (fst (remove_step_st st c)).
  Proof.
    intros [ix n] c [Hshape [Htable Hparents]]. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [exact (conj Hshape (conj Htable Hparents)) |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| exact (conj Hshape (conj Htable Hparents))].
    destruct (N.eqb (edge_count edge) 1%N); cbn [fst].
    - apply shape_drop;
        [exact (conj Hshape (conj Htable Hparents)) | exact Hguard | apply Pos.le_refl].
    - split.
      + apply edge_shape_put; try exact Hshape; try apply Pos.le_refl.
        * exact (proj1 (Hshape n (encode_cell c) edge Hget)).
        * exact (proj2 (Hshape n (encode_cell c) edge Hget)).
      + split.
        * apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl].
        * apply parents_unique_put; [exact Hparents |].
          intros q key out Hout Hchild. cbn [edge_child] in Hchild.
          eapply Hparents; [exact Hout | exact Hget | exact Hchild].
  Qed.

  Lemma edges_ok_remove_step : forall st c, edges_ok (fst st) ->
    edges_ok (fst (remove_step_st st c)).
  Proof.
    intros [ix n] c Hedges. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hedges |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| exact Hedges].
    destruct (N.eqb (edge_count edge) 1%N) eqn:Hone; cbn [fst].
    - intros q key out Hout. apply stored_edge_drop in Hout as [_ Hout].
      exact (Hedges q key out Hout).
    - intros q key out Hout. apply stored_edge_put in Hout as [[-> [-> ->]] | [_ Hout]].
      + destruct (Hedges n (encode_cell c) edge Hget) as [Hcode [Hbounds [Hbits Hcount]]].
        split; [exact Hcode |]. split; [exact Hbounds |]. split; [exact Hbits |].
        change (0 < N.pred (edge_count edge) < Npos (next ix))%N.
        change (0 < edge_count edge < Npos (next ix))%N in Hcount.
        apply N.eqb_neq in Hone. lia.
      + exact (Hedges q key out Hout).
  Qed.

  Lemma shape_remove_walk : forall r st, shape (fst st) ->
    shape (fst (fold_left remove_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hshape; cbn [fold_left]; [exact Hshape |].
    apply IH. now apply shape_remove_step.
  Qed.

  Lemma edges_ok_remove_walk : forall r st, edges_ok (fst st) ->
    edges_ok (fst (fold_left remove_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hedges; cbn [fold_left]; [exact Hedges |].
    apply IH. now apply edges_ok_remove_step.
  Qed.

  Lemma bounded_succ_small : forall limit count, (count <= Npos limit)%N ->
    bounded_succ limit count = N.succ count.
  Proof.
    intros limit count Hbound. unfold bounded_succ.
    assert (Hguard : N.ltb (Npos limit) count = false) by now apply N.ltb_ge.
    now rewrite Hguard.
  Qed.

  Lemma degrees_ok_write : forall ix n nd counter, degrees_ok ix ->
    N.to_nat (node_degree nd) = length (PTrieCode.elements (node_edges nd)) ->
    (node_degree nd < Npos counter)%N -> (next ix <= counter)%positive ->
    degrees_ok (write_node ix n nd counter).
  Proof.
    intros ix n nd counter Hdegrees Hlength Hdegree Hcounter q.
    destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_write_same. split; [exact Hlength | exact Hdegree].
    - rewrite read_node_write_other by exact Hneq.
      destruct (Hdegrees q) as [Hlen Hbound]. split; [exact Hlen |].
      change (node_degree (read_node ix q) < Npos counter)%N.
      eapply N.lt_le_trans; [exact Hbound | exact Hcounter].
  Qed.

  Lemma degrees_ok_insert_step : forall st c, degrees_ok (fst st) ->
    degrees_ok (fst (insert_step_st st c)).
  Proof.
    intros [ix n] c Hdegrees. cbn [fst] in Hdegrees. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hdegrees |].
    destruct (Hdegrees n) as [Hlength Hbound].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; cbn [fst].
    - apply degrees_ok_write; try exact Hdegrees; try exact Hbound; try apply Pos.le_refl.
      cbn [node_degree node_edges].
      rewrite (TrieCardinalityFacts.set_present _ _ edge) by exact Hget. exact Hlength.
    - rewrite bounded_succ_small by (apply N.lt_le_incl; exact Hbound).
      apply degrees_ok_write; [exact Hdegrees | | |].
      + cbn [node_degree node_edges]. rewrite N2Nat.inj_succ.
        rewrite TrieCardinalityFacts.set_absent by exact Hget. f_equal. exact Hlength.
      + change (N.succ (node_degree (read_node ix n)) < N.succ (Npos (next ix)))%N.
        change (node_degree (read_node ix n) < Npos (next ix))%N in Hbound. lia.
      + apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  Lemma degrees_ok_remove_step : forall st c, degrees_ok (fst st) ->
    degrees_ok (fst (remove_step_st st c)).
  Proof.
    intros [ix n] c Hdegrees. cbn [fst] in Hdegrees. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hdegrees |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| exact Hdegrees].
    destruct (Hdegrees n) as [Hlength Hbound].
    destruct (N.eqb (edge_count edge) 1%N); cbn [fst].
    - apply degrees_ok_write; [exact Hdegrees | | | apply Pos.le_refl].
      + cbn [node_degree node_edges]. rewrite N2Nat.inj_pred, Hlength.
        rewrite <- (TrieCardinalityFacts.remove_present _ _ edge _ Hget). reflexivity.
      + change (N.pred (node_degree (read_node ix n)) < Npos (next ix))%N.
        change (node_degree (read_node ix n) < Npos (next ix))%N in Hbound. lia.
    - apply degrees_ok_write; try exact Hdegrees; try exact Hbound; try apply Pos.le_refl.
      cbn [node_degree node_edges].
      rewrite (TrieCardinalityFacts.set_present _ _ edge) by exact Hget. exact Hlength.
  Qed.

  Lemma degrees_ok_insert_walk : forall r st, degrees_ok (fst st) ->
    degrees_ok (fst (fold_left insert_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hdegrees; cbn [fold_left]; [exact Hdegrees |].
    apply IH. now apply degrees_ok_insert_step.
  Qed.

  Lemma degrees_ok_remove_walk : forall r st, degrees_ok (fst st) ->
    degrees_ok (fst (fold_left remove_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hdegrees; cbn [fold_left]; [exact Hdegrees |].
    apply IH. now apply degrees_ok_remove_step.
  Qed.
  (** The initial node counter starts at one. *)
  Lemma next_empty : next empty = 1%positive.
  Proof.
    reflexivity.
  Qed.

  (** A walk step allocates at most one fresh node. *)
  Lemma insert_step_counter : forall st c,
    Pos.to_nat (next (fst (insert_step_st st c))) <= Pos.to_nat (next (fst st)) + 1.
  Proof.
    intros [ix n] c. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); cbn [fst]; [lia |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
      cbn [fst write_node next index_counter]; [lia |].
    rewrite Pos2Nat.inj_succ. lia.
  Qed.

  Lemma insert_walk_counter : forall r st,
    Pos.to_nat (next (fst (fold_left insert_step_st r st))) <=
      Pos.to_nat (next (fst st)) + length r.
  Proof.
    induction r as [| c r IH]; intro st; cbn [fold_left length]; [lia |].
    pose proof (IH (insert_step_st st c)).
    pose proof (insert_step_counter st c). lia.
  Qed.

  (** Every removal step retains the allocation counter, including absent edges. *)
  Lemma remove_step_counter : forall st c,
    next (fst (remove_step_st st c)) = next (fst st).
  Proof.
    intros [ix n] c. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [reflexivity |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |]; [| reflexivity].
    destruct (N.eqb (edge_count edge) 1%N); reflexivity.
  Qed.

  Lemma remove_walk_counter : forall r st,
    next (fst (fold_left remove_step_st r st)) = next (fst st).
  Proof.
    induction r as [| c r IH]; intro st; cbn [fold_left]; [reflexivity |].
    rewrite IH. apply remove_step_counter.
  Qed.

  (** Insertion allocates at most one node per tuple cell. *)
  Lemma next_insert : forall a r ix, wf a ix ->
    (next (insert r ix) <= next ix + Pos.of_nat (length r))%positive.
  Proof.
    intros a r ix _. apply Pos2Nat.inj_le.
    rewrite Pos2Nat.inj_add, Nat2Pos.id_max.
    pose proof (insert_walk_counter r (start ix)) as Hcounter.
    cbn [start fst] in Hcounter.
    unfold insert, insert_finish. destruct (contains r ix).
    - lia.
    - cbn [mark_terminal next index_counter]. lia.
  Qed.

  (** Removal keeps the fresh node counter. *)
  Lemma next_remove : forall a r ix, wf a ix -> next (remove r ix) = next ix.
  Proof.
    intros a r ix _. unfold remove, remove_finish.
    destruct (contains r ix); [| reflexivity].
    change (next (fst (fold_left remove_step_st r (start ix))) = next ix).
    rewrite remove_walk_counter. reflexivity.
  Qed.

  Lemma read_node_empty : forall n, read_node empty n = empty_node.
  Proof.
    intro n. unfold read_node. cbn [empty index_nodes].
    rewrite PTrie.get_empty. reflexivity.
  Qed.

  Lemma child_empty : forall n c, child empty n c = None.
  Proof.
    intros n c. unfold child. destruct (Pos.ltb (next empty) n); [reflexivity |].
    rewrite read_node_empty. cbn [empty_node node_edges].
    rewrite PTrie.get_empty. reflexivity.
  Qed.

  Lemma empty_no_edge : forall n code edge, ~ stored_edge empty n code edge.
  Proof.
    intros n code edge Hget. unfold stored_edge in Hget.
    rewrite read_node_empty in Hget. cbn [empty_node node_edges] in Hget.
    rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  Lemma mem_empty : forall u, ~ mem empty u.
  Proof.
    intros [| c u]; unfold mem, contains, contains_from; cbn [seek].
    - rewrite read_node_empty. discriminate.
    - rewrite child_empty. discriminate.
  Qed.

  Lemma wf_empty : forall a, wf a empty.
  Proof.
    intro a. split; [| intros u Hu; exact (False_rect _ (mem_empty u Hu))].
    unfold valid. split.
    - intros n code edge Hget. exfalso. exact (empty_no_edge n code edge Hget).
    - split.
      + intro n. rewrite read_node_empty. split; reflexivity.
      + split.
        * intros n nd Hget. cbn [empty index_nodes] in Hget.
          rewrite PTrie.get_empty in Hget. discriminate.
        * split.
          -- intros pre pre' n Hpre Hpre'.
             destruct pre as [| c pre], pre' as [| c' pre']; [reflexivity |..];
               unfold node in *; cbn [seek] in *; rewrite ?child_empty in *; discriminate.
          -- split.
             ++ intros n code edge n' code' edge' Hget.
                exfalso. exact (empty_no_edge n code edge Hget).
             ++ intros n code edge Hget.
                exfalso. exact (empty_no_edge n code edge Hget).
  Qed.

  Lemma wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  Proof.
    intros a ix u [_ Harity]. apply Harity.
  Qed.

  Lemma node_root : forall a ix, wf a ix -> node ix (root ix) [].
  Proof.
    intros a ix _. reflexivity.
  Qed.

  (** Seeking a concatenated tuple first reaches its prefix node. *)
  Lemma seek_append : forall ix pre n suf,
    seek ix n (pre ++ suf) =
      match seek ix n pre with Some m => seek ix m suf | None => None end.
  Proof.
    intros ix pre. induction pre as [| c pre IH]; intros n suf; cbn [app seek].
    - reflexivity.
    - destruct (child ix n c); [apply IH | reflexivity].
  Qed.

  Lemma node_member_suffix : forall ix n pre suf, node ix n pre ->
    (mem ix (pre ++ suf) <-> contains_from n suf ix = true).
  Proof.
    intros ix n pre suf Hnode. unfold node in Hnode.
    unfold mem, contains, contains_from. rewrite seek_append, Hnode. reflexivity.
  Qed.

  Lemma child_node : forall ix n pre c m, node ix n pre ->
    (child ix n c = Some m <-> node ix m (pre ++ [c])).
  Proof.
    intros ix n pre c m Hnode. unfold node in *.
    rewrite seek_append, Hnode. cbn [seek].
    destruct (child ix n c); split; congruence.
  Qed.

  Lemma encode_cell_inj : forall c d, encode_cell c = encode_cell d -> c = d.
  Proof.
    intros [i | v] [j | w] Heq; cbn [encode_cell] in Heq; try discriminate.
    - injection Heq as Heq. now subst j.
    - injection Heq as Heq. apply V.encode_inj in Heq. now subst w.
  Qed.

  Lemma child_forward : forall ix n c m, edge_shape ix -> child ix n c = Some m ->
    (n < m <= next ix)%positive.
  Proof.
    intros ix n c m Hshape Hchild. unfold child in Hchild.
    destruct (Pos.ltb (next ix) n); [discriminate |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| discriminate].
    injection Hchild as <-. exact (proj2 (Hshape n (encode_cell c) edge Hget)).
  Qed.

  Lemma seek_forward : forall ix r n m, edge_shape ix -> seek ix n r = Some m ->
    (n <= m)%positive.
  Proof.
    intros ix r. induction r as [| c r IH]; intros n m Hshape Hseek.
    - cbn [seek] in Hseek. injection Hseek as <-. apply Pos.le_refl.
    - cbn [seek] in Hseek.
      destruct (child ix n c) as [child_node |] eqn:Hchild; [| discriminate].
      eapply Pos.le_trans; [| eapply IH; eassumption].
      apply Pos.lt_le_incl. exact (proj1 (child_forward ix n c child_node Hshape Hchild)).
  Qed.

  Lemma seek_strict : forall ix r n m, edge_shape ix -> r <> [] ->
    seek ix n r = Some m -> (n < m)%positive.
  Proof.
    intros ix [| c r] n m Hshape Hnonempty Hseek; [contradiction |].
    cbn [seek] in Hseek.
    destruct (child ix n c) as [child_node |] eqn:Hchild; [| discriminate].
    eapply Pos.lt_le_trans; [exact (proj1 (child_forward ix n c child_node Hshape Hchild)) |].
    eapply seek_forward; eassumption.
  Qed.

  Lemma child_parents_unique : forall ix n c n' c' m,
    parents_unique ix -> child ix n c = Some m -> child ix n' c' = Some m ->
    n = n' /\ c = c'.
  Proof.
    intros ix n c n' c' m Hparents Hchild Hchild'.
    unfold child in Hchild, Hchild'.
    destruct (Pos.ltb (next ix) n), (Pos.ltb (next ix) n'); try discriminate.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| discriminate].
    destruct (PTrieCode.get (encode_cell c') (node_edges (read_node ix n')))
      as [edge' |] eqn:Hget'; [| discriminate].
    destruct (Hparents n (encode_cell c) edge n' (encode_cell c') edge'
      Hget Hget' ltac:(congruence)) as [Hnode Hcode].
    split; [exact Hnode | now apply encode_cell_inj].
  Qed.

  (** Increasing identifiers and globally unique parents make root paths unique. *)
  Lemma shape_paths_unique : forall ix, shape ix -> paths_unique ix.
  Proof.
    intros ix [Hshape [_ Hparents]] pre.
    induction pre as [| c pre IH] using rev_ind; intros pre' n Hnode Hnode'.
    - change (Some (root ix) = Some n) in Hnode. injection Hnode as <-.
      destruct pre' as [| c' pre']; [reflexivity |].
      pose proof (seek_strict ix (c' :: pre') (root ix) (root ix)
        Hshape ltac:(discriminate) Hnode') as Hlt.
      exfalso. exact (Pos.lt_irrefl _ Hlt).
    - destruct (rev pre') as [| c' rest] eqn:Hrev.
      + apply (f_equal (@rev (cell V.t))) in Hrev.
        rewrite rev_involutive in Hrev. cbn [rev] in Hrev. subst pre'.
        change (Some (root ix) = Some n) in Hnode'. injection Hnode' as <-.
        pose proof (seek_strict ix (pre ++ [c]) (root ix) (root ix)
          Hshape ltac:(destruct pre; discriminate) Hnode) as Hlt.
        exfalso. exact (Pos.lt_irrefl _ Hlt).
      + assert (Hpre' : pre' = rev rest ++ [c']).
        { rewrite <- (rev_involutive pre'), Hrev. reflexivity. }
        subst pre'. unfold node in Hnode, Hnode'.
        rewrite seek_append in Hnode, Hnode'.
        destruct (seek ix (root ix) pre) as [p |] eqn:Hpre; [| discriminate].
        destruct (seek ix (root ix) (rev rest)) as [q |] eqn:Hrest; [| discriminate].
        cbn [seek] in Hnode, Hnode'.
        destruct (child ix p c) as [m |] eqn:Hchild; [| discriminate].
        destruct (child ix q c') as [m' |] eqn:Hchild'; [| discriminate].
        injection Hnode as ->. injection Hnode' as ->.
        destruct (child_parents_unique ix p c q c' n Hparents Hchild Hchild') as [<- <-].
        f_equal. exact (IH (rev rest) p Hpre Hrest).
  Qed.

  (** Paths with a common starting node are unique even when that node is detached. *)
  Lemma seek_paths_unique : forall ix q pre pre' n, shape ix ->
    seek ix q pre = Some n -> seek ix q pre' = Some n -> pre = pre'.
  Proof.
    intros ix q pre pre' n [Hshape [_ Hparents]]. revert pre' n.
    induction pre as [| c pre IH] using rev_ind; intros pre' n Hseek Hseek'.
    - change (Some q = Some n) in Hseek. injection Hseek as <-.
      destruct pre' as [| c' pre']; [reflexivity |].
      pose proof (seek_strict ix (c' :: pre') q q
        Hshape ltac:(discriminate) Hseek') as Hlt.
      exfalso. exact (Pos.lt_irrefl _ Hlt).
    - destruct (rev pre') as [| c' rest] eqn:Hrev.
      + apply (f_equal (@rev (cell V.t))) in Hrev.
        rewrite rev_involutive in Hrev. cbn [rev] in Hrev. subst pre'.
        change (Some q = Some n) in Hseek'. injection Hseek' as <-.
        pose proof (seek_strict ix (pre ++ [c]) q q
          Hshape ltac:(destruct pre; discriminate) Hseek) as Hlt.
        exfalso. exact (Pos.lt_irrefl _ Hlt).
      + assert (Hpre' : pre' = rev rest ++ [c']).
        { rewrite <- (rev_involutive pre'), Hrev. reflexivity. }
        subst pre'. rewrite seek_append in Hseek, Hseek'.
        destruct (seek ix q pre) as [p |] eqn:Hpre; [| discriminate].
        destruct (seek ix q (rev rest)) as [p' |] eqn:Hrest; [| discriminate].
        cbn [seek] in Hseek, Hseek'.
        destruct (child ix p c) as [m |] eqn:Hchild; [| discriminate].
        destruct (child ix p' c') as [m' |] eqn:Hchild'; [| discriminate].
        injection Hseek as ->. injection Hseek' as ->.
        destruct (child_parents_unique ix p c p' c' n Hparents Hchild Hchild') as [<- <-].
        f_equal. exact (IH (rev rest) p eq_refl Hrest).
  Qed.

  Lemma read_node_mark_same : forall ix n present bits,
    read_node (mark_terminal ix n present bits) n =
      IndexNode (node_edges (read_node ix n)) (node_degree (read_node ix n)) present.
  Proof.
    intros ix n present bits. unfold read_node, mark_terminal. cbn [index_nodes].
    rewrite PTrie.get_set_same. reflexivity.
  Qed.

  Lemma read_node_mark_other : forall ix n present bits q, q <> n ->
    read_node (mark_terminal ix n present bits) q = read_node ix q.
  Proof.
    intros ix n present bits q Hneq. unfold read_node, mark_terminal. cbn [index_nodes].
    now rewrite PTrie.get_set_other.
  Qed.

  Lemma mark_node_edges : forall ix n present bits q,
    node_edges (read_node (mark_terminal ix n present bits) q) =
      node_edges (read_node ix q).
  Proof.
    intros ix n present bits q. destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_mark_same. reflexivity.
    - now rewrite read_node_mark_other.
  Qed.

  Lemma child_mark_terminal : forall ix n present bits q c,
    child (mark_terminal ix n present bits) q c = child ix q c.
  Proof.
    intros ix n present bits q c. unfold child.
    replace (next (mark_terminal ix n present bits)) with (next ix) by reflexivity.
    rewrite mark_node_edges. reflexivity.
  Qed.

  Lemma seek_mark_terminal : forall ix r n present bits q,
    seek (mark_terminal ix n present bits) q r = seek ix q r.
  Proof.
    intros ix r. induction r as [| c r IH]; intros n present bits q; cbn [seek].
    - reflexivity.
    - rewrite child_mark_terminal. destruct (child ix q c); [apply IH | reflexivity].
  Qed.

  Lemma mark_terminal_add : forall ix n bits q r,
    contains_from q r (mark_terminal ix n true bits) = true <->
      seek ix q r = Some n \/ contains_from q r ix = true.
  Proof.
    intros ix n bits q r. unfold contains_from. rewrite seek_mark_terminal.
    destruct (seek ix q r) as [m |]; [| intuition discriminate].
    destruct (Pos.eq_dec m n) as [-> | Hneq].
    - rewrite read_node_mark_same. cbn [node_terminal]. intuition congruence.
    - rewrite read_node_mark_other by exact Hneq. intuition congruence.
  Qed.

  Lemma mark_terminal_delete : forall ix n bits q r,
    contains_from q r (mark_terminal ix n false bits) = true <->
      seek ix q r <> Some n /\ contains_from q r ix = true.
  Proof.
    intros ix n bits q r. unfold contains_from. rewrite seek_mark_terminal.
    destruct (seek ix q r) as [m |]; [| intuition discriminate].
    destruct (Pos.eq_dec m n) as [-> | Hneq].
    - rewrite read_node_mark_same. cbn [node_terminal]. intuition congruence.
    - rewrite read_node_mark_other by exact Hneq. intuition congruence.
  Qed.

  Lemma terminal_put_edge : forall ix n code edge degree counter q,
    node_terminal (read_node
      (write_node ix n
        (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree
          (node_terminal (read_node ix n))) counter) q) =
      node_terminal (read_node ix q).
  Proof.
    intros ix n code edge degree counter q. destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_write_same. reflexivity.
    - now rewrite read_node_write_other.
  Qed.

  Lemma child_put_edge_other : forall ix n code edge degree counter q c,
    table_ok ix ->
    table_ok (write_node ix n
      (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    (q <> n \/ encode_cell c <> code) ->
    child (write_node ix n
      (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) q c = child ix q c.
  Proof.
    intros ix n code edge degree counter q c Htable Htable' Hother.
    rewrite !child_raw by assumption.
    destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_write_same. cbn [node_edges].
      rewrite PTrie.get_set_other by tauto. reflexivity.
    - rewrite read_node_write_other by exact Hneq. reflexivity.
  Qed.

  Lemma child_put_edge_same : forall ix n c edge degree counter,
    table_ok (write_node ix n
      (IndexNode (PTrieCode.set (encode_cell c) edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    child (write_node ix n
      (IndexNode (PTrieCode.set (encode_cell c) edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) n c = Some (edge_child edge).
  Proof.
    intros ix n c edge degree counter Htable.
    rewrite child_raw by exact Htable. rewrite read_node_write_same. cbn [node_edges].
    rewrite PTrie.get_set_same. reflexivity.
  Qed.

  Lemma child_put_edge_existing : forall ix n code old edge degree counter,
    table_ok ix ->
    table_ok (write_node ix n
      (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    PTrieCode.get code (node_edges (read_node ix n)) = Some old ->
    edge_child edge = edge_child old -> forall q c,
    child (write_node ix n
      (IndexNode (PTrieCode.set code edge (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) q c = child ix q c.
  Proof.
    intros ix n code old edge degree counter Htable Htable' Hget Hchild q c.
    destruct (Pos.eq_dec q n) as [-> | Hnode].
    - destruct (Pos.eq_dec (encode_cell c) code) as [Hcode | Hcode].
      + rewrite !child_raw by assumption. rewrite read_node_write_same. cbn [node_edges].
        rewrite Hcode, PTrie.get_set_same, Hget, Hchild. reflexivity.
      + apply child_put_edge_other; auto.
    - apply child_put_edge_other; auto.
  Qed.

  Lemma seek_extensional : forall ix ix',
    (forall n c, child ix' n c = child ix n c) ->
    forall r n, seek ix' n r = seek ix n r.
  Proof.
    intros ix ix' Hchild r. induction r as [| c r IH]; intro n; cbn [seek].
    - reflexivity.
    - rewrite Hchild. destruct (child ix n c); [apply IH | reflexivity].
  Qed.

  Lemma contains_from_extensional : forall ix ix',
    (forall n c, child ix' n c = child ix n c) ->
    (forall n, node_terminal (read_node ix' n) = node_terminal (read_node ix n)) ->
    forall r n, contains_from n r ix' = contains_from n r ix.
  Proof.
    intros ix ix' Hchild Hterminal r n. unfold contains_from.
    rewrite (seek_extensional ix ix' Hchild).
    destruct (seek ix n r); [apply Hterminal | reflexivity].
  Qed.

  Lemma contains_from_empty_node : forall ix n r, read_node ix n = empty_node ->
    contains_from n r ix = false.
  Proof.
    intros ix n [| c r] Hempty; unfold contains_from; cbn [seek].
    - rewrite Hempty. reflexivity.
    - unfold child. destruct (Pos.ltb (next ix) n); [reflexivity |].
      rewrite Hempty. cbn [empty_node node_edges]. rewrite PTrie.get_empty. reflexivity.
  Qed.

  Lemma contains_from_cons : forall ix n c r,
    contains_from n (c :: r) ix =
      match child ix n c with Some m => contains_from m r ix | None => false end.
  Proof.
    intros ix n c r. unfold contains_from. cbn [seek].
    destruct (child ix n c); reflexivity.
  Qed.

  (** Connecting a fresh empty child introduces no tuple before its terminal is marked. *)
  Lemma fresh_edge_membership : forall ix n c degree, edge_shape ix -> table_ok ix ->
    (n <= next ix)%positive ->
    PTrieCode.get (encode_cell c) (node_edges (read_node ix n)) = None ->
    forall r q, (q <= next ix)%positive ->
    contains_from q r
      (write_node ix n
        (IndexNode (PTrieCode.set (encode_cell c) (IndexEdge c (Pos.succ (next ix)) 1%N)
          (node_edges (read_node ix n))) degree (node_terminal (read_node ix n)))
        (Pos.succ (next ix))) = contains_from q r ix.
  Proof.
    intros ix n c degree Hshape Htable Hnode Hget.
    set (out := write_node ix n
      (IndexNode (PTrieCode.set (encode_cell c) (IndexEdge c (Pos.succ (next ix)) 1%N)
        (node_edges (read_node ix n))) degree (node_terminal (read_node ix n)))
      (Pos.succ (next ix))).
    assert (Htable' : table_ok out).
    { unfold out. apply table_ok_write; [exact Htable | |].
      - eapply Pos.le_trans; [exact Hnode | apply Pos.lt_le_incl, Pos.lt_succ_diag_r].
      - apply Pos.lt_le_incl, Pos.lt_succ_diag_r. }
    assert (Hfresh : read_node out (Pos.succ (next ix)) = empty_node).
    { unfold out. rewrite read_node_write_other.
      - apply read_node_above_counter; [exact Htable | apply Pos.lt_succ_diag_r].
      - intro Heq. rewrite <- Heq in Hnode.
        pose proof (Pos.lt_succ_diag_r (next ix)) as Hlt.
        apply Pos.lt_nle in Hlt. contradiction. }
    assert (Hnew : child out n c = Some (Pos.succ (next ix))).
    { unfold out. apply child_put_edge_same. exact Htable'. }
    assert (Hold : child ix n c = None).
    { rewrite child_raw by exact Htable. now rewrite Hget. }
    assert (Hother : forall q d, q <> n \/ encode_cell d <> encode_cell c ->
      child out q d = child ix q d).
    { intros q d Hdiff. unfold out. apply child_put_edge_other; assumption. }
    induction r as [| d r IH]; intros q Hbound.
    - change (node_terminal (read_node out q) = node_terminal (read_node ix q)).
      unfold out. apply terminal_put_edge.
    - rewrite !contains_from_cons.
      destruct (Pos.eq_dec q n) as [Hnode' | Hnode'];
        destruct (Pos.eq_dec (encode_cell d) (encode_cell c)) as [Hcode | Hcode].
      + subst q. apply encode_cell_inj in Hcode. subst d. rewrite Hnew, Hold.
        now apply contains_from_empty_node.
      + rewrite Hother by tauto.
        destruct (child ix q d) as [m |] eqn:Hchild; [| reflexivity].
        apply IH. exact (proj2 (child_forward ix q d m Hshape Hchild)).
      + rewrite Hother by tauto.
        destruct (child ix q d) as [m |] eqn:Hchild; [| reflexivity].
        apply IH. exact (proj2 (child_forward ix q d m Hshape Hchild)).
      + rewrite Hother by tauto.
        destruct (child ix q d) as [m |] eqn:Hchild; [| reflexivity].
        apply IH. exact (proj2 (child_forward ix q d m Hshape Hchild)).
  Qed.

  Lemma insert_step_membership : forall st c r q, shape (fst st) ->
    (q <= next (fst st))%positive ->
    contains_from q r (fst (insert_step_st st c)) = contains_from q r (fst st).
  Proof.
    intros [ix n] c r q [Hshape [Htable Hparents]] Hbound.
    unfold insert_step_st. destruct (Pos.ltb (next ix) n) eqn:Hguard; [reflexivity |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; cbn [fst].
    - apply contains_from_extensional.
      + apply child_put_edge_existing with (old := edge); try assumption; try reflexivity.
        apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl].
      + apply terminal_put_edge.
    - apply fresh_edge_membership; assumption.
  Qed.

  Lemma shape_insert_walk : forall r st, shape (fst st) ->
    shape (fst (fold_left insert_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hshape; cbn [fold_left]; [exact Hshape |].
    apply IH. now apply shape_insert_step.
  Qed.

  Lemma insert_walk_membership : forall walk st r q, shape (fst st) ->
    (q <= next (fst st))%positive ->
    contains_from q r (fst (fold_left insert_step_st walk st)) =
      contains_from q r (fst st).
  Proof.
    induction walk as [| c walk IH]; intros st r q Hshape Hbound;
      cbn [fold_left]; [reflexivity |].
    rewrite IH.
    - now apply insert_step_membership.
    - now apply shape_insert_step.
    - eapply Pos.le_trans; [exact Hbound | apply insert_step_counter_mono].
  Qed.

  Lemma seek_bounded : forall ix r q n, edge_shape ix -> (q <= next ix)%positive ->
    seek ix q r = Some n -> (n <= next ix)%positive.
  Proof.
    intros ix r. induction r as [| c r IH]; intros q n Hshape Hbound Hseek.
    - cbn [seek] in Hseek. injection Hseek as <-. exact Hbound.
    - cbn [seek] in Hseek.
      destruct (child ix q c) as [m |] eqn:Hchild; [| discriminate].
      eapply IH; [exact Hshape | | exact Hseek].
      exact (proj2 (child_forward ix q c m Hshape Hchild)).
  Qed.

  (** Distinct live suffixes from a nonroot node have distinct bounded terminal nodes. *)
  Lemma live_suffixes_bound : forall ix q suffixes, shape ix ->
    (1 < q <= next ix)%positive -> NoDup suffixes ->
    (forall r, In r suffixes -> contains_from q r ix = true) ->
    length suffixes <= Pos.to_nat (next ix) - 1.
  Proof.
    intros ix q suffixes Hshape [Hlower Hupper] Hnodup Hlive.
    assert (Hends : forall r, In r suffixes -> exists n, seek ix q r = Some n).
    { intros r Hr. specialize (Hlive r Hr). unfold contains_from in Hlive.
      destruct (seek ix q r) as [n |] eqn:Hseek; [exists n; reflexivity | discriminate]. }
    set (endpoint := fun r : list (cell V.t) =>
      match seek ix q r with Some n => n | None => q end).
    eapply TrieCardinalityFacts.bounded_positive_length with (key := endpoint).
    - exact Hnodup.
    - intros r r' Hr Hr' Heq.
      destruct (Hends r Hr) as [n Hseek]. destruct (Hends r' Hr') as [n' Hseek'].
      unfold endpoint in Heq. rewrite Hseek, Hseek' in Heq. subst n'.
      eapply seek_paths_unique; eassumption.
    - intros r Hr. destruct (Hends r Hr) as [n Hseek].
      unfold endpoint. rewrite Hseek. split.
      + eapply Pos.lt_le_trans; [exact Hlower |].
        eapply seek_forward; [exact (proj1 Hshape) | exact Hseek].
      + eapply seek_bounded; [exact (proj1 Hshape) | exact Hupper | exact Hseek].
  Qed.

  (** Live edge counts fit strictly below the node allocation counter. *)
  Lemma counted_edges_upper : forall ix n code edge, shape ix -> counted_edges ix ->
    stored_edge ix n code edge -> (edge_count edge < Npos (next ix))%N.
  Proof.
    intros ix n code edge Hshape Hcounts Hedge.
    destruct ((proj1 Hshape) n code edge Hedge) as [_ [Hforward Hupper]].
    destruct (Hcounts n code edge Hedge) as [suffixes [Hnodup [Hmembers Hcount]]].
    assert (Hrange : (1 < edge_child edge <= next ix)%positive) by (split; lia).
    pose proof (live_suffixes_bound ix (edge_child edge) suffixes Hshape Hrange Hnodup
      (fun r Hr => proj1 (Hmembers r) Hr)) as Hlength.
    rewrite Hcount. pose proof (Pos2Nat.is_pos (next ix)). lia.
  Qed.

  (** Distinct edge children also bound any cache that counts its node's bindings. *)
  Lemma degrees_upper : forall ix, shape ix ->
    (forall n, N.to_nat (node_degree (read_node ix n)) =
      length (PTrieCode.elements (node_edges (read_node ix n)))) ->
    forall n, (node_degree (read_node ix n) < Npos (next ix))%N.
  Proof.
    intros ix Hshape Hdegrees n.
    assert (Hlength : length (PTrieCode.elements (node_edges (read_node ix n))) <=
      Pos.to_nat (next ix) - 1).
    { eapply TrieCardinalityFacts.bounded_positive_length with
        (key := fun entry : positive * index_edge (cell V.t) => edge_child (snd entry)).
      - apply NoDup_map_inv with (f := @fst positive (index_edge (cell V.t))).
        apply PTrie.elements_nodup.
      - intros [code edge] [code' edge'] Hin Hin' Heq. cbn [snd] in Heq.
        apply PTrie.elements_spec in Hin, Hin'.
        destruct ((proj2 (proj2 Hshape)) n code edge n code' edge' Hin Hin' Heq)
          as [_ Hcode]. subst code'. assert (Hedge : edge = edge') by congruence.
        now subst edge'.
      - intros [code edge] Hin. cbn [snd]. apply PTrie.elements_spec in Hin.
        destruct ((proj1 Hshape) n code edge Hin) as [_ [Hforward Hupper]].
        split; lia. }
    specialize (Hdegrees n). pose proof (Pos2Nat.is_pos (next ix)). lia.
  Qed.

  (** A path ending at a node never reads that node's outgoing edges. *)
  Lemma seek_preserve_endpoint : forall ix ix' target,
    edge_shape ix -> table_ok ix -> table_ok ix' ->
    (forall q, q <> target ->
      node_edges (read_node ix' q) = node_edges (read_node ix q)) ->
    forall r q, seek ix q r = Some target -> seek ix' q r = Some target.
  Proof.
    intros ix ix' target Hshape Htable Htable' Hedges r.
    induction r as [| c r IH]; intros q Hseek; cbn [seek] in *; [exact Hseek |].
    destruct (child ix q c) as [m |] eqn:Hchild; [| discriminate].
    assert (Hneq : q <> target).
    { intro Heq. subst q.
      pose proof (proj1 (child_forward ix target c m Hshape Hchild)) as Hlt.
      pose proof (seek_forward ix r m target Hshape Hseek) as Hle.
      apply Pos.lt_nle in Hlt. contradiction. }
    assert (Hchild' : child ix' q c = Some m).
    { rewrite child_raw by exact Htable'. rewrite Hedges by exact Hneq.
      rewrite <- child_raw by exact Htable. exact Hchild. }
    rewrite Hchild'. now apply IH.
  Qed.

  Lemma insert_step_other_edges : forall st c q, q <> snd st ->
    node_edges (read_node (fst (insert_step_st st c)) q) =
      node_edges (read_node (fst st) q).
  Proof.
    intros [ix n] c q Hneq. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); [reflexivity |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
      cbn [fst]; rewrite read_node_write_other by exact Hneq; reflexivity.
  Qed.

  Lemma insert_step_child : forall ix n c, table_ok ix -> (n <= next ix)%positive ->
    child (fst (insert_step_st (ix, n) c)) n c = Some (snd (insert_step_st (ix, n) c)).
  Proof.
    intros ix n c Htable Hnode.
    assert (Hguard : Pos.ltb (next ix) n = false) by now apply Pos.ltb_ge.
    unfold insert_step_st. rewrite Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n))); cbn [fst snd].
    - rewrite child_put_edge_same; [reflexivity |].
      apply table_ok_write; [exact Htable | exact Hnode | apply Pos.le_refl].
    - rewrite child_put_edge_same; [reflexivity |].
      apply table_ok_write; [exact Htable | |].
      + eapply Pos.le_trans; [exact Hnode | apply Pos.lt_le_incl, Pos.lt_succ_diag_r].
      + apply Pos.lt_le_incl, Pos.lt_succ_diag_r.
  Qed.

  Lemma insert_step_path : forall st c pre, shape (fst st) -> node (fst st) (snd st) pre ->
    node (fst (insert_step_st st c)) (snd (insert_step_st st c)) (pre ++ [c]).
  Proof.
    intros [ix n] c pre [Hshape [Htable Hparents]] Hnode.
    assert (Hbound : (n <= next ix)%positive).
    { eapply seek_bounded; [exact Hshape | apply Pos.le_1_l | exact Hnode]. }
    assert (Hprefix : seek (fst (insert_step_st (ix, n) c)) (root ix) pre = Some n).
    { eapply seek_preserve_endpoint; [exact Hshape | exact Htable | | | exact Hnode].
      - now apply table_ok_insert_step.
      - intros q Hneq. exact (insert_step_other_edges (ix, n) c q Hneq). }
    unfold node. change (seek (fst (insert_step_st (ix, n) c)) (root ix)
      (pre ++ [c]) = Some (snd (insert_step_st (ix, n) c))).
    rewrite seek_append, Hprefix. cbn [seek].
    rewrite (insert_step_child ix n c Htable Hbound). reflexivity.
  Qed.

  Lemma insert_walk_path : forall walk st pre, shape (fst st) ->
    node (fst st) (snd st) pre ->
    node (fst (fold_left insert_step_st walk st)) (snd (fold_left insert_step_st walk st))
      (pre ++ walk).
  Proof.
    induction walk as [| c walk IH]; intros st pre Hshape Hnode; cbn [fold_left].
    - now rewrite app_nil_r.
    - pose proof (IH (insert_step_st st c) (pre ++ [c])
        (shape_insert_step st c Hshape) (insert_step_path st c pre Hshape Hnode)) as Hpath.
      rewrite <- app_assoc in Hpath. exact Hpath.
  Qed.

  (** Insertion marks exactly its reached endpoint after preserving every old member. *)
  Lemma insert_membership : forall ix r u, shape ix ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  Proof.
    intros ix r u Hshape. unfold insert, insert_finish.
    destruct (contains r ix) eqn:Hpresent.
    - split; [now right |]. intros [-> | Hmem]; [exact Hpresent | exact Hmem].
    - set (st := fold_left insert_step_st r (start ix)).
      assert (Hshape' : shape (fst st)) by (apply shape_insert_walk; exact Hshape).
      assert (Hpath : node (fst st) (snd st) r).
      { exact (insert_walk_path r (start ix) [] Hshape eq_refl). }
      pose proof (shape_paths_unique (fst st) Hshape') as Hunique.
      pose proof (insert_walk_membership r (start ix) u 1%positive Hshape
        (Pos.le_1_l (next ix))) as Hmembers.
      change (contains_from 1%positive u (fst st) = contains_from 1%positive u ix) in Hmembers.
      unfold mem, contains. cbn [root]. rewrite mark_terminal_add.
      change ((seek (fst st) 1%positive u = Some (snd st) \/
        contains_from 1%positive u (fst st) = true) <->
        u = r \/ contains_from 1%positive u ix = true).
      rewrite Hmembers.
      split.
      + intros [Hnode | Hmem]; [left | now right].
        eapply Hunique; [exact Hnode | exact Hpath].
      + intros [-> | Hmem]; [now left | now right].
  Qed.

  Lemma degrees_ok_mark_terminal : forall ix n present bits,
    degrees_ok ix -> degrees_ok (mark_terminal ix n present bits).
  Proof.
    intros ix n present bits Hdegrees q. destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_mark_same. cbn [node_degree node_edges]. exact (Hdegrees n).
    - rewrite read_node_mark_other by exact Hneq. exact (Hdegrees q).
  Qed.

  Lemma shape_mark_terminal : forall ix n present bits, shape ix ->
    (n <= next ix)%positive -> shape (mark_terminal ix n present bits).
  Proof.
    intros ix n present bits [Hedges [Htable Hparents]] Hbound. split.
    - intros q key edge Hget. unfold stored_edge in Hget.
      rewrite mark_node_edges in Hget. exact (Hedges q key edge Hget).
    - split.
      + change (table_ok (write_node ix n
          (IndexNode (node_edges (read_node ix n)) (node_degree (read_node ix n)) present)
          (next ix))).
        apply table_ok_write; [exact Htable | exact Hbound | apply Pos.le_refl].
      + intros q key edge q' key' edge' Hget Hget' Hchild.
        unfold stored_edge in Hget, Hget'. rewrite mark_node_edges in Hget, Hget'.
        eapply Hparents; eassumption.
  Qed.

  Lemma edges_ok_mark_terminal : forall ix n present bits, edges_ok ix ->
    index_cell_width ix <= bits -> edges_ok (mark_terminal ix n present bits).
  Proof.
    intros ix n present bits Hedges Hwidth q key edge Hget.
    unfold stored_edge in Hget. rewrite mark_node_edges in Hget.
    destruct (Hedges q key edge Hget) as [Hcode [Hbounds [Hbits Hcount]]].
    split; [exact Hcode |]. split; [exact Hbounds |]. split; [| exact Hcount].
    change (cell_bits V.encode (edge_cell edge) <= bits). lia.
  Qed.

  Lemma remove_step_point_bound : forall st c, edge_shape (fst st) ->
    (snd st <= next (fst st))%positive ->
    (snd (remove_step_st st c) <= next (fst (remove_step_st st c)))%positive.
  Proof.
    intros [ix n] c Hshape Hbound. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hbound |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| exact Hbound].
    destruct (N.eqb (edge_count edge) 1%N);
      exact (proj2 (proj2 (Hshape n (encode_cell c) edge Hget))).
  Qed.

  Lemma remove_walk_point_bound : forall r st, shape (fst st) ->
    (snd st <= next (fst st))%positive ->
    (snd (fold_left remove_step_st r st) <= next (fst (fold_left remove_step_st r st)))%positive.
  Proof.
    induction r as [| c r IH]; intros st Hshape Hbound; cbn [fold_left]; [exact Hbound |].
    apply IH; [now apply shape_remove_step |].
    apply remove_step_point_bound; [exact (proj1 Hshape) | exact Hbound].
  Qed.

  Lemma remove_step_width : forall st c,
    index_cell_width (fst (remove_step_st st c)) = index_cell_width (fst st).
  Proof.
    intros [ix n] c. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [reflexivity |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |]; [| reflexivity].
    destruct (N.eqb (edge_count edge) 1%N); reflexivity.
  Qed.

  Lemma remove_walk_width : forall r st,
    index_cell_width (fst (fold_left remove_step_st r st)) = index_cell_width (fst st).
  Proof.
    induction r as [| c r IH]; intro st; cbn [fold_left]; [reflexivity |].
    rewrite IH. apply remove_step_width.
  Qed.

  Lemma shape_insert : forall ix r, shape ix -> shape (insert r ix).
  Proof.
    intros ix r Hshape. unfold insert, insert_finish.
    destruct (contains r ix); [exact Hshape |].
    apply shape_mark_terminal.
    - apply shape_insert_walk. exact Hshape.
    - eapply seek_bounded.
      + exact (proj1 (shape_insert_walk r (start ix) Hshape)).
      + apply Pos.le_1_l.
      + exact (insert_walk_path r (start ix) [] Hshape eq_refl).
  Qed.

  Lemma shape_remove : forall ix r, shape ix -> shape (remove r ix).
  Proof.
    intros ix r Hshape. unfold remove, remove_finish.
    destruct (contains r ix); [| exact Hshape].
    apply shape_mark_terminal.
    - apply shape_remove_walk. exact Hshape.
    - apply remove_walk_point_bound; [exact Hshape | apply Pos.le_1_l].
  Qed.

  Lemma degrees_ok_insert : forall ix r, degrees_ok ix -> degrees_ok (insert r ix).
  Proof.
    intros ix r Hdegrees. unfold insert, insert_finish.
    destruct (contains r ix); [exact Hdegrees |].
    apply degrees_ok_mark_terminal, degrees_ok_insert_walk. exact Hdegrees.
  Qed.

  Lemma degrees_ok_remove : forall ix r, degrees_ok ix -> degrees_ok (remove r ix).
  Proof.
    intros ix r Hdegrees. unfold remove, remove_finish.
    destruct (contains r ix); [| exact Hdegrees].
    apply degrees_ok_mark_terminal, degrees_ok_remove_walk. exact Hdegrees.
  Qed.

  Lemma edges_ok_remove : forall ix r, edges_ok ix -> edges_ok (remove r ix).
  Proof.
    intros ix r Hedges. unfold remove, remove_finish.
    destruct (contains r ix); [| exact Hedges].
    apply edges_ok_mark_terminal.
    - apply edges_ok_remove_walk. exact Hedges.
    - rewrite remove_walk_width. apply Nat.le_refl.
  Qed.

  Definition refines (ix ix' : t) : Prop :=
    (forall n c m, child ix' n c = Some m -> child ix n c = Some m) /\
    (forall n, node_terminal (read_node ix' n) = true ->
      node_terminal (read_node ix n) = true).

  Lemma refines_refl : forall ix, refines ix ix.
  Proof.
    intro ix. split; auto.
  Qed.

  Lemma refines_trans : forall ix ix' ix'', refines ix ix' -> refines ix' ix'' ->
    refines ix ix''.
  Proof.
    intros ix ix' ix'' [Hedges Hterminal] [Hedges' Hterminal']. split.
    - intros n c m Hchild. apply Hedges. now apply Hedges'.
    - intros n Hterm. apply Hterminal. now apply Hterminal'.
  Qed.

  Lemma seek_refinement : forall ix ix', refines ix ix' ->
    forall r n m, seek ix' n r = Some m -> seek ix n r = Some m.
  Proof.
    intros ix ix' [Hedges _] r. induction r as [| c r IH]; intros n m Hseek.
    - exact Hseek.
    - cbn [seek] in *. destruct (child ix' n c) as [q |] eqn:Hchild; [| discriminate].
      rewrite (Hedges n c q Hchild). now apply IH.
  Qed.

  Lemma contains_from_refinement : forall ix ix', refines ix ix' ->
    forall r n, contains_from n r ix' = true -> contains_from n r ix = true.
  Proof.
    intros ix ix' [Hedges Hterminal] r. induction r as [| c r IH]; intros n Hmember.
    - apply Hterminal. exact Hmember.
    - rewrite contains_from_cons in *. destruct (child ix' n c) as [q |] eqn:Hchild;
        [| discriminate].
      rewrite (Hedges n c q Hchild). now apply IH.
  Qed.

  Lemma terminal_drop_edge : forall ix n code degree counter q,
    node_terminal (read_node
      (write_node ix n
        (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
          (node_terminal (read_node ix n))) counter) q) =
      node_terminal (read_node ix q).
  Proof.
    intros ix n code degree counter q. destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_write_same. reflexivity.
    - now rewrite read_node_write_other.
  Qed.

  Lemma child_drop_edge_other : forall ix n code degree counter q c,
    table_ok ix ->
    table_ok (write_node ix n
      (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    (q <> n \/ encode_cell c <> code) ->
    child (write_node ix n
      (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) q c = child ix q c.
  Proof.
    intros ix n code degree counter q c Htable Htable' Hother.
    rewrite !child_raw by assumption.
    destruct (Pos.eq_dec q n) as [-> | Hneq].
    - rewrite read_node_write_same. cbn [node_edges].
      rewrite PTrie.get_remove_other by tauto. reflexivity.
    - rewrite read_node_write_other by exact Hneq. reflexivity.
  Qed.

  Lemma child_drop_edge_same : forall ix n c degree counter,
    table_ok (write_node ix n
      (IndexNode (PTrieCode.remove (encode_cell c) (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    child (write_node ix n
      (IndexNode (PTrieCode.remove (encode_cell c) (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) n c = None.
  Proof.
    intros ix n c degree counter Htable.
    rewrite child_raw by exact Htable. rewrite read_node_write_same. cbn [node_edges].
    rewrite PTrie.get_remove_same. reflexivity.
  Qed.

  Lemma child_drop_edge_refinement : forall ix n code degree counter,
    table_ok ix ->
    table_ok (write_node ix n
      (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) ->
    forall q c m,
    child (write_node ix n
      (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
        (node_terminal (read_node ix n))) counter) q c = Some m -> child ix q c = Some m.
  Proof.
    intros ix n code degree counter Htable Htable' q c m Hchild.
    rewrite child_raw in Hchild by exact Htable'.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node
      (write_node ix n
        (IndexNode (PTrieCode.remove code (node_edges (read_node ix n))) degree
          (node_terminal (read_node ix n))) counter) q))) as [edge |] eqn:Hget;
      [| discriminate].
    apply stored_edge_drop in Hget as [_ Hget].
    rewrite child_raw by exact Htable. rewrite Hget. exact Hchild.
  Qed.

  Lemma remove_step_refines : forall st c, shape (fst st) ->
    refines (fst st) (fst (remove_step_st st c)).
  Proof.
    intros [ix n] c [_ [Htable _]]. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n) eqn:Hguard; [apply refines_refl |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| apply refines_refl].
    destruct (N.eqb (edge_count edge) 1%N); cbn [fst]; split.
    - apply child_drop_edge_refinement; [exact Htable |].
      apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl].
    - intros q Hterm. rewrite terminal_drop_edge in Hterm. exact Hterm.
    - intros q d m Hchild.
      rewrite (child_put_edge_existing ix n (encode_cell c) edge) in Hchild;
        [exact Hchild | exact Htable | | exact Hget | reflexivity].
      apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl].
    - intros q Hterm. rewrite terminal_put_edge in Hterm. exact Hterm.
  Qed.

  Lemma remove_walk_refines : forall r st, shape (fst st) ->
    refines (fst st) (fst (fold_left remove_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros st Hshape; cbn [fold_left]; [apply refines_refl |].
    eapply refines_trans; [now apply remove_step_refines |].
    apply IH. now apply shape_remove_step.
  Qed.

  Lemma mark_terminal_delete_refines : forall ix n bits,
    refines ix (mark_terminal ix n false bits).
  Proof.
    intros ix n bits. split.
    - intros q c m Hchild. now rewrite child_mark_terminal in Hchild.
    - intros q Hterm. destruct (Pos.eq_dec q n) as [-> | Hneq].
      + rewrite read_node_mark_same in Hterm. discriminate.
      + now rewrite read_node_mark_other in Hterm.
  Qed.

  Lemma remove_refines : forall ix r, shape ix -> refines ix (remove r ix).
  Proof.
    intros ix r Hshape. unfold remove, remove_finish.
    destruct (contains r ix); [| apply refines_refl].
    eapply refines_trans; [| apply mark_terminal_delete_refines].
    apply remove_walk_refines. exact Hshape.
  Qed.

  Lemma remove_no_add : forall ix r u, shape ix -> mem (remove r ix) u -> mem ix u.
  Proof.
    intros ix r u Hshape Hmember.
    exact (contains_from_refinement ix (remove r ix) (remove_refines ix r Hshape)
      u 1%positive Hmember).
  Qed.

  (** A write below a starting node cannot affect any of its increasing paths. *)
  Lemma seek_above_change : forall ix ix' cut,
    edge_shape ix -> table_ok ix -> table_ok ix' ->
    (forall q, q <> cut -> read_node ix' q = read_node ix q) ->
    forall r q, (cut < q)%positive -> seek ix' q r = seek ix q r.
  Proof.
    intros ix ix' cut Hshape Htable Htable' Hread r.
    induction r as [| c r IH]; intros q Habove; cbn [seek]; [reflexivity |].
    assert (Hneq : q <> cut) by (intro Heq; subst q; exact (Pos.lt_irrefl _ Habove)).
    assert (Hchild : child ix' q c = child ix q c).
    { rewrite !child_raw by assumption. now rewrite Hread. }
    rewrite Hchild. destruct (child ix q c) as [m |] eqn:Hedge; [| reflexivity].
    apply IH. eapply Pos.lt_trans; [exact Habove |].
    exact (proj1 (child_forward ix q c m Hshape Hedge)).
  Qed.

  Lemma contains_from_above_change : forall ix ix' cut,
    edge_shape ix -> table_ok ix -> table_ok ix' ->
    (forall q, q <> cut -> read_node ix' q = read_node ix q) ->
    forall r q, (cut < q)%positive -> contains_from q r ix' = contains_from q r ix.
  Proof.
    intros ix ix' cut Hshape Htable Htable' Hread r q Habove. unfold contains_from.
    rewrite (seek_above_change ix ix' cut Hshape Htable Htable' Hread r q Habove).
    destruct (seek ix q r) as [m |] eqn:Hseek; [| reflexivity].
    rewrite Hread; [reflexivity |].
    intro Heq. subst m. pose proof (seek_forward ix r q cut Hshape Hseek) as Hle.
    apply Pos.lt_nle in Habove. contradiction.
  Qed.

  Lemma remove_step_other_nodes : forall st c q, q <> snd st ->
    read_node (fst (remove_step_st st c)) q = read_node (fst st) q.
  Proof.
    intros [ix n] c q Hneq. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [reflexivity |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |]; [| reflexivity].
    destruct (N.eqb (edge_count edge) 1%N); cbn [fst];
      now rewrite read_node_write_other.
  Qed.

  Lemma remove_step_pointer : forall ix n c m, child ix n c = Some m ->
    snd (remove_step_st (ix, n) c) = m.
  Proof.
    intros ix n c m Hchild. unfold child in Hchild. unfold remove_step_st.
    destruct (Pos.ltb (next ix) n); [discriminate |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |]; [| discriminate].
    injection Hchild as <-. destruct (N.eqb (edge_count edge) 1%N); reflexivity.
  Qed.

  Lemma remove_step_descendant_seek : forall ix n c m, shape ix ->
    child ix n c = Some m -> forall r,
    seek (fst (remove_step_st (ix, n) c)) m r = seek ix m r.
  Proof.
    intros ix n c m [Hshape [Htable Hparents]] Hchild r.
    eapply seek_above_change with (cut := n);
      [exact Hshape | exact Htable | | |].
    - apply table_ok_remove_step. exact Htable.
    - intros q Hneq. exact (remove_step_other_nodes (ix, n) c q Hneq).
    - exact (proj1 (child_forward ix n c m Hshape Hchild)).
  Qed.

  Lemma remove_walk_pointer : forall r st m, shape (fst st) ->
    seek (fst st) (snd st) r = Some m -> snd (fold_left remove_step_st r st) = m.
  Proof.
    induction r as [| c r IH]; intros [ix n] m Hshape Hseek.
    - cbn [fold_left seek fst snd] in *. now injection Hseek.
    - cbn [fold_left seek fst snd] in *.
      destruct (child ix n c) as [q |] eqn:Hchild; [| discriminate].
      apply IH.
      + apply shape_remove_step. exact Hshape.
      + rewrite (remove_step_pointer ix n c q Hchild).
        rewrite (remove_step_descendant_seek ix n c q Hshape Hchild). exact Hseek.
  Qed.

  Lemma remove_target_absent : forall ix r, shape ix -> ~ mem (remove r ix) r.
  Proof.
    intros ix r Hshape. unfold remove, remove_finish.
    destruct (contains r ix) eqn:Hpresent.
    - set (st := fold_left remove_step_st r (start ix)).
      intro Hmember. unfold mem, contains in Hmember.
      apply mark_terminal_delete in Hmember as [Hmissing Hbefore].
      change (contains_from 1%positive r (fst st) = true) in Hbefore.
      unfold contains_from in Hbefore.
      destruct (seek (fst st) 1%positive r) as [m |] eqn:Hseek; [| discriminate].
      pose proof (seek_refinement ix (fst st) (remove_walk_refines r (start ix) Hshape)
        r 1%positive m Hseek) as Horiginal.
      pose proof (remove_walk_pointer r (start ix) m Hshape Horiginal) as Hpointer.
      change (snd st = m) in Hpointer.
      apply Hmissing. change (seek (fst st) 1%positive r = Some (snd st)).
      now rewrite Hpointer.
    - intro Hmember. unfold mem in Hmember. congruence.
  Qed.

  Lemma remove_membership_sound : forall ix r u, shape ix -> mem (remove r ix) u ->
    u <> r /\ mem ix u.
  Proof.
    intros ix r u Hshape Hmember. split.
    - intro Heq. subst u. exact (remove_target_absent ix r Hshape Hmember).
    - eapply remove_no_add; eassumption.
  Qed.

  (** A stored count of one permits only one live suffix below that edge. *)
  Lemma counted_edge_singleton : forall ix n code edge,
    counted_edges ix -> stored_edge ix n code edge -> edge_count edge = 1%N ->
    forall r s, contains_from (edge_child edge) r ix = true ->
      contains_from (edge_child edge) s ix = true -> r = s.
  Proof.
    intros ix n code edge Hcounts Hget Hone r s Hr Hs.
    destruct (Hcounts n code edge Hget) as [suffixes [_ [Hmembers Hcount]]].
    assert (Hlength : length suffixes = 1).
    { apply Nat2N.inj. rewrite <- Hcount. exact Hone. }
    destruct suffixes as [| suffix suffixes]; [discriminate |].
    destruct suffixes as [| second suffixes]; [| discriminate].
    apply Hmembers in Hr, Hs. cbn [In] in Hr, Hs. intuition congruence.
  Qed.

  (** Losing a member after changing just one arc exposes the exact traversed arc. *)
  Lemma edge_deletion_loss : forall ix ix' n c m, child ix n c = Some m ->
    (forall q d, q <> n \/ encode_cell d <> encode_cell c -> child ix' q d = child ix q d) ->
    (forall q, node_terminal (read_node ix' q) = node_terminal (read_node ix q)) ->
    forall u q, contains_from q u ix = true -> contains_from q u ix' = false ->
    exists pre suf, u = pre ++ c :: suf /\ seek ix q pre = Some n /\
      contains_from m suf ix = true.
  Proof.
    intros ix ix' n c m Htarget Hother Hterminal u.
    induction u as [| d u IH]; intros q Hmember Hmissing.
    - change (node_terminal (read_node ix q) = true) in Hmember.
      change (node_terminal (read_node ix' q) = false) in Hmissing.
      rewrite Hterminal in Hmissing. congruence.
    - rewrite contains_from_cons in Hmember, Hmissing.
      destruct (child ix q d) as [p |] eqn:Hchild; [| discriminate].
      destruct (Pos.eq_dec q n) as [Hnode | Hnode];
        destruct (Pos.eq_dec (encode_cell d) (encode_cell c)) as [Hcode | Hcode].
      + subst q. apply encode_cell_inj in Hcode. subst d.
        rewrite Htarget in Hchild. injection Hchild as <-.
        exists [], u. repeat split; assumption || reflexivity.
      + rewrite Hother in Hmissing by tauto. rewrite Hchild in Hmissing.
        destruct (IH p Hmember Hmissing) as [pre [suf [Htuple [Hseek Hsuffix]]]].
        exists (d :: pre), suf. split; [cbn [app]; now rewrite Htuple |].
        split; [cbn [seek]; now rewrite Hchild | exact Hsuffix].
      + rewrite Hother in Hmissing by tauto. rewrite Hchild in Hmissing.
        destruct (IH p Hmember Hmissing) as [pre [suf [Htuple [Hseek Hsuffix]]]].
        exists (d :: pre), suf. split; [cbn [app]; now rewrite Htuple |].
        split; [cbn [seek]; now rewrite Hchild | exact Hsuffix].
      + rewrite Hother in Hmissing by tauto. rewrite Hchild in Hmissing.
        destruct (IH p Hmember Hmissing) as [pre [suf [Htuple [Hseek Hsuffix]]]].
        exists (d :: pre), suf. split; [cbn [app]; now rewrite Htuple |].
        split; [cbn [seek]; now rewrite Hchild | exact Hsuffix].
  Qed.

  Lemma deleted_member_is_target : forall original ix ix' n c edge pre suf,
    valid original -> refines original ix -> node original n pre ->
    stored_edge original n (encode_cell c) edge -> edge_count edge = 1%N ->
    contains_from (edge_child edge) suf original = true ->
    child ix n c = Some (edge_child edge) ->
    (forall q d, q <> n \/ encode_cell d <> encode_cell c -> child ix' q d = child ix q d) ->
    (forall q, node_terminal (read_node ix' q) = node_terminal (read_node ix q)) ->
    forall u, mem ix u -> contains u ix' = false -> u = pre ++ c :: suf.
  Proof.
    intros original ix ix' n c edge pre suf Hvalid Hrefines Hnode Hget Hone Hsuffix
      Hchild Hother Hterminal u Hmember Hmissing.
    pose proof (valid_shape original Hvalid) as Hshape.
    destruct Hvalid as [_ [_ [_ [_ [_ Hcounts]]]]].
    destruct (edge_deletion_loss ix ix' n c (edge_child edge) Hchild Hother Hterminal
      u 1%positive Hmember Hmissing) as [prefix [suffix [Htuple [Hprefix Htail]]]].
    pose proof (seek_refinement original ix Hrefines prefix 1%positive n Hprefix) as Hprefix'.
    assert (Hprefix_eq : prefix = pre).
    { eapply (shape_paths_unique original Hshape); [exact Hprefix' | exact Hnode]. }
    subst prefix.
    pose proof (contains_from_refinement original ix Hrefines suffix (edge_child edge) Htail)
      as Htail'.
    pose proof (counted_edge_singleton original n (encode_cell c) edge Hcounts Hget Hone
      suffix suf Htail' Hsuffix) as Hsuffix_eq.
    now rewrite Hsuffix_eq in Htuple.
  Qed.

  Lemma remove_step_preserves_other : forall original ix n c pre suf u,
    valid original -> shape ix -> refines original ix ->
    read_node ix n = read_node original n -> node original n pre ->
    mem original (pre ++ c :: suf) -> u <> pre ++ c :: suf -> mem ix u ->
    mem (fst (remove_step_st (ix, n) c)) u.
  Proof.
    intros original ix n c pre suf u Hvalid [_ [Htable _]] Hrefines Hread Hnode
      Htarget Hneq Hmember.
    pose proof (proj1 (proj2 (valid_shape original Hvalid))) as Htable_original.
    unfold remove_step_st. destruct (Pos.ltb (next ix) n) eqn:Hguard; [exact Hmember |].
    apply Pos.ltb_ge in Hguard.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| exact Hmember].
    assert (Horiginal : stored_edge original n (encode_cell c) edge).
    { unfold stored_edge. rewrite <- Hread. exact Hget. }
    destruct (N.eqb (edge_count edge) 1%N) eqn:Hone; cbn [fst].
    - set (out := write_node ix n
        (IndexNode (PTrieCode.remove (encode_cell c) (node_edges (read_node ix n)))
          (N.pred (node_degree (read_node ix n))) (node_terminal (read_node ix n)))
        (next ix)).
      assert (Htable' : table_ok out).
      { unfold out. apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl]. }
      change (contains u out = true).
      destruct (contains u out) eqn:Hpresent; [reflexivity |].
      exfalso. apply Hneq.
      eapply (deleted_member_is_target original ix out n c edge pre suf);
        try exact Hvalid; try exact Hrefines; try exact Hnode; try exact Horiginal;
        try exact Hmember; try exact Hpresent.
      + now apply N.eqb_eq.
      + pose proof (proj1 (node_member_suffix original n pre (c :: suf) Hnode) Htarget)
          as Htail.
        rewrite contains_from_cons in Htail.
        rewrite child_raw in Htail by exact Htable_original.
        unfold stored_edge in Horiginal. rewrite Horiginal in Htail. exact Htail.
      + rewrite child_raw by exact Htable. rewrite Hget. reflexivity.
      + intros q d Hdiff. unfold out. apply child_drop_edge_other; assumption.
      + intro q. unfold out. apply terminal_drop_edge.
    - set (out := write_node ix n
        (IndexNode (PTrieCode.set (encode_cell c)
          (IndexEdge (edge_cell edge) (edge_child edge) (N.pred (edge_count edge)))
          (node_edges (read_node ix n))) (node_degree (read_node ix n))
          (node_terminal (read_node ix n))) (next ix)).
      assert (Htable' : table_ok out).
      { unfold out. apply table_ok_write; [exact Htable | exact Hguard | apply Pos.le_refl]. }
      assert (Hchildren : forall q d, child out q d = child ix q d).
      { intros q d. unfold out. eapply child_put_edge_existing with (old := edge);
          try assumption; reflexivity. }
      assert (Hterminal : forall q,
        node_terminal (read_node out q) = node_terminal (read_node ix q)).
      { intro q. unfold out. apply terminal_put_edge. }
      change (contains_from 1%positive u out = true).
      rewrite (contains_from_extensional ix out Hchildren Hterminal u 1%positive).
      exact Hmember.
  Qed.

  Lemma remove_walk_preserves_other : forall original walk st pre u,
    valid original -> shape (fst st) -> refines original (fst st) ->
    node original (snd st) pre ->
    (forall q, (snd st <= q)%positive -> read_node (fst st) q = read_node original q) ->
    mem original (pre ++ walk) -> u <> pre ++ walk -> mem (fst st) u ->
    mem (fst (fold_left remove_step_st walk st)) u.
  Proof.
    intros original walk. induction walk as [| c walk IH];
      intros [ix n] pre u Hvalid Hshape Hrefines Hnode Hread Htarget Hneq Hmember;
      cbn [fold_left]; [exact Hmember |].
    cbn [fst snd] in Hshape, Hrefines, Hnode, Hread, Hmember.
    pose proof (valid_shape original Hvalid) as Horiginal_shape.
    pose proof (proj1 (node_member_suffix original n pre (c :: walk) Hnode) Htarget) as Htail.
    rewrite contains_from_cons in Htail.
    destruct (child original n c) as [m |] eqn:Horiginal_child; [| discriminate].
    assert (Hchild : child ix n c = Some m).
    { rewrite child_raw by exact (proj1 (proj2 Hshape)).
      rewrite (Hread n (Pos.le_refl n)).
      rewrite <- child_raw by exact (proj1 (proj2 Horiginal_shape)).
      exact Horiginal_child. }
    pose proof (remove_step_pointer ix n c m Hchild) as Hpointer.
    pose proof (proj1 (child_forward original n c m (proj1 Horiginal_shape) Horiginal_child))
      as Hforward.
    apply (IH (remove_step_st (ix, n) c) (pre ++ [c]) u).
    - exact Hvalid.
    - apply shape_remove_step. exact Hshape.
    - eapply refines_trans; [exact Hrefines |]. apply remove_step_refines. exact Hshape.
    - rewrite Hpointer. apply (child_node original n pre c m Hnode). exact Horiginal_child.
    - intros q Hbound. rewrite Hpointer in Hbound.
      assert (Habove : (n < q)%positive) by (eapply Pos.lt_le_trans; eassumption).
      rewrite remove_step_other_nodes.
      + apply Hread. now apply Pos.lt_le_incl.
      + cbn [snd]. intro Heq. subst q. exact (Pos.lt_irrefl _ Habove).
    - rewrite <- app_assoc. exact Htarget.
    - rewrite <- app_assoc. exact Hneq.
    - apply (remove_step_preserves_other original ix n c pre walk u);
        try assumption.
      apply Hread, Pos.le_refl.
  Qed.

  Lemma remove_membership_complete : forall ix r u, valid ix ->
    u <> r -> mem ix u -> mem (remove r ix) u.
  Proof.
    intros ix r u Hvalid Hneq Hmember.
    pose proof (valid_shape ix Hvalid) as Hshape.
    unfold remove, remove_finish. destruct (contains r ix) eqn:Htarget; [| exact Hmember].
    set (st := fold_left remove_step_st r (start ix)).
    assert (Hbefore : mem (fst st) u).
    { apply (remove_walk_preserves_other ix r (start ix) [] u);
        try assumption; try apply refines_refl; reflexivity. }
    unfold contains, contains_from in Htarget.
    destruct (seek ix (root ix) r) as [m |] eqn:Hpath; [| discriminate].
    pose proof (remove_walk_pointer r (start ix) m Hshape Hpath) as Hpointer.
    change (snd st = m) in Hpointer.
    change (contains_from 1%positive u
      (mark_terminal (fst st) (snd st) false (index_cell_width ix)) = true).
    apply mark_terminal_delete. split; [| exact Hbefore].
    intro Hseek. rewrite Hpointer in Hseek.
    pose proof (seek_refinement ix (fst st) (remove_walk_refines r (start ix) Hshape)
      u 1%positive m Hseek) as Horiginal.
    apply Hneq. eapply (shape_paths_unique ix Hshape); [exact Horiginal | exact Hpath].
  Qed.

  (** Positive cached suffix counts witness a live continuation below every edge. *)
  Lemma child_live : forall ix n c m, valid ix -> child ix n c = Some m ->
    exists suf, contains_from m suf ix = true.
  Proof.
    intros ix n c m [Hedges [_ [_ [_ [_ Hcounts]]]]] Hchild.
    unfold child in Hchild. destruct (Pos.ltb (next ix) n); [discriminate |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| discriminate].
    injection Hchild as <-.
    pose proof (Hedges n (encode_cell c) edge Hget) as [_ [_ [_ [Hpositive _]]]].
    destruct (Hcounts n (encode_cell c) edge Hget) as [suffixes [_ [Hmembers Hcount]]].
    destruct suffixes as [| suf suffixes].
    - cbn [length N.of_nat] in Hcount. rewrite Hcount in Hpositive. discriminate.
    - exists suf. apply Hmembers. now left.
  Qed.

  Lemma child_cell_bound : forall ix n c m, valid ix -> child ix n c = Some m ->
    cell_bits V.encode c <= index_cell_width ix.
  Proof.
    intros ix n c m [Hedges _] Hchild.
    unfold child in Hchild. destruct (Pos.ltb (next ix) n); [discriminate |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; [| discriminate].
    destruct (Hedges n (encode_cell c) edge Hget) as [Hcode [_ [Hbits _]]].
    apply encode_cell_inj in Hcode. now rewrite <- Hcode.
  Qed.

  Lemma seek_cell_bound : forall ix r n m c, valid ix -> seek ix n r = Some m ->
    In c r -> cell_bits V.encode c <= index_cell_width ix.
  Proof.
    intros ix r. induction r as [| d r IH]; intros n m c Hvalid Hseek Hin.
    - contradiction.
    - cbn [seek] in Hseek.
      destruct (child ix n d) as [child_node |] eqn:Hchild; [| discriminate].
      destruct Hin as [<- | Hin].
      + eapply child_cell_bound; eassumption.
      + eapply IH; eassumption.
  Qed.

  Lemma seek_live_nonempty : forall ix pre n m, valid ix -> pre <> [] ->
    seek ix n pre = Some m -> exists suf, contains_from m suf ix = true.
  Proof.
    intros ix pre. induction pre as [| c pre IH]; intros n m Hvalid Hnonempty Hseek.
    - contradiction.
    - cbn [seek] in Hseek.
      destruct (child ix n c) as [child_node |] eqn:Hchild; [| discriminate].
      destruct pre as [| d pre].
      + cbn [seek] in Hseek. injection Hseek as <-.
        eapply child_live; eassumption.
      + eapply IH; [exact Hvalid | discriminate | exact Hseek].
  Qed.

  Lemma node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] ->
    exists suf, mem ix (pre ++ suf).
  Proof.
    intros a ix n pre [Hvalid _] Hnode Hnonempty.
    destruct (seek_live_nonempty ix pre (root ix) n Hvalid Hnonempty Hnode)
      as [suf Hmember].
    exists suf. now apply (node_member_suffix ix n pre suf Hnode).
  Qed.

  Lemma node_fun : forall a ix n m pre, wf a ix ->
    node ix n pre -> node ix m pre -> n = m.
  Proof.
    intros a ix n m pre _ Hn Hm. unfold node in *. congruence.
  Qed.

  Lemma child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  Proof.
    intros a ix n pre c Hwf Hnode. split.
    - intro m. now apply child_node.
    - split.
      + intros Hchild [suf Hmember].
        apply (node_member_suffix ix n pre (c :: suf) Hnode) in Hmember.
        unfold contains_from in Hmember. cbn [seek] in Hmember.
        rewrite Hchild in Hmember. discriminate.
      + intro Habsent. destruct (child ix n c) as [m |] eqn:Hchild; [| reflexivity].
        exfalso. apply Habsent.
        destruct (child_live ix n c m (proj1 Hwf) Hchild) as [suf Hmember].
        exists suf. apply (node_member_suffix ix n pre (c :: suf) Hnode).
        unfold contains_from. cbn [seek]. rewrite Hchild. exact Hmember.
  Qed.

  Lemma children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\
    NoDup (children ix n).
  Proof.
    intros a ix n pre c [[Hedges _] _] _.
    unfold children, child. destruct (Pos.ltb (next ix) n).
    - split; [split; [contradiction | intros [m Hm]; discriminate] | constructor].
    - assert (Hcode : forall entry,
        In entry (PTrieCode.elements (node_edges (read_node ix n))) ->
        encode_cell (edge_cell (snd entry)) = fst entry).
      { intros [code edge] Hin. cbn [fst snd].
        apply PTrie.elements_spec in Hin. exact (proj1 (Hedges n code edge Hin)). }
      split.
      + split.
        * intro Hin. apply in_map_iff in Hin as [[code edge] [Heq Hin]].
          cbn [snd] in Heq. subst c.
          pose proof (Hcode (code, edge) Hin) as Hencode. cbn [fst snd] in Hencode.
          apply PTrie.elements_spec in Hin. rewrite Hencode, Hin.
          now exists (edge_child edge).
        * intros [m Hchild].
          destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
            as [edge |] eqn:Hget; [| discriminate].
          apply in_map_iff. exists (encode_cell c, edge). split.
          -- cbn [snd]. apply encode_cell_inj. exact (proj1 (Hedges n _ _ Hget)).
          -- now apply PTrie.elements_spec.
      + apply NoDup_map_inv with (f := encode_cell). rewrite map_map.
        replace (map (fun x => encode_cell (edge_cell (snd x)))
          (PTrieCode.elements (node_edges (read_node ix n)))) with
          (map fst (PTrieCode.elements (node_edges (read_node ix n)))).
        * apply PTrie.elements_nodup.
        * symmetry. apply map_ext_in. exact Hcode.
  Qed.

  Lemma degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
  Proof.
    intros a ix n pre [[_ [Hdegree _]] _] _.
    unfold degree, children. destruct (Pos.ltb (next ix) n); [reflexivity |].
    rewrite length_map. exact (proj1 (Hdegree n)).
  Qed.

  Lemma mem_insert : forall a r ix u, wf a ix -> length r = a ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  Proof.
    intros a r ix u [Hvalid _] _. apply insert_membership. now apply valid_shape.
  Qed.

  Lemma mem_remove : forall a r ix u, wf a ix ->
    (mem (remove r ix) u <-> u <> r /\ mem ix u).
  Proof.
    intros a r ix u [Hvalid _]. split.
    - apply remove_membership_sound. now apply valid_shape.
    - intros [Hneq Hmember]. now apply remove_membership_complete.
  Qed.

  Definition reaches (ix : t) (source target : positive) : Prop :=
    exists path, seek ix source path = Some target.

  Lemma reaches_self : forall ix n, reaches ix n n.
  Proof.
    intros ix n. exists []. reflexivity.
  Qed.

  Lemma reaches_no_backward : forall ix source target, edge_shape ix ->
    (target < source)%positive -> ~ reaches ix source target.
  Proof.
    intros ix source target Hshape Hlt [path Hseek].
    pose proof (seek_forward ix path source target Hshape Hseek) as Hle.
    apply Pos.lt_nle in Hlt. contradiction.
  Qed.

  (** A distinct source reaches a child precisely when it reaches its unique parent. *)
  Lemma reaches_parent : forall ix n c m source, parents_unique ix ->
    child ix n c = Some m -> source <> m ->
    (reaches ix source m <-> reaches ix source n).
  Proof.
    intros ix n c m source Hparents Hchild Hneq. split.
    - intros [path Hseek]. destruct (rev path) as [| d rest] eqn:Hrev.
      + apply (f_equal (@rev (cell V.t))) in Hrev.
        rewrite rev_involutive in Hrev. cbn [rev] in Hrev. subst path.
        cbn [seek] in Hseek. injection Hseek as Heq. contradiction.
      + assert (Hpath : path = rev rest ++ [d]).
        { rewrite <- (rev_involutive path), Hrev. reflexivity. }
        rewrite Hpath, seek_append in Hseek.
        destruct (seek ix source (rev rest)) as [q |] eqn:Hprefix; [| discriminate].
        cbn [seek] in Hseek.
        destruct (child ix q d) as [out |] eqn:Hlast; [| discriminate].
        injection Hseek as ->.
        destruct (child_parents_unique ix q d n c m Hparents Hlast Hchild) as [-> _].
        now exists (rev rest).
    - intros [path Hseek]. exists (path ++ [c]).
      rewrite seek_append, Hseek. cbn [seek]. now rewrite Hchild.
  Qed.

  Lemma stored_child_parent : forall ix n code edge parent c m, parents_unique ix ->
    stored_edge ix n code edge -> child ix parent c = Some m -> edge_child edge = m ->
    n = parent /\ code = encode_cell c.
  Proof.
    intros ix n code edge parent c m Hparents Hget Hchild Hsame.
    unfold child in Hchild. destruct (Pos.ltb (next ix) parent); [discriminate |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix parent)))
      as [other |] eqn:Hother; [| discriminate].
    eapply Hparents; [exact Hget | exact Hother | congruence].
  Qed.

  Lemma insert_step_reaches_cursor : forall ix n c source, shape ix ->
    (reaches (fst (insert_step_st (ix, n) c)) source n <-> reaches ix source n).
  Proof.
    intros ix n c source Hshape.
    pose proof (shape_insert_step (ix, n) c Hshape) as Hshape'.
    split; intros [path Hpath]; exists path.
    - eapply seek_preserve_endpoint; [exact (proj1 Hshape') |
        exact (proj1 (proj2 Hshape')) | exact (proj1 (proj2 Hshape)) | | exact Hpath].
      intros q Hneq. symmetry. exact (insert_step_other_edges (ix, n) c q Hneq).
    - eapply seek_preserve_endpoint; [exact (proj1 Hshape) |
        exact (proj1 (proj2 Hshape)) | exact (proj1 (proj2 Hshape')) | | exact Hpath].
      intros q Hneq. exact (insert_step_other_edges (ix, n) c q Hneq).
  Qed.

  Lemma insert_step_reaches_next : forall ix n c source, shape ix ->
    (n <= next ix)%positive -> source <> snd (insert_step_st (ix, n) c) ->
    (reaches (fst (insert_step_st (ix, n) c)) source (snd (insert_step_st (ix, n) c)) <->
      reaches ix source n).
  Proof.
    intros ix n c source Hshape Hbound Hneq.
    pose proof (shape_insert_step (ix, n) c Hshape) as Hshape'.
    rewrite (reaches_parent _ n c _ source (proj2 (proj2 Hshape'))
      (insert_step_child ix n c (proj1 (proj2 Hshape)) Hbound) Hneq).
    apply insert_step_reaches_cursor. exact Hshape.
  Qed.

  (** Counts include one pending insertion for precisely the ancestors of its current node. *)
  Definition pending_insert_edge (ix : t) (cursor : positive)
      (edge : index_edge (cell V.t)) : Prop :=
    exists suffixes pending, NoDup suffixes /\
      (forall r, In r suffixes <-> contains_from (edge_child edge) r ix = true) /\
      (pending = true <-> reaches ix (edge_child edge) cursor) /\
      edge_count edge = (N.of_nat (length suffixes) + if pending then 1 else 0)%N.

  Definition pending_insert_counts (ix : t) (cursor : positive) : Prop :=
    forall n code edge, stored_edge ix n code edge -> pending_insert_edge ix cursor edge.

  Lemma pending_insert_start : forall ix, shape ix -> counted_edges ix ->
    pending_insert_counts ix (root ix).
  Proof.
    intros ix Hshape Hcounts n code edge Hget.
    destruct (Hcounts n code edge Hget) as [suffixes [Hnodup [Hmembers Hcount]]].
    exists suffixes, false. split; [exact Hnodup |]. split; [exact Hmembers |]. split.
    - split; [discriminate |]. intro Hreach. exfalso.
      eapply reaches_no_backward; [exact (proj1 Hshape) | | exact Hreach].
      destruct ((proj1 Hshape) n code edge Hget) as [_ [Hforward _]].
      change (1 < edge_child edge)%positive. lia.
    - cbn. now rewrite N.add_0_r.
  Qed.

  (** Marking a previously absent terminal turns every pending credit into a real suffix. *)
  Lemma pending_insert_finish : forall ix cursor bits, shape ix ->
    pending_insert_counts ix cursor -> node_terminal (read_node ix cursor) = false ->
    counted_edges (mark_terminal ix cursor true bits).
  Proof.
    intros ix cursor bits Hshape Hcounts Habsent n code edge Hget.
    unfold stored_edge in Hget. rewrite mark_node_edges in Hget.
    destruct (Hcounts n code edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    destruct pending.
    - destruct (proj1 Hpending eq_refl) as [path Hpath].
      exists (path :: suffixes). split.
      + constructor; [| exact Hnodup]. intro Hin. apply Hmembers in Hin.
        unfold contains_from in Hin. rewrite Hpath, Habsent in Hin. discriminate.
      + split.
        * intro r. rewrite mark_terminal_add. cbn [In]. rewrite Hmembers. split.
          -- intros [-> | Hmember]; [now left | now right].
          -- intros [Hseek | Hmember]; [left | now right].
             symmetry. eapply seek_paths_unique; [exact Hshape | exact Hseek | exact Hpath].
        * cbn [length] in *. rewrite Nat2N.inj_succ. lia.
    - exists suffixes. split; [exact Hnodup |]. split.
      + intro r. rewrite mark_terminal_add, Hmembers. split; [now right |].
        intros [Hseek | Hmember]; [| exact Hmember].
        assert (Hbad : false = true) by (apply Hpending; now exists r). discriminate.
      + cbn in Hcount. now rewrite N.add_0_r in Hcount.
  Qed.

  Lemma pending_current_count_bound : forall ix n code edge, shape ix ->
    pending_insert_counts ix n -> stored_edge ix n code edge ->
    (edge_count edge < Npos (next ix))%N.
  Proof.
    intros ix n code edge Hshape Hcounts Hget.
    destruct ((proj1 Hshape) n code edge Hget) as [_ [Hforward Hupper]].
    destruct (Hcounts n code edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    destruct pending.
    - exfalso. eapply reaches_no_backward;
        [exact (proj1 Hshape) | exact Hforward | now apply Hpending].
    - cbn in Hcount. rewrite N.add_0_r in Hcount.
      assert (Hrange : (1 < edge_child edge <= next ix)%positive) by (split; lia).
      pose proof (live_suffixes_bound ix (edge_child edge) suffixes Hshape Hrange Hnodup
        (fun r Hr => proj1 (Hmembers r) Hr)) as Hlength.
      rewrite Hcount. pose proof (Pos2Nat.is_pos (next ix)). lia.
  Qed.

  (** Every unchanged edge retains its inventory and pending-ancestor status. *)
  Lemma pending_insert_other : forall ix n c q code edge, shape ix ->
    pending_insert_counts ix n -> (n <= next ix)%positive ->
    stored_edge ix q code edge ->
    stored_edge (fst (insert_step_st (ix, n) c)) q code edge ->
    (q <> n \/ code <> encode_cell c) ->
    pending_insert_edge (fst (insert_step_st (ix, n) c))
      (snd (insert_step_st (ix, n) c)) edge.
  Proof.
    intros ix n c q code edge Hshape Hcounts Hbound Hget Hget' Hdiff.
    pose proof (shape_insert_step (ix, n) c Hshape) as Hshape'.
    pose proof (insert_step_child ix n c (proj1 (proj2 Hshape)) Hbound) as Hchild.
    assert (Hneq : edge_child edge <> snd (insert_step_st (ix, n) c)).
    { intro Heq. destruct (stored_child_parent _ q code edge n c _
        (proj2 (proj2 Hshape')) Hget' Hchild Heq) as [Hnode Hcode]. tauto. }
    destruct (Hcounts q code edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    exists suffixes, pending. split; [exact Hnodup |]. split.
    - intro r. rewrite (insert_step_membership (ix, n) c r (edge_child edge) Hshape).
      + apply Hmembers.
      + exact (proj2 (proj2 ((proj1 Hshape) q code edge Hget))).
    - split; [| exact Hcount].
      rewrite (insert_step_reaches_next ix n c (edge_child edge) Hshape Hbound Hneq).
      exact Hpending.
  Qed.

  Lemma pending_insert_existing : forall ix n c edge, shape ix ->
    pending_insert_counts ix n -> (n <= next ix)%positive ->
    PTrieCode.get (encode_cell c) (node_edges (read_node ix n)) = Some edge ->
    pending_insert_edge (fst (insert_step_st (ix, n) c))
      (snd (insert_step_st (ix, n) c))
      (IndexEdge c (edge_child edge) (bounded_succ (next ix) (edge_count edge))).
  Proof.
    intros ix n c edge Hshape Hcounts Hbound Hget.
    pose proof (pending_current_count_bound ix n (encode_cell c) edge Hshape Hcounts Hget)
      as Hcount_bound.
    destruct ((proj1 Hshape) n (encode_cell c) edge Hget) as [_ [Hforward Hupper]].
    destruct (Hcounts n (encode_cell c) edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    destruct pending.
    - exfalso. eapply reaches_no_backward;
        [exact (proj1 Hshape) | exact Hforward | now apply Hpending].
    - assert (Hguard : Pos.ltb (next ix) n = false) by now apply Pos.ltb_ge.
      assert (Hpointer : snd (insert_step_st (ix, n) c) = edge_child edge).
      { unfold insert_step_st. now rewrite Hguard, Hget. }
      exists suffixes, true. split; [exact Hnodup |]. split.
      + intro r. cbn [edge_child].
        rewrite (insert_step_membership (ix, n) c r (edge_child edge) Hshape Hupper).
        apply Hmembers.
      + split.
        * cbn [edge_child]. rewrite Hpointer. split; [intros _; apply reaches_self | reflexivity].
        * cbn [edge_count]. rewrite bounded_succ_small by now apply N.lt_le_incl.
          cbn in Hcount. rewrite N.add_0_r in Hcount. rewrite Hcount. lia.
  Qed.

  Lemma pending_insert_fresh : forall ix n c, shape ix -> (n <= next ix)%positive ->
    PTrieCode.get (encode_cell c) (node_edges (read_node ix n)) = None ->
    pending_insert_edge (fst (insert_step_st (ix, n) c))
      (snd (insert_step_st (ix, n) c)) (IndexEdge c (Pos.succ (next ix)) 1%N).
  Proof.
    intros ix n c Hshape Hbound Hget.
    assert (Hguard : Pos.ltb (next ix) n = false) by now apply Pos.ltb_ge.
    assert (Hpointer : snd (insert_step_st (ix, n) c) = Pos.succ (next ix)).
    { unfold insert_step_st. now rewrite Hguard, Hget. }
    assert (Hempty : read_node (fst (insert_step_st (ix, n) c)) (Pos.succ (next ix)) =
      empty_node).
    { unfold insert_step_st. rewrite Hguard, Hget. cbn [fst].
      rewrite read_node_write_other.
      - apply read_node_above_counter; [exact (proj1 (proj2 Hshape)) |].
        apply Pos.lt_succ_diag_r.
      - pose proof (Pos.lt_succ_diag_r (next ix)). lia. }
    exists [], true. split; [constructor |]. split.
    - intro r. cbn [In edge_child].
      rewrite contains_from_empty_node by exact Hempty. intuition discriminate.
    - split.
      + cbn [edge_child]. rewrite Hpointer. split; [intros _; apply reaches_self | reflexivity].
      + reflexivity.
  Qed.

  Lemma pending_insert_step : forall ix n c, shape ix -> pending_insert_counts ix n ->
    (n <= next ix)%positive ->
    pending_insert_counts (fst (insert_step_st (ix, n) c)) (snd (insert_step_st (ix, n) c)).
  Proof.
    intros ix n c Hshape Hcounts Hbound q code out Hout.
    assert (Hguard : Pos.ltb (next ix) n = false) by now apply Pos.ltb_ge.
    pose proof Hout as Hnew.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget.
    - unfold insert_step_st in Hout. rewrite Hguard, Hget in Hout. cbn [fst] in Hout.
      apply stored_edge_put in Hout as [[-> [-> ->]] | [Hdiff Hout]].
      + now apply pending_insert_existing.
      + eapply pending_insert_other; eassumption.
    - unfold insert_step_st in Hout. rewrite Hguard, Hget in Hout. cbn [fst] in Hout.
      apply stored_edge_put in Hout as [[-> [-> ->]] | [Hdiff Hout]].
      + now apply pending_insert_fresh.
      + eapply pending_insert_other; eassumption.
  Qed.

  Lemma pending_insert_walk : forall r st, shape (fst st) ->
    pending_insert_counts (fst st) (snd st) -> (snd st <= next (fst st))%positive ->
    pending_insert_counts (fst (fold_left insert_step_st r st))
      (snd (fold_left insert_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros [ix n] Hshape Hcounts Hbound;
      cbn [fold_left]; [exact Hcounts |].
    apply IH.
    - apply shape_insert_step. exact Hshape.
    - apply pending_insert_step; assumption.
    - pose proof (shape_insert_step (ix, n) c Hshape) as Hshape'.
      exact (proj2 (child_forward _ n c _ (proj1 Hshape')
        (insert_step_child ix n c (proj1 (proj2 Hshape)) Hbound))).
  Qed.

  Lemma counted_edges_insert : forall ix r, shape ix -> counted_edges ix ->
    counted_edges (insert r ix).
  Proof.
    intros ix r Hshape Hcounts. unfold insert, insert_finish.
    destruct (contains r ix) eqn:Hpresent; [exact Hcounts |].
    set (st := fold_left insert_step_st r (start ix)).
    assert (Hshape' : shape (fst st)) by (apply shape_insert_walk; exact Hshape).
    assert (Hpending : pending_insert_counts (fst st) (snd st)).
    { apply pending_insert_walk; [exact Hshape | | apply Pos.le_1_l].
      now apply pending_insert_start. }
    assert (Hpath : seek (fst st) 1%positive r = Some (snd st)).
    { exact (insert_walk_path r (start ix) [] Hshape eq_refl). }
    pose proof (insert_walk_membership r (start ix) r 1%positive Hshape
      (Pos.le_1_l (next ix))) as Hmembers.
    change (contains_from 1%positive r (fst st) = contains_from 1%positive r ix) in Hmembers.
    change (contains_from 1%positive r ix = false) in Hpresent.
    rewrite <- Hmembers in Hpresent. unfold contains_from in Hpresent.
    rewrite Hpath in Hpresent. now apply pending_insert_finish.
  Qed.

  Definition edge_counts_positive (ix : t) : Prop := forall n code edge,
    stored_edge ix n code edge -> (0 < edge_count edge)%N.

  Definition edge_cells_bounded (ix : t) (bound : nat) : Prop := forall n code edge,
    stored_edge ix n code edge -> cell_bits V.encode (edge_cell edge) <= bound.

  Lemma insertion_cursor_bound : forall ix n c, shape ix -> (n <= next ix)%positive ->
    (snd (insert_step_st (ix, n) c) <= next (fst (insert_step_st (ix, n) c)))%positive.
  Proof.
    intros ix n c Hshape Hbound.
    pose proof (shape_insert_step (ix, n) c Hshape) as Hshape'.
    exact (proj2 (child_forward _ n c _ (proj1 Hshape')
      (insert_step_child ix n c (proj1 (proj2 Hshape)) Hbound))).
  Qed.

  Lemma positive_insert_step : forall ix n c, shape ix -> pending_insert_counts ix n ->
    (n <= next ix)%positive -> edge_counts_positive ix ->
    edge_counts_positive (fst (insert_step_st (ix, n) c)).
  Proof.
    intros ix n c Hshape Hcounts Hbound Hpositive q code out Hout.
    assert (Hguard : Pos.ltb (next ix) n = false) by now apply Pos.ltb_ge.
    unfold insert_step_st in Hout. rewrite Hguard in Hout.
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget; cbn [fst] in Hout.
    - apply stored_edge_put in Hout as [[-> [-> ->]] | [_ Hout]].
      + cbn [edge_count]. rewrite bounded_succ_small.
        * lia.
        * apply N.lt_le_incl. eapply pending_current_count_bound; eassumption.
      + exact (Hpositive q code out Hout).
    - apply stored_edge_put in Hout as [[-> [-> ->]] | [_ Hout]].
      + reflexivity.
      + exact (Hpositive q code out Hout).
  Qed.

  Lemma positive_insert_walk : forall r st, shape (fst st) ->
    pending_insert_counts (fst st) (snd st) -> (snd st <= next (fst st))%positive ->
    edge_counts_positive (fst st) -> edge_counts_positive (fst (fold_left insert_step_st r st)).
  Proof.
    induction r as [| c r IH]; intros [ix n] Hshape Hcounts Hbound Hpositive;
      cbn [fold_left]; [exact Hpositive |].
    apply IH.
    - apply shape_insert_step. exact Hshape.
    - apply pending_insert_step; assumption.
    - now apply insertion_cursor_bound.
    - apply positive_insert_step; assumption.
  Qed.

  Lemma positive_mark_terminal : forall ix cursor present bits, edge_counts_positive ix ->
    edge_counts_positive (mark_terminal ix cursor present bits).
  Proof.
    intros ix cursor present bits Hpositive n code edge Hget.
    unfold stored_edge in Hget. rewrite mark_node_edges in Hget. now apply Hpositive in Hget.
  Qed.

  Lemma positive_insert : forall ix r, shape ix -> counted_edges ix ->
    edge_counts_positive ix -> edge_counts_positive (insert r ix).
  Proof.
    intros ix r Hshape Hcounts Hpositive. unfold insert, insert_finish.
    destruct (contains r ix); [exact Hpositive |].
    apply positive_mark_terminal, positive_insert_walk;
      [exact Hshape | | apply Pos.le_1_l | exact Hpositive].
    now apply pending_insert_start.
  Qed.

  Lemma cells_insert_step : forall st c bound, edge_cells_bounded (fst st) bound ->
    cell_bits V.encode c <= bound -> edge_cells_bounded (fst (insert_step_st st c)) bound.
  Proof.
    intros [ix n] c bound Hcells Hcell q code out Hout.
    unfold insert_step_st in Hout. destruct (Pos.ltb (next ix) n).
    - exact (Hcells q code out Hout).
    - destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
        cbn [fst] in Hout;
        apply stored_edge_put in Hout as [[-> [-> ->]] | [_ Hout]].
      + exact Hcell.
      + exact (Hcells q code out Hout).
      + exact Hcell.
      + exact (Hcells q code out Hout).
  Qed.

  Lemma cells_insert_walk : forall r st bound, edge_cells_bounded (fst st) bound ->
    Forall (fun c => cell_bits V.encode c <= bound) r ->
    edge_cells_bounded (fst (fold_left insert_step_st r st)) bound.
  Proof.
    induction r as [| c r IH]; intros st bound Hcells Hbounds;
      cbn [fold_left]; [exact Hcells |].
    inversion Hbounds as [| head tail Hhead Htail]; subst.
    apply IH; [now apply cells_insert_step | exact Htail].
  Qed.

  Lemma cells_mark_terminal : forall ix cursor present bits bound,
    edge_cells_bounded ix bound -> edge_cells_bounded (mark_terminal ix cursor present bits) bound.
  Proof.
    intros ix cursor present bits bound Hcells n code edge Hget.
    unfold stored_edge in Hget. rewrite mark_node_edges in Hget. now apply Hcells in Hget.
  Qed.

  Lemma stored_cell_width_insert : forall ix r, edge_cells_bounded ix (index_cell_width ix) ->
    edge_cells_bounded (insert r ix) (index_cell_width (insert r ix)).
  Proof.
    intros ix r Hcells. unfold insert, insert_finish.
    destruct (contains r ix); [exact Hcells |].
    set (st := fold_left insert_step_st r (start ix)).
    set (bound := Nat.max (index_cell_width ix) (tuple_bits r)).
    change (edge_cells_bounded (mark_terminal (fst st) (snd st) true bound) bound).
    apply cells_mark_terminal. unfold st. apply cells_insert_walk.
    - intros n code edge Hget. unfold bound.
      eapply Nat.le_trans; [exact (Hcells n code edge Hget) | apply Nat.le_max_l].
    - apply Forall_forall. intros c Hin. unfold bound.
      eapply Nat.le_trans; [exact (tuple_bits_member r c Hin) | apply Nat.le_max_r].
  Qed.

  Lemma edges_ok_insert : forall ix r, valid ix -> edges_ok (insert r ix).
  Proof.
    intros ix r Hvalid. pose proof (valid_shape ix Hvalid) as Hshape.
    destruct Hvalid as [Hedges [_ [_ [_ [_ Hcounts]]]]].
    assert (Hpositive : edge_counts_positive ix).
    { intros n code edge Hget. exact (proj1 (proj2 (proj2 (proj2 (Hedges n code edge Hget))))). }
    assert (Hcells : edge_cells_bounded ix (index_cell_width ix)).
    { intros n code edge Hget. exact (proj1 (proj2 (proj2 (Hedges n code edge Hget)))). }
    pose proof (shape_insert ix r Hshape) as Hshape'.
    pose proof (counted_edges_insert ix r Hshape Hcounts) as Hcounts'.
    pose proof (positive_insert ix r Hshape Hcounts Hpositive) as Hpositive'.
    pose proof (stored_cell_width_insert ix r Hcells) as Hcells'.
    intros n code edge Hget. destruct ((proj1 Hshape') n code edge Hget) as [Hcode Hbounds].
    split; [exact Hcode |]. split; [exact Hbounds |]. split; [now apply Hcells' in Hget |].
    split; [now apply Hpositive' in Hget |]. eapply counted_edges_upper; eassumption.
  Qed.

  Lemma valid_insert : forall ix r, valid ix -> valid (insert r ix).
  Proof.
    intros ix r Hvalid. pose proof Hvalid as Hfields.
    destruct Hfields as [_ [Hdegrees [_ [_ [_ Hcounts]]]]].
    pose proof (valid_shape ix Hvalid) as Hshape.
    pose proof (shape_insert ix r Hshape) as Hshape'.
    split; [now apply edges_ok_insert |]. split; [now apply degrees_ok_insert |].
    split; [exact (proj1 (proj2 Hshape')) |]. split; [now apply shape_paths_unique |].
    split; [exact (proj2 (proj2 Hshape')) |]. now apply counted_edges_insert.
  Qed.

  Lemma wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  Proof.
    intros a r ix [Hvalid Harity] Hlength. split; [now apply valid_insert |].
    intros u Hmember. apply (insert_membership ix r u (valid_shape ix Hvalid)) in Hmember.
    destruct Hmember as [-> | Hmember]; [exact Hlength | now apply Harity].
  Qed.

  Lemma nodup_without : forall (A : Type) (xs : list A) x, NoDup xs -> In x xs ->
    exists ys, NoDup ys /\ (forall y, In y ys <-> In y xs /\ y <> x) /\
      length xs = S (length ys).
  Proof.
    intros A xs x Hnodup Hin. apply in_split in Hin as [pre [suf ->]].
    destruct (NoDup_remove pre suf x Hnodup) as [Hremaining Habsent].
    exists (pre ++ suf). split; [exact Hremaining |]. split.
    - intro y. rewrite !in_app_iff. cbn [In]. split.
      + intro Hmember. split; [tauto |]. intro Heq. subst y.
        apply Habsent. now apply in_or_app.
      + intros [Hmember Hneq]. intuition congruence.
    - rewrite !length_app. cbn [length]. lia.
  Qed.

  (** A pending deletion has already been subtracted from each ancestor's cached count. *)
  Definition pending_remove_edge (ix : t) (cursor : positive)
      (edge : index_edge (cell V.t)) : Prop :=
    exists suffixes pending, NoDup suffixes /\
      (forall r, In r suffixes <-> contains_from (edge_child edge) r ix = true) /\
      (pending = true <-> reaches ix (edge_child edge) cursor) /\
      N.of_nat (length suffixes) = (edge_count edge + if pending then 1 else 0)%N.

  Definition pending_remove_counts (ix : t) (cursor : positive) : Prop :=
    forall n code edge, stored_edge ix n code edge -> pending_remove_edge ix cursor edge.

  Lemma pending_remove_start : forall ix, shape ix -> counted_edges ix ->
    pending_remove_counts ix (root ix).
  Proof.
    intros ix Hshape Hcounts n code edge Hget.
    destruct (Hcounts n code edge Hget) as [suffixes [Hnodup [Hmembers Hcount]]].
    exists suffixes, false. split; [exact Hnodup |]. split; [exact Hmembers |]. split.
    - split; [discriminate |]. intro Hreach. exfalso.
      eapply reaches_no_backward; [exact (proj1 Hshape) | | exact Hreach].
      destruct ((proj1 Hshape) n code edge Hget) as [_ [Hforward _]].
      change (1 < edge_child edge)%positive. lia.
    - cbn. rewrite N.add_0_r. symmetry. exact Hcount.
  Qed.

  Lemma pending_remove_finish : forall ix cursor bits, shape ix ->
    pending_remove_counts ix cursor -> node_terminal (read_node ix cursor) = true ->
    counted_edges (mark_terminal ix cursor false bits).
  Proof.
    intros ix cursor bits Hshape Hcounts Hpresent n code edge Hget.
    unfold stored_edge in Hget. rewrite mark_node_edges in Hget.
    destruct (Hcounts n code edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    destruct pending.
    - destruct (proj1 Hpending eq_refl) as [path Hpath].
      assert (Hin : In path suffixes).
      { apply Hmembers. unfold contains_from. now rewrite Hpath. }
      destruct (nodup_without _ suffixes path Hnodup Hin)
        as [remaining [Hremaining [Hremaining_mem Hlength]]].
      exists remaining. split; [exact Hremaining |]. split.
      + intro r. rewrite Hremaining_mem, Hmembers, mark_terminal_delete. split.
        * intros [Hmember Hneq]. split; [| exact Hmember].
          intro Hseek. apply Hneq. eapply seek_paths_unique; eassumption.
        * intros [Hmissing Hmember]. split; [exact Hmember |].
          intro Heq. subst r. contradiction.
      + cbn in Hcount. rewrite Hlength, Nat2N.inj_succ in Hcount. lia.
    - exists suffixes. split; [exact Hnodup |]. split.
      + intro r. rewrite mark_terminal_delete, Hmembers. split.
        * intro Hmember. split; [| exact Hmember]. intro Hseek.
          assert (Hbad : false = true) by (apply Hpending; now exists r). discriminate.
        * tauto.
      + cbn in Hcount. rewrite N.add_0_r in Hcount. symmetry. exact Hcount.
  Qed.

  Lemma pending_remove_current : forall ix n code edge, shape ix ->
    pending_remove_counts ix n -> stored_edge ix n code edge ->
    exists suffixes, NoDup suffixes /\
      (forall r, In r suffixes <-> contains_from (edge_child edge) r ix = true) /\
      N.of_nat (length suffixes) = edge_count edge.
  Proof.
    intros ix n code edge Hshape Hcounts Hget.
    destruct ((proj1 Hshape) n code edge Hget) as [_ [Hforward _]].
    destruct (Hcounts n code edge Hget)
      as [suffixes [pending [Hnodup [Hmembers [Hpending Hcount]]]]].
    destruct pending.
    - exfalso. eapply reaches_no_backward;
        [exact (proj1 Hshape) | exact Hforward | now apply Hpending].
    - exists suffixes. split; [exact Hnodup |]. split; [exact Hmembers |].
      cbn in Hcount. now rewrite N.add_0_r in Hcount.
  Qed.

  Lemma pending_remove_singleton : forall ix n code edge, shape ix ->
    pending_remove_counts ix n -> stored_edge ix n code edge -> edge_count edge = 1%N ->
    exists suffix, forall r, contains_from (edge_child edge) r ix = true <-> r = suffix.
  Proof.
    intros ix n code edge Hshape Hcounts Hget Hone.
    destruct (pending_remove_current ix n code edge Hshape Hcounts Hget)
      as [suffixes [_ [Hmembers Hcount]]].
    assert (Hlength : length suffixes = 1).
    { apply Nat2N.inj. rewrite Hcount. exact Hone. }
    destruct suffixes as [| suffix suffixes]; [discriminate |].
    destruct suffixes as [| second suffixes]; [| discriminate].
    exists suffix. intro r. rewrite <- Hmembers. cbn [In]. intuition congruence.
  Qed.

  Lemma seek_endpoint_children : forall ix ix' target, edge_shape ix ->
    (forall q c, q <> target -> child ix' q c = child ix q c) ->
    forall r q, seek ix q r = Some target -> seek ix' q r = Some target.
  Proof.
    intros ix ix' target Hshape Hchildren r. induction r as [| c r IH]; intros q Hseek.
    - exact Hseek.
    - cbn [seek] in *. destruct (child ix q c) as [m |] eqn:Hchild; [| discriminate].
      assert (Hneq : q <> target).
      { intro Heq. subst q.
        pose proof (proj1 (child_forward ix target c m Hshape Hchild)) as Hlt.
        pose proof (seek_forward ix r m target Hshape Hseek) as Hle.
        apply Pos.lt_nle in Hlt. contradiction. }
      rewrite Hchildren by exact Hneq. rewrite Hchild. now apply IH.
  Qed.

  Lemma reaches_incoming : forall ix source target, source <> target ->
    reaches ix source target -> exists n c, child ix n c = Some target.
  Proof.
    intros ix source target Hneq [path Hseek].
    destruct (rev path) as [| c rest] eqn:Hrev.
    - apply (f_equal (@rev (cell V.t))) in Hrev.
      rewrite rev_involutive in Hrev. cbn [rev] in Hrev. subst path.
      cbn [seek] in Hseek. injection Hseek as Heq. contradiction.
    - assert (Hpath : path = rev rest ++ [c]).
      { rewrite <- (rev_involutive path), Hrev. reflexivity. }
      rewrite Hpath, seek_append in Hseek.
      destruct (seek ix source (rev rest)) as [n |]; [| discriminate].
      cbn [seek] in Hseek. destruct (child ix n c) as [m |] eqn:Hchild; [| discriminate].
      injection Hseek as ->. now exists n, c.
  Qed.

  Lemma deleted_arc_unreachable : forall ix ix' n c m source, parents_unique ix ->
    refines ix ix' -> child ix n c = Some m -> child ix' n c = None -> source <> m ->
    ~ reaches ix' source m.
  Proof.
    intros ix ix' n c m source Hparents [Hedges _] Hchild Hmissing Hneq Hreach.
    destruct (reaches_incoming ix' source m Hneq Hreach) as [q [d Hedge]].
    pose proof (Hedges q d m Hedge) as Hold.
    destruct (child_parents_unique ix q d n c m Hparents Hold Hchild) as [-> ->].
    congruence.
  Qed.

  Lemma deletion_outside_ancestors : forall ix ix' n c m source, refines ix ix' ->
    child ix n c = Some m ->
    (forall q d, q <> n \/ encode_cell d <> encode_cell c -> child ix' q d = child ix q d) ->
    (forall q, node_terminal (read_node ix' q) = node_terminal (read_node ix q)) ->
    ~ reaches ix source n -> forall r,
    (contains_from source r ix' = true <-> contains_from source r ix = true).
  Proof.
    intros ix ix' n c m source Hrefines Hchild Hother Hterminal Houtside r. split.
    - now apply contains_from_refinement.
    - intro Hmember. destruct (contains_from source r ix') eqn:Hnew; [reflexivity |].
      exfalso. destruct (edge_deletion_loss ix ix' n c m Hchild Hother Hterminal
        r source Hmember Hnew) as [pre [suf [_ [Hpath _]]]].
      apply Houtside. now exists pre.
  Qed.

  (** Unlinking a singleton subtree deletes one known suffix from each ancestor. *)
  Lemma deleting_singleton_membership : forall ix ix' n c m source path live,
    shape ix -> refines ix ix' -> child ix n c = Some m -> child ix' n c = None ->
    (forall q d, q <> n \/ encode_cell d <> encode_cell c -> child ix' q d = child ix q d) ->
    (forall q, node_terminal (read_node ix' q) = node_terminal (read_node ix q)) ->
    seek ix source path = Some n ->
    (forall r, contains_from m r ix = true <-> r = live) -> forall u,
    (contains_from source u ix' = true <->
      u <> path ++ c :: live /\ contains_from source u ix = true).
  Proof.
    intros ix ix' n c m source path live Hshape Hrefines Hchild Hmissing Hother Hterminal
      Hpath Hsingle u.
    assert (Hpath' : seek ix' source path = Some n).
    { eapply seek_endpoint_children; [exact (proj1 Hshape) | | exact Hpath].
      intros q d Hneq. apply Hother. now left. }
    assert (Habsent : contains_from source (path ++ c :: live) ix' = false).
    { unfold contains_from. rewrite seek_append, Hpath'. cbn [seek]. now rewrite Hmissing. }
    split.
    - intro Hmember. split.
      + intro Heq. subst u. congruence.
      + eapply contains_from_refinement; eassumption.
    - intros [Hneq Hmember]. destruct (contains_from source u ix') eqn:Hnew; [reflexivity |].
      exfalso. destruct (edge_deletion_loss ix ix' n c m Hchild Hother Hterminal
        u source Hmember Hnew) as [pre [suf [Htuple [Hprefix Hsuffix]]]].
      pose proof (seek_paths_unique ix source pre path n Hshape Hprefix Hpath) as Hpre.
      apply Hsingle in Hsuffix. subst pre suf. contradiction.
  Qed.

End Index.

Module IndexT (V : VALUE_T) <: INDEX_ALL V.
  Include Index V.
  TimeFun empty_node.
  TimeFun empty.
  TimeFun next.
  TimeFun root.
  TimeFun encode_cell.
  TimeFun read_node.
  TimeFun child.
  TimeFun children.
  TimeFun degree.
  TimeFun seek.
  TimeFun contains_from.
  TimeFun contains.
  TimeFun tuple_bits.
  TimeFun bounded_succ.
  TimeFun write_node.
  TimeFun start.
  TimeFun insert_step_st.
  TimeFun insert_step.
  TimeFun remove_step_st.
  TimeFun mark_terminal.
  TimeFun insert_finish.
  TimeFun remove_finish.
  TimeFun insert.
  TimeFun remove.
  Definition max_cell_bits (ix : t) : nat := index_cell_width ix.
  Definition width (ix : t) (r : list (cell V.t)) : nat :=
    Pos.size_nat (next ix + Pos.of_nat (length r)) + tuple_bits r + max_cell_bits ix.
  (** Empty indexes have no encoded cells. *)
  Lemma max_cell_bits_empty : max_cell_bits empty = 0.
  Proof.
    reflexivity.
  Qed.

  (** Insertion adds at most the encoded width of its tuple. *)
  Lemma max_cell_bits_insert : forall r ix,
    max_cell_bits (insert r ix) <=
      Nat.max (max_cell_bits ix)
        (fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r).
  Proof.
    intros r ix. unfold insert, insert_finish, max_cell_bits.
    destruct (contains r ix); cbn [mark_terminal index_cell_width].
    - apply Nat.le_max_l.
    - apply Nat.le_refl.
  Qed.

  (** Removal never increases the stored cell width. *)
  Lemma max_cell_bits_remove : forall r ix,
    max_cell_bits (remove r ix) <= max_cell_bits ix.
  Proof.
    intros r ix. unfold remove, remove_finish, max_cell_bits.
    destruct (contains r ix); cbn [mark_terminal index_cell_width]; apply Nat.le_refl.
  Qed.

  (** Every stored cell fits the recorded cell width. *)
  Lemma max_cell_bits_mem : forall a ix u c, wf a ix -> mem ix u -> In c u ->
    cell_bits V.encode c <= max_cell_bits ix.
  Proof.
    intros a ix u c [Hvalid _] Hmem Hin.
    unfold mem, contains, contains_from in Hmem.
    destruct (seek ix (root ix) u) as [n |] eqn:Hseek; [| discriminate].
    eapply seek_cell_bound; eassumption.
  Qed.

  Lemma width_le : forall ix r,
    width ix r <= Pos.size_nat (next ix + Pos.of_nat (length r)) +
      fold_right (fun c n => Nat.max (cell_bits V.encode c) n) 0 r + max_cell_bits ix.
  Proof.
    intros ix r. apply Nat.le_refl.
  Qed.

  Definition c_ix : N := (1024 * (PTrieT.c_trie + V.c_key + 1))%N.
  (** The fresh node counter is stored. *)
  Lemma T_next_le : forall ix, (T_next ix <= c_ix)%N.
  Proof.
    intros ix. time_step next; unfold c_ix; lia.
  Qed.

  (** The empty index is a constant. *)
  Lemma T_empty_le : (T_empty <= c_ix)%N.
  Proof.
    time_step empty; unfold c_ix; lia.
  Qed.

  (** The root is stored. *)
  Lemma T_root_le : forall ix, (T_root ix <= c_ix)%N.
  Proof.
    intros ix. time_step root; unfold c_ix; lia.
  Qed.

  Lemma T_insert_le : forall a r ix, wf a ix ->
    (T_insert r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_remove_le : forall a r ix, wf a ix ->
    (T_remove r ix <= c_ix * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Every permitted node fits the counter component of the original walk width. *)
  Lemma node_bits_width : forall ix r n, (n <= next ix)%positive ->
    Pos.size_nat n <= width ix r.
  Proof.
    intros ix r n Hnode. unfold width.
    assert (Hbits : Pos.size_nat n <=
      Pos.size_nat (next ix + Pos.of_nat (length r))).
    { apply Pos.size_nat_monotone. lia. }
    lia.
  Qed.

  (** The one-cell width includes the exact encoding presented to an edge lookup. *)
  Lemma cell_bits_width : forall ix c, cell_bits V.encode c <= width ix [c].
  Proof.
    intros ix c. unfold width, tuple_bits. cbn [fold_right].
    pose proof (Nat.le_max_l (cell_bits V.encode c) 0). lia.
  Qed.

  (** The range guard compares the stored counter first, so arbitrary query names are cheap. *)
  Lemma T_node_guard_le : forall ix n,
    (T_next ix + Pos.T_ltb (next ix) n <= N.of_nat (Pos.size_nat (next ix)) + 4)%N.
  Proof.
    intros ix n. pose proof (Pos.T_compare_le (next ix) n) as Hcompare.
    time_unfold T_next. time_unfold @T_index_counter. time_unfold Pos.T_ltb.
    time_cbn. lia.
  Qed.

  (** A node read pays for one trie lookup and two fixed calls. *)
  Lemma T_read_node_le : forall ix n,
    (T_read_node ix n <= PTrieT.c_trie * N.of_nat (Pos.size_nat n + 1) + 2)%N.
  Proof.
    intros ix n. pose proof (PTrieT.T_get_le _ n (index_nodes ix)) as Hget.
    time_unfold T_read_node. time_unfold @T_index_nodes. time_cbn. lia.
  Qed.

  (** Encoding a cell adds one constructor case to the value encoding charge. *)
  Lemma T_encode_cell_le : forall c,
    (T_encode_cell c <= (V.c_key + 1) * N.of_nat (cell_bits V.encode c + 1))%N.
  Proof.
    intros [i | v].
    - time_unfold T_encode_cell. cbn [cell_bits Pos.size_nat]. nia.
    - pose proof (V.T_encode_le v) as Hencode.
      time_unfold T_encode_cell. cbn [cell_bits Pos.size_nat].
      unfold V.bits in Hencode. nia.
  Qed.

  (** A fixed navigation charge fits the shared coefficient after normalizing its widths. *)
  Lemma navigation_budget : forall trie_cost key_cost bits,
    (1 <= bits ->
      bits + 16 + 2 * trie_cost * bits + (key_cost + 1) * bits <=
      1024 * (trie_cost + key_cost + 1) * bits)%N.
  Proof.
    intros trie_cost key_cost bits Hbits.
    replace (bits + 16 + 2 * trie_cost * bits + (key_cost + 1) * bits)%N
      with (16 + 2 * bits + 2 * (trie_cost * bits) + key_cost * bits)%N by ring.
    replace (1024 * (trie_cost + key_cost + 1) * bits)%N
      with (1024 * bits + 1024 * (trie_cost * bits) +
        1024 * (key_cost * bits))%N by ring.
    lia.
  Qed.

  Lemma T_child_le : forall ix n c,
    (T_child ix n c <= c_ix * N.of_nat (width ix [c] + 1))%N.
  Proof.
    intros ix n c.
    pose proof (T_node_guard_le ix n) as Hguard.
    pose proof (node_bits_width ix [c] (next ix) (Pos.le_refl _)) as Hcounter.
    set (bits := N.of_nat (width ix [c] + 1)).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hguard' : (T_next ix + Pos.T_ltb (next ix) n <= bits + 4)%N)
      by (unfold bits; lia).
    pose proof (navigation_budget PTrieT.c_trie V.c_key bits Hbits) as Hbudget.
    unfold c_ix. fold bits. time_unfold T_child.
    destruct (Pos.ltb (next ix) n) eqn:Hrange.
    - clear Hguard Hcounter. clearbody bits.
      time_cbn. set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost. lia.
    - apply Pos.ltb_ge in Hrange.
      pose proof (node_bits_width ix [c] n Hrange) as Hnode.
      pose proof (cell_bits_width ix c) as Hcell.
      pose proof (T_read_node_le ix n) as Hread.
      pose proof (T_encode_cell_le c) as Hencode.
      pose proof (PTrieT.T_get_le _ (encode_cell c)
        (node_edges (read_node ix n))) as Hget.
      assert (Hcode : Pos.size_nat (encode_cell c) = cell_bits V.encode c)
        by (destruct c; reflexivity).
      rewrite Hcode in Hget.
      assert (Hread' : (T_read_node ix n <= PTrieT.c_trie * bits + 2)%N).
      { eapply N.le_trans; [exact Hread|].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      assert (Hencode' : (T_encode_cell c <= (V.c_key + 1) * bits)%N).
      { eapply N.le_trans; [exact Hencode|].
        apply N.mul_le_mono_l. unfold bits. lia. }
      assert (Hget' : (PTrieT.T_get (encode_cell c)
        (node_edges (read_node ix n)) <= PTrieT.c_trie * bits)%N).
      { eapply N.le_trans; [exact Hget|].
        apply N.mul_le_mono_l. unfold bits. lia. }
      clear Hguard Hcounter Hnode Hcell Hread Hencode Hget Hcode.
      clearbody bits.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost.
      destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
        time_unfold @T_node_edges; try time_unfold @T_edge_child; time_cbn; lia.
  Qed.

  (** Every enumerated edge pays at most the recorded cell width and its binding unit. *)
  Lemma edge_weight_le : forall ix n, valid ix ->
    PTrieT.weight (node_edges (read_node ix n)) <=
      length (PTrieCode.elements (node_edges (read_node ix n))) * (max_cell_bits ix + 1).
  Proof.
    intros ix n [Hedges _].
    assert (Hbounds : Forall
      (fun entry : positive * index_edge (cell V.t) =>
        Pos.size_nat (fst entry) + 1 <= max_cell_bits ix + 1)
      (PTrieCode.elements (node_edges (read_node ix n)))).
    { apply Forall_forall. intros [code edge] Hin.
      apply PTrie.elements_spec in Hin.
      destruct (Hedges n code edge Hin) as [Hcode [_ [Hbits _]]].
      cbn [fst]. rewrite <- Hcode.
      assert (Hencode : Pos.size_nat (encode_cell (edge_cell edge)) =
        cell_bits V.encode (edge_cell edge)) by (destruct (edge_cell edge); reflexivity).
      rewrite Hencode. unfold max_cell_bits. lia. }
    unfold PTrieT.weight.
    induction Hbounds as [|entry entries Hhead Htail IH]; cbn [map fold_right length Nat.mul].
    - reflexivity.
    - apply Nat.add_le_mono; assumption.
  Qed.

  (** Enumeration charges are linear in the edge count and the shared width budget. *)
  Lemma children_budget : forall trie_cost key_cost amount bits,
    (1 <= amount -> 1 <= bits ->
      bits + 8 + trie_cost * bits + trie_cost * amount * bits + 4 * amount <=
      1024 * (trie_cost + key_cost + 1) * amount * bits)%N.
  Proof.
    intros trie_cost key_cost amount bits Hamount Hbits.
    assert (Hwidth : (bits <= amount * bits)%N).
    { replace bits with (1 * bits)%N at 1 by ring.
      apply N.mul_le_mono_r. exact Hamount. }
    assert (Hcount : (amount <= amount * bits)%N).
    { replace amount with (amount * 1)%N at 1 by ring.
      apply N.mul_le_mono_l. exact Hbits. }
    assert (Htrie : (trie_cost * bits <= trie_cost * (amount * bits))%N).
    { apply N.mul_le_mono_l. exact Hwidth. }
    replace (trie_cost * amount * bits)%N with (trie_cost * (amount * bits))%N by ring.
    replace (1024 * (trie_cost + key_cost + 1) * amount * bits)%N
      with (1024 * (amount * bits) + 1024 * (trie_cost * (amount * bits)) +
        1024 * (key_cost * (amount * bits)))%N by ring.
    lia.
  Qed.

  Lemma T_children_le : forall a ix n, wf a ix ->
    (T_children ix n <= c_ix * N.of_nat (N.to_nat (degree ix n) + 1) *
      N.of_nat (width ix [] + 1))%N.
  Proof.
    intros a ix n [Hvalid Harity].
    pose proof (T_node_guard_le ix n) as Hguard.
    pose proof (node_bits_width ix [] (next ix) (Pos.le_refl _)) as Hcounter.
    set (bits := N.of_nat (width ix [] + 1)).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hguard' : (T_next ix + Pos.T_ltb (next ix) n <= bits + 4)%N)
      by (unfold bits; lia).
    unfold c_ix, degree. fold bits. time_unfold T_children.
    destruct (Pos.ltb (next ix) n) eqn:Hrange.
    - pose proof (navigation_budget PTrieT.c_trie V.c_key bits Hbits) as Hbudget.
      clear Hguard Hcounter Hvalid Harity. clearbody bits.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost.
      time_cbn. lia.
    - pose proof (edge_weight_le ix n Hvalid) as Hweight.
      destruct Hvalid as [_ [Hdegrees _]].
      pose proof (proj1 (Hdegrees n)) as Hdegree. rewrite Hdegree.
      apply Pos.ltb_ge in Hrange.
      pose proof (node_bits_width ix [] n Hrange) as Hnode.
      pose proof (T_read_node_le ix n) as Hread.
      assert (Hread' : (T_read_node ix n <= PTrieT.c_trie * bits + 2)%N).
      { eapply N.le_trans; [exact Hread|].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      set (entries := PTrieCode.elements (node_edges (read_node ix n))) in *.
      set (amount := N.of_nat (length entries + 1)). fold amount.
      assert (Hamount : (1 <= amount)%N) by (unfold amount; lia).
      assert (Hwidth : max_cell_bits ix + 1 <= width ix [] + 1)
        by (unfold width; lia).
      assert (Hmass : PTrieT.weight (node_edges (read_node ix n)) + 1 <=
        (length entries + 1) * (width ix [] + 1)).
      { assert (Hmul : length entries * (max_cell_bits ix + 1) <=
          length entries * (width ix [] + 1)) by (apply Nat.mul_le_mono_l; exact Hwidth).
        rewrite Nat.mul_add_distr_r. cbn [Nat.mul]. lia. }
      assert (HmassN : (N.of_nat (PTrieT.weight (node_edges (read_node ix n)) + 1) <=
        N.of_nat ((length entries + 1) * (width ix [] + 1)))%N).
      { clear - Hmass. lia. }
      rewrite Nat2N.inj_mul in HmassN. fold amount bits in HmassN.
      pose proof (PTrieT.T_elements_le _ (node_edges (read_node ix n))) as Helements.
      assert (Helements' : (PTrieT.T_elements (node_edges (read_node ix n)) <=
        PTrieT.c_trie * amount * bits)%N).
      { eapply N.le_trans; [exact Helements|].
        rewrite <- N.mul_assoc. apply N.mul_le_mono_l. exact HmassN. }
      assert (Hcallback : forall entry : positive * index_edge (cell V.t),
        (1 + (Datatypes.T_snd entry + T_edge_cell (snd entry)) <= 3)%N).
      { intro entry. time_unfold @Datatypes.T_snd. time_unfold @T_edge_cell. time_cbn. lia. }
      pose proof (Argent.Std.ListDef.T_map_le
        (fun entry : positive * index_edge (cell V.t) => edge_cell (snd entry))
        (fun entry => (1 + (Datatypes.T_snd entry + T_edge_cell (snd entry)))%N)
        3%N entries Hcallback) as Hmap.
      assert (Hmap' : (Argent.Std.ListDef.T_map
        (fun entry : positive * index_edge (cell V.t) => edge_cell (snd entry))
        (fun entry => (1 + (Datatypes.T_snd entry + T_edge_cell (snd entry)))%N)
        entries <= 4 * amount)%N) by (unfold amount; lia).
      pose proof (children_budget PTrieT.c_trie V.c_key amount bits Hamount Hbits) as Hbudget.
      clear Hguard Hcounter Hdegrees Hdegree Harity Hnode Hread Hweight Hwidth Hmass HmassN
        Helements Hcallback Hmap.
      clearbody bits amount entries.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost.
      time_unfold @T_node_edges. time_cbn. lia.
  Qed.

  Lemma T_degree_le : forall ix n,
    (T_degree ix n <= c_ix * N.of_nat (width ix [] + 1))%N.
  Proof.
    intros ix n.
    pose proof (T_node_guard_le ix n) as Hguard.
    pose proof (node_bits_width ix [] (next ix) (Pos.le_refl _)) as Hcounter.
    set (bits := N.of_nat (width ix [] + 1)).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hguard' : (T_next ix + Pos.T_ltb (next ix) n <= bits + 4)%N)
      by (unfold bits; lia).
    pose proof (navigation_budget PTrieT.c_trie V.c_key bits Hbits) as Hbudget.
    unfold c_ix. fold bits. time_unfold T_degree.
    destruct (Pos.ltb (next ix) n) eqn:Hrange.
    - clear Hguard Hcounter. clearbody bits.
      time_cbn. set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost. lia.
    - apply Pos.ltb_ge in Hrange.
      pose proof (node_bits_width ix [] n Hrange) as Hnode.
      pose proof (T_read_node_le ix n) as Hread.
      assert (Hread' : (T_read_node ix n <= PTrieT.c_trie * bits + 2)%N).
      { eapply N.le_trans; [exact Hread|].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      clear Hguard Hcounter Hnode Hread. clearbody bits.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost.
      time_unfold @T_node_degree. time_cbn. lia.
  Qed.

  (** Increasing a positive bound never decreases its binary width. *)
  Lemma positive_bits_mono : forall p q, (p <= q)%positive ->
    Pos.size_nat p <= Pos.size_nat q.
  Proof.
    intros p q Hle. destruct (Pos.eq_dec p q) as [Heq | Hneq].
    - now subst q.
    - apply Pos.size_nat_monotone. lia.
  Qed.

  (** A binary natural below a positive counter fits that counter's bit width. *)
  Lemma N_bits_bounded : forall n limit, (n <= Npos limit)%N ->
    N.size_nat n <= Pos.size_nat limit.
  Proof.
    intros [|n] limit Hle; cbn [N.size_nat]; [lia |].
    apply positive_bits_mono. lia.
  Qed.

  (** Guarding the counter first makes even a malformed stored count cheap to reject. *)
  Lemma T_bounded_succ_le : forall limit n,
    (T_bounded_succ limit n <= 2 * N.of_nat (Pos.size_nat limit) + 5)%N.
  Proof.
    intros limit n. pose proof (N.T_compare_le (Npos limit) n) as Hcompare.
    time_unfold T_bounded_succ. time_unfold N.T_ltb.
    destruct (N.ltb (Npos limit) n) eqn:Hrange.
    - cbn [N.size_nat] in Hcompare. time_cbn. lia.
    - apply N.ltb_ge in Hrange.
      pose proof (N_bits_bounded n limit Hrange) as Hbits.
      pose proof (N.T_succ_le n) as Hsucc.
      cbn [N.size_nat] in Hcompare. time_cbn. lia.
  Qed.

  (** Writing a node charges its trie key and three fixed wrapper calls. *)
  Lemma T_write_node_le : forall ix n nd counter,
    (T_write_node ix n nd counter <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat n + 1) + 3)%N.
  Proof.
    intros ix n nd counter.
    pose proof (PTrieT.T_set_le _ n nd (index_nodes ix)) as Hset.
    time_unfold T_write_node. time_unfold @T_index_nodes. time_unfold @T_index_cell_width.
    time_cbn. lia.
  Qed.

  (** An insertion step eagerly pays the value encoder even when its edge is absent. *)
  Lemma T_insert_step_st_encode_ge : forall ix n v,
    Pos.ltb (next ix) n = false ->
    (V.T_encode v <= T_insert_step_st (ix, n) (Val v))%N.
  Proof.
    intros ix n v Hrange. time_unfold T_insert_step_st. cbn beta iota zeta.
    rewrite Hrange. time_unfold T_encode_cell. time_cbn. lia.
  Qed.

  (** The insertion wrapper retains the eager value-encoding charge. *)
  Lemma T_insert_step_encode_ge : forall ix n v,
    Pos.ltb (next ix) n = false ->
    (V.T_encode v <= T_insert_step ix n (Val v))%N.
  Proof.
    intros ix n v Hrange. pose proof (T_insert_step_st_encode_ge ix n v Hrange) as Hstep.
    time_unfold T_insert_step. time_cbn. lia.
  Qed.

  (** A removal step also pays the encoder before observing that an edge is absent. *)
  Lemma T_remove_step_st_encode_ge : forall ix n v,
    Pos.ltb (next ix) n = false ->
    (V.T_encode v <= T_remove_step_st (ix, n) (Val v))%N.
  Proof.
    intros ix n v Hrange. time_unfold T_remove_step_st. cbn beta iota zeta.
    rewrite Hrange. time_unfold T_encode_cell. time_cbn. lia.
  Qed.

  (** Normalized mutation charges fit a coefficient that includes the value encoder. *)
  Lemma mutation_step_budget : forall trie_cost key_cost bits,
    (1 <= bits ->
      96 + 16 * bits + 4 * trie_cost * bits + (key_cost + 1) * bits <=
      128 * (trie_cost + key_cost + 1) * bits)%N.
  Proof.
    intros trie_cost key_cost bits Hbits.
    replace (96 + 16 * bits + 4 * trie_cost * bits + (key_cost + 1) * bits)%N
      with (96 + 17 * bits + 4 * (trie_cost * bits) + key_cost * bits)%N by ring.
    replace (128 * (trie_cost + key_cost + 1) * bits)%N
      with (128 * bits + 128 * (trie_cost * bits) + 128 * (key_cost * bits))%N by ring.
    lia.
  Qed.

  (** An insertion step has a width bound on every state, including malformed counts. *)
  Lemma T_insert_step_budget : forall st c bound,
    Pos.size_nat (next (fst st)) <= bound -> cell_bits V.encode c <= bound ->
    (T_insert_step_st st c <=
      128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros [ix n] c bound Hcounter Hcell. cbn [fst] in Hcounter.
    set (bits := N.of_nat (bound + 1)).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    pose proof (mutation_step_budget PTrieT.c_trie V.c_key bits Hbits) as Hbudget.
    pose proof (T_node_guard_le ix n) as Hguard.
    assert (Hguard' : (Pos.T_ltb (next ix) n <= bits + 4)%N) by (unfold bits; lia).
    time_unfold T_insert_step_st. cbn beta iota zeta. fold bits.
    destruct (Pos.ltb (next ix) n) eqn:Hrange.
    - time_unfold T_next. time_unfold @T_index_counter. time_cbn.
      clear Hguard Hcounter Hcell. clearbody bits.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost. lia.
    - apply Pos.ltb_ge in Hrange.
      assert (Hnode : Pos.size_nat n <= bound).
      { eapply Nat.le_trans; [apply positive_bits_mono; exact Hrange | exact Hcounter]. }
      assert (Hcode : Pos.size_nat (encode_cell c) = cell_bits V.encode c)
        by (destruct c; reflexivity).
      assert (Hread : (T_read_node ix n <= PTrieT.c_trie * bits + 2)%N).
      { eapply N.le_trans; [apply T_read_node_le |].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      assert (Hencode : (T_encode_cell c <= (V.c_key + 1) * bits)%N).
      { eapply N.le_trans; [apply T_encode_cell_le |].
        apply N.mul_le_mono_l. unfold bits. lia. }
      assert (Hget : (PTrieCode.T_get (encode_cell c)
        (node_edges (read_node ix n)) <= PTrieT.c_trie * bits)%N).
      { eapply N.le_trans; [apply PTrieT.T_get_le |].
        apply N.mul_le_mono_l. rewrite Hcode. unfold bits. lia. }
      assert (Hset : forall edge : index_edge (cell V.t),
        (PTrieCode.T_set (encode_cell c) edge (node_edges (read_node ix n)) <=
          PTrieT.c_trie * bits)%N).
      { intro edge. eapply N.le_trans; [apply PTrieT.T_set_le |].
        apply N.mul_le_mono_l. rewrite Hcode. unfold bits. lia. }
      assert (Hwrite : forall nd counter,
        (T_write_node ix n nd counter <= PTrieT.c_trie * bits + 3)%N).
      { intros nd counter. eapply N.le_trans; [apply T_write_node_le |].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      assert (Hincrement : forall count,
        (T_bounded_succ (next ix) count <= 2 * bits + 5)%N).
      { intro count. eapply N.le_trans; [apply T_bounded_succ_le |]. unfold bits. lia. }
      pose proof (Pos.T_succ_le (next ix)) as Hsucc.
      assert (Hsucc' : (Pos.T_succ (next ix) <= bits)%N) by (unfold bits; lia).
      time_unfold T_next. time_unfold @T_index_counter.
      destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
        time_pose; time_simpl; time_cbn;
        clear Hguard Hcounter Hcell Hnode Hcode Hsucc Hset Hwrite Hincrement;
        clearbody bits;
        set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost; lia.
  Qed.

  (** Removal charges its decrements using the edge and cached-degree bounds. *)
  Lemma T_remove_step_budget : forall st c bound,
    edges_ok (fst st) -> degrees_ok (fst st) ->
    Pos.size_nat (next (fst st)) <= bound -> cell_bits V.encode c <= bound ->
    (T_remove_step_st st c <=
      128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros [ix n] c bound Hedges Hdegrees Hcounter Hcell.
    cbn [fst] in Hedges, Hdegrees, Hcounter.
    set (bits := N.of_nat (bound + 1)).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    pose proof (mutation_step_budget PTrieT.c_trie V.c_key bits Hbits) as Hbudget.
    pose proof (T_node_guard_le ix n) as Hguard.
    assert (Hguard' : (Pos.T_ltb (next ix) n <= bits + 4)%N) by (unfold bits; lia).
    time_unfold T_remove_step_st. cbn beta iota zeta. fold bits.
    destruct (Pos.ltb (next ix) n) eqn:Hrange.
    - time_unfold T_next. time_unfold @T_index_counter. time_cbn.
      clear Hguard Hcounter Hcell Hedges Hdegrees. clearbody bits.
      set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost. lia.
    - apply Pos.ltb_ge in Hrange.
      assert (Hnode : Pos.size_nat n <= bound).
      { eapply Nat.le_trans; [apply positive_bits_mono; exact Hrange | exact Hcounter]. }
      assert (Hcode : Pos.size_nat (encode_cell c) = cell_bits V.encode c)
        by (destruct c; reflexivity).
      assert (Hread : (T_read_node ix n <= PTrieT.c_trie * bits + 2)%N).
      { eapply N.le_trans; [apply T_read_node_le |].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      assert (Hencode : (T_encode_cell c <= (V.c_key + 1) * bits)%N).
      { eapply N.le_trans; [apply T_encode_cell_le |].
        apply N.mul_le_mono_l. unfold bits. lia. }
      assert (Hget : (PTrieCode.T_get (encode_cell c)
        (node_edges (read_node ix n)) <= PTrieT.c_trie * bits)%N).
      { eapply N.le_trans; [apply PTrieT.T_get_le |].
        apply N.mul_le_mono_l. rewrite Hcode. unfold bits. lia. }
      assert (Hset : forall edge : index_edge (cell V.t),
        (PTrieCode.T_set (encode_cell c) edge (node_edges (read_node ix n)) <=
          PTrieT.c_trie * bits)%N).
      { intro edge. eapply N.le_trans; [apply PTrieT.T_set_le |].
        apply N.mul_le_mono_l. rewrite Hcode. unfold bits. lia. }
      assert (Hremove : (PTrieCode.T_remove (encode_cell c) (node_edges (read_node ix n)) <=
        PTrieT.c_trie * bits)%N).
      { eapply N.le_trans; [apply PTrieT.T_remove_le |].
        apply N.mul_le_mono_l. rewrite Hcode. unfold bits. lia. }
      assert (Hwrite : forall nd counter,
        (T_write_node ix n nd counter <= PTrieT.c_trie * bits + 3)%N).
      { intros nd counter. eapply N.le_trans; [apply T_write_node_le |].
        apply N.add_le_mono_r, N.mul_le_mono_l. unfold bits. lia. }
      time_unfold T_next. time_unfold @T_index_counter.
      destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
        as [edge |] eqn:Hlookup.
      + destruct (Hedges n (encode_cell c) edge Hlookup) as [_ [_ [_ [_ Hcount]]]].
        pose proof (proj2 (Hdegrees n)) as Hdegree.
        assert (Hcount_bits : N.size_nat (edge_count edge) <= bound).
        { eapply Nat.le_trans; [apply N_bits_bounded; apply N.lt_le_incl; exact Hcount | exact Hcounter]. }
        assert (Hdegree_bits : N.size_nat (node_degree (read_node ix n)) <= bound).
        { eapply Nat.le_trans; [apply N_bits_bounded; apply N.lt_le_incl; exact Hdegree | exact Hcounter]. }
        pose proof (N.T_eqb_le (edge_count edge) 1%N) as Hcompare.
        pose proof (N.T_pred_le (edge_count edge)) as Hpred_count.
        pose proof (N.T_pred_le (node_degree (read_node ix n))) as Hpred_degree.
        assert (Hcompare' : (N.T_eqb (edge_count edge) 1 <= bits + 1)%N)
          by (unfold bits; lia).
        assert (Hpred_count' : (N.T_pred (edge_count edge) <= bits + 2)%N)
          by (unfold bits; lia).
        assert (Hpred_degree' : (N.T_pred (node_degree (read_node ix n)) <= bits + 2)%N)
          by (unfold bits; lia).
        destruct (N.eqb (edge_count edge) 1%N);
          time_pose; time_simpl; time_cbn;
          clear Hguard Hcounter Hcell Hnode Hcode Hset Hwrite Hedges Hdegrees
            Hcompare Hpred_count Hpred_degree Hcount Hdegree Hcount_bits Hdegree_bits;
          clearbody bits;
          set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost; lia.
      + time_pose. time_simpl. time_cbn.
        clear Hguard Hcounter Hcell Hnode Hcode Hset Hwrite Hedges Hdegrees.
        clearbody bits. set (trie_cost := PTrieT.c_trie) in *; clearbody trie_cost. lia.
  Qed.

  (** An insertion cursor remains within the counter maintained by its current state. *)
  Lemma insert_step_point_bound : forall st c, edge_shape (fst st) ->
    (snd st <= next (fst st))%positive ->
    (snd (insert_step_st st c) <= next (fst (insert_step_st st c)))%positive.
  Proof.
    intros [ix n] c Hshape Hbound. unfold insert_step_st.
    destruct (Pos.ltb (next ix) n); [exact Hbound |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)))
      as [edge |] eqn:Hget.
    - exact (proj2 (proj2 (Hshape n (encode_cell c) edge Hget))).
    - apply Pos.le_refl.
  Qed.

  (** Every insertion prefix retains a bounded cursor. *)
  Lemma insert_walk_point_bound : forall r st, shape (fst st) ->
    (snd st <= next (fst st))%positive ->
    (snd (fold_left insert_step_st r st) <= next (fst (fold_left insert_step_st r st)))%positive.
  Proof.
    induction r as [| c r IH]; intros st Hshape Hbound; cbn [fold_left]; [exact Hbound |].
    apply IH; [now apply shape_insert_step |].
    apply insert_step_point_bound; [exact (proj1 Hshape) | exact Hbound].
  Qed.

  (** The original walk width covers the counter after every shorter insertion prefix. *)
  Lemma insert_prefix_counter_bits : forall ix r pre, length pre <= length r ->
    Pos.size_nat (next (fst (fold_left insert_step_st pre (start ix)))) <= width ix r.
  Proof.
    intros ix r pre Hlength.
    pose proof (insert_walk_counter pre (start ix)) as Hcounter.
    cbn [start fst] in Hcounter.
    assert (Hbits : Pos.size_nat (next (fst (fold_left insert_step_st pre (start ix)))) <=
      Pos.size_nat (next ix + Pos.of_nat (length r))).
    { apply positive_bits_mono, Pos2Nat.inj_le.
      rewrite Pos2Nat.inj_add, Nat2Pos.id_max. lia. }
    unfold width. lia.
  Qed.

  (** Every tuple cell fits the width charged to its complete walk. *)
  Lemma tuple_cell_width : forall ix r c, In c r -> cell_bits V.encode c <= width ix r.
  Proof.
    intros ix r c Hin. pose proof (tuple_bits_member r c Hin). unfold width. lia.
  Qed.

  (** A fold sums uniform bounds needed only at the states its prefixes actually reach. *)
  Lemma T_fold_left_prefix_le : forall A B (f : A -> B -> A) T_f xs acc k,
    (forall pre x suf, xs = pre ++ x :: suf ->
      (T_f (fold_left f pre acc) x <= k)%N) ->
    (List.T_fold_left f T_f xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f xs. induction xs as [|x xs IH]; intros acc k Hprefix.
    - time_unfold List.T_fold_left. time_cbn. lia.
    - pose proof (Hprefix [] x xs eq_refl) as Hhead. cbn [fold_left] in Hhead.
      assert (Htail : forall pre y suf, xs = pre ++ y :: suf ->
        (T_f (fold_left f pre (f acc x)) y <= k)%N).
      { intros pre y suf Heq. specialize (Hprefix (x :: pre) y suf).
        cbn [fold_left app] in Hprefix. apply Hprefix. now rewrite Heq. }
      pose proof (IH (f acc x) k Htail) as Hrest.
      time_unfold List.T_fold_left. time_cbn. nia.
  Qed.

  (** Direct step bounds sum over insertion prefixes without requiring count invariants. *)
  Lemma T_insert_fold_budget : forall ix r,
    (List.T_fold_left insert_step_st T_insert_step_st r (start ix) <=
      (128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (width ix r + 1) + 1) *
        N.of_nat (length r) + 1)%N.
  Proof.
    intros ix r. apply T_fold_left_prefix_le. intros pre c suf Hsplit.
    apply T_insert_step_budget.
    - apply insert_prefix_counter_bits. rewrite Hsplit, length_app. cbn [length]. lia.
    - apply tuple_cell_width. rewrite Hsplit. apply in_or_app. right. now left.
  Qed.

  (** Removal prefixes preserve exactly the counter invariants needed by their clocks. *)
  Lemma T_remove_fold_budget : forall ix r, valid ix ->
    (List.T_fold_left remove_step_st T_remove_step_st r (start ix) <=
      (128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (width ix r + 1) + 1) *
        N.of_nat (length r) + 1)%N.
  Proof.
    intros ix r Hvalid. apply T_fold_left_prefix_le. intros pre c suf Hsplit.
    apply T_remove_step_budget.
    - apply edges_ok_remove_walk. exact (proj1 Hvalid).
    - apply degrees_ok_remove_walk. exact (proj1 (proj2 Hvalid)).
    - rewrite remove_walk_counter. cbn [start fst]. apply node_bits_width, Pos.le_refl.
    - apply tuple_cell_width. rewrite Hsplit. apply in_or_app. right. now left.
  Qed.

  (** A child read performs a prefix of the work done by an insertion step. *)
  Lemma T_child_le_insert_step : forall ix n c,
    (T_child ix n c <= T_insert_step_st (ix, n) c)%N.
  Proof.
    intros ix n c. time_unfold T_child. time_unfold T_insert_step_st.
    cbn beta iota zeta. destruct (Pos.ltb (next ix) n); [apply N.le_refl |].
    destruct (PTrieCode.get (encode_cell c) (node_edges (read_node ix n)));
      time_simpl; time_cbn; lia.
  Qed.

  (** The direct insertion budget also bounds a child read at an arbitrary cursor. *)
  Lemma T_child_budget : forall ix n c bound,
    Pos.size_nat (next ix) <= bound -> cell_bits V.encode c <= bound ->
    (T_child ix n c <=
      128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros ix n c bound Hcounter Hcell.
    eapply N.le_trans; [apply T_child_le_insert_step |].
    apply T_insert_step_budget; assumption.
  Qed.

  (** Seeking a tuple sums bounded child reads and its own recursive calls. *)
  Lemma T_seek_budget : forall ix r n bound,
    Pos.size_nat (next ix) <= bound ->
    (forall c, In c r -> cell_bits V.encode c <= bound) ->
    (T_seek ix n r <=
      (128 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (bound + 1) + 1) *
        N.of_nat (length r) + 1)%N.
  Proof.
    intros ix r. induction r as [|c r IH]; intros n bound Hcounter Hcells.
    - time_unfold T_seek. time_cbn. lia.
    - pose proof (T_child_budget ix n c bound Hcounter (Hcells c (or_introl eq_refl))) as Hchild.
      time_unfold T_seek. cbn beta iota zeta.
      destruct (child ix n c) as [m |] eqn:Hnext.
      + pose proof (IH m bound Hcounter (fun d Hd => Hcells d (or_intror Hd))) as Htail.
        set (step_cost := (128 * (PTrieT.c_trie + V.c_key + 1) *
          N.of_nat (bound + 1))%N) in *; clearbody step_cost.
        time_cbn. nia.
      + set (step_cost := (128 * (PTrieT.c_trie + V.c_key + 1) *
          N.of_nat (bound + 1))%N) in *; clearbody step_cost.
        time_cbn. nia.
  Qed.

  (** A final node read fits beside the charged sequence of child reads. *)
  Lemma contains_budget : forall cost bits amount,
    (1 <= cost -> 1 <= bits ->
      8 + (128 * cost * bits + 1) * amount + cost * bits <=
      160 * cost * (amount + 1) * bits)%N.
  Proof.
    intros cost bits amount Hcost Hbits.
    assert (Hunit : (1 <= cost * bits)%N).
    { replace 1%N with (1 * 1)%N by reflexivity. apply N.mul_le_mono; assumption. }
    assert (Hamount : (amount <= cost * bits * amount)%N).
    { replace amount with (1 * amount)%N at 1 by ring. apply N.mul_le_mono_r. exact Hunit. }
    replace (8 + (128 * cost * bits + 1) * amount + cost * bits)%N
      with (8 + 128 * (cost * bits * amount) + amount + cost * bits)%N by ring.
    replace (160 * cost * (amount + 1) * bits)%N
      with (160 * (cost * bits * amount) + 160 * (cost * bits))%N by ring.
    lia.
  Qed.

  (** Membership checking pays the walk and a bounded terminal-node observation. *)
  Lemma T_contains_budget : forall ix r bound, shape ix ->
    Pos.size_nat (next ix) <= bound ->
    (forall c, In c r -> cell_bits V.encode c <= bound) ->
    (T_contains r ix <= 160 * (PTrieT.c_trie + V.c_key + 1) *
      N.of_nat (length r + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros ix r bound Hshape Hcounter Hcells.
    pose proof (T_seek_budget ix r (root ix) bound Hcounter Hcells) as Hseek.
    set (bits := N.of_nat (bound + 1)) in *.
    set (cost := (PTrieT.c_trie + V.c_key + 1)%N) in *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    pose proof (contains_budget cost bits (N.of_nat (length r)) Hcost Hbits) as Hbudget.
    assert (Hlength : N.of_nat (length r + 1) = (N.of_nat (length r) + 1)%N) by lia.
    rewrite Hlength. time_unfold T_contains. time_unfold T_contains_from. time_unfold T_root.
    destruct (seek ix (root ix) r) as [n |] eqn:Hpath.
    - assert (Hnode : (n <= next ix)%positive).
      { eapply (seek_bounded ix r (root ix) n);
          [exact (proj1 Hshape) | unfold root; lia | exact Hpath]. }
      assert (Hnode_bits : Pos.size_nat n <= bound).
      { eapply Nat.le_trans; [apply positive_bits_mono; exact Hnode | exact Hcounter]. }
      assert (Hread : (T_read_node ix n <= cost * bits + 2)%N).
      { eapply N.le_trans; [apply T_read_node_le |].
        apply N.add_le_mono_r, N.mul_le_mono.
        - unfold cost. lia.
        - unfold bits. lia. }
      clear Hshape Hcounter Hcells Hnode Hnode_bits. clearbody cost bits.
      time_simpl. time_cbn. lia.
    - clear Hshape Hcounter Hcells. clearbody cost bits.
      time_simpl. time_cbn. lia.
  Qed.

  (** Unary maximum examines no more constructors than its first argument contains. *)
  Lemma T_nat_max_le : forall n m, (T_max n m <= N.of_nat n + 1)%N.
  Proof.
    intro n. induction n as [|n IH]; intros [|m]; time_step Nat.max.
  Qed.

  (** Measuring a cell includes its encoder and the resulting positive's bit scan. *)
  Lemma T_cell_bits_le : forall c,
    (T_cell_bits V.encode (fun v => V.T_encode v) c <=
      (V.c_key + 2) * N.of_nat (cell_bits V.encode c + 1))%N.
  Proof.
    intros [i | v].
    - pose proof (Pos.T_size_nat_le (xO i)) as Hsize.
      time_unfold @T_cell_bits. cbn [cell_bits Pos.size_nat] in Hsize |- *. nia.
    - pose proof (V.T_encode_le v) as Hencode.
      pose proof (Pos.T_size_nat_le (xI (V.encode v))) as Hsize.
      unfold V.bits in Hencode.
      time_unfold @T_cell_bits. cbn [cell_bits Pos.size_nat] in Hsize |- *. nia.
  Qed.

  (** A right fold only needs its callback bound at members of the traversed list. *)
  Lemma T_fold_right_members_le : forall A B (f : B -> A -> A) T_f xs acc k,
    (forall x out, In x xs -> (T_f x out <= k)%N) ->
    (List.T_fold_right f T_f acc xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f xs. induction xs as [|x xs IH]; intros acc k Hcost.
    - time_unfold List.T_fold_right. time_cbn. lia.
    - pose proof (Hcost x (fold_right f acc xs) (or_introl eq_refl)) as Hhead.
      pose proof (IH acc k (fun y out Hy => Hcost y out (or_intror Hy))) as Htail.
      time_unfold List.T_fold_right. time_cbn. nia.
  Qed.

  (** The width scan's callback and driver charges fit a linear tuple budget. *)
  Lemma tuple_scan_budget : forall cost bits amount,
    (1 <= cost -> 1 <= bits ->
      2 + (8 * cost * bits + 1) * amount <= 16 * cost * (amount + 1) * bits)%N.
  Proof.
    intros cost bits amount Hcost Hbits.
    assert (Hunit : (1 <= cost * bits)%N).
    { replace 1%N with (1 * 1)%N by reflexivity. apply N.mul_le_mono; assumption. }
    assert (Hamount : (amount <= cost * bits * amount)%N).
    { replace amount with (1 * amount)%N at 1 by ring. apply N.mul_le_mono_r. exact Hunit. }
    replace (2 + (8 * cost * bits + 1) * amount)%N
      with (2 + 8 * (cost * bits * amount) + amount)%N by ring.
    replace (16 * cost * (amount + 1) * bits)%N
      with (16 * (cost * bits * amount) + 16 * (cost * bits))%N by ring.
    lia.
  Qed.

  (** Computing the tuple's maximum width pays for each cell's encoding and comparison. *)
  Lemma T_tuple_bits_budget : forall r bound,
    (forall c, In c r -> cell_bits V.encode c <= bound) ->
    (T_tuple_bits r <= 16 * (PTrieT.c_trie + V.c_key + 1) *
      N.of_nat (length r + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros r bound Hcells.
    set (bits := N.of_nat (bound + 1)) in *.
    set (cost := (PTrieT.c_trie + V.c_key + 1)%N) in *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    assert (Hcallback : forall c n, In c r ->
      (1 + (T_cell_bits V.encode (fun v => V.T_encode v) c + T_max (cell_bits V.encode c) n) <=
        8 * cost * bits)%N).
    { intros c n Hin. pose proof (Hcells c Hin) as Hcell.
      assert (Hmeasure : (T_cell_bits V.encode (fun v => V.T_encode v) c <=
        (V.c_key + 2) * bits)%N).
      { eapply N.le_trans; [apply T_cell_bits_le |].
        apply N.mul_le_mono_l. unfold bits. lia. }
      pose proof (T_nat_max_le (cell_bits V.encode c) n) as Hmax.
      assert (Hmax' : (T_max (cell_bits V.encode c) n <= bits)%N) by (unfold bits; lia).
      assert (Hfactor : ((V.c_key + 4) * bits <= 8 * cost * bits)%N).
      { apply N.mul_le_mono_r. unfold cost. lia. }
      eapply N.le_trans; [|exact Hfactor].
      replace ((V.c_key + 4) * bits)%N with
        ((V.c_key + 2) * bits + bits + bits)%N by ring. lia. }
    assert (Hfold : (List.T_fold_right
      (fun c n => Nat.max (cell_bits V.encode c) n)
      (fun c n => (1 + (T_cell_bits V.encode (fun v => V.T_encode v) c +
        T_max (cell_bits V.encode c) n))%N) 0%nat r <=
      (8 * cost * bits + 1) * N.of_nat (length r) + 1)%N).
    { apply T_fold_right_members_le. exact Hcallback. }
    pose proof (tuple_scan_budget cost bits (N.of_nat (length r)) Hcost Hbits) as Hbudget.
    assert (Hlength : N.of_nat (length r + 1) = (N.of_nat (length r) + 1)%N) by lia.
    rewrite Hlength. time_unfold T_tuple_bits. cbn beta iota zeta.
    clear Hcells Hcallback. clearbody cost bits. lia.
  Qed.

  (** A terminal update charges two node-key trie operations and fixed record accesses. *)
  Lemma T_mark_terminal_budget : forall ix n present stored_width bound,
    Pos.size_nat n <= bound ->
    (T_mark_terminal ix n present stored_width <=
      16 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (bound + 1))%N.
  Proof.
    intros ix n present stored_width bound Hnode.
    set (bits := N.of_nat (bound + 1)) in *.
    set (cost := (PTrieT.c_trie + V.c_key + 1)%N) in *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    assert (Hunit : (1 <= cost * bits)%N).
    { replace 1%N with (1 * 1)%N by reflexivity. apply N.mul_le_mono; assumption. }
    assert (Hread : (T_read_node ix n <= cost * bits + 2)%N).
    { eapply N.le_trans; [apply T_read_node_le |].
      apply N.add_le_mono_r, N.mul_le_mono; [unfold cost; lia | unfold bits; lia]. }
    assert (Hset : forall nd : index_node (cell V.t),
      (PTrieCode.T_set n nd (index_nodes ix) <= cost * bits)%N).
    { intro nd. eapply N.le_trans; [apply PTrieT.T_set_le |].
      apply N.mul_le_mono; [unfold cost; lia | unfold bits; lia]. }
    time_unfold T_mark_terminal. time_unfold T_next. time_unfold @T_index_counter.
    time_pose. time_simpl. time_cbn. clear Hnode Hset. clearbody cost bits. lia.
  Qed.

  (** The finishing pass fits the membership scan, width scan and final node write. *)
  Lemma finish_budget : forall cost amount bits,
    (1 <= cost -> 1 <= amount -> 1 <= bits ->
      4 + 160 * cost * amount * bits + 16 * cost * amount * bits + bits +
        16 * cost * bits <= 224 * cost * amount * bits)%N.
  Proof.
    intros cost amount bits Hcost Hamount Hbits.
    assert (Hsingle : (cost * bits <= cost * amount * bits)%N).
    { apply N.mul_le_mono_r. replace cost with (cost * 1)%N at 1 by ring.
      apply N.mul_le_mono_l. exact Hamount. }
    assert (Hwidth : (bits <= cost * amount * bits)%N).
    { replace bits with (1 * bits)%N at 1 by ring. apply N.mul_le_mono_r.
      replace 1%N with (1 * 1)%N by reflexivity. apply N.mul_le_mono; assumption. }
    assert (Hunit : (1 <= cost * amount * bits)%N) by (eapply N.le_trans; eassumption).
    replace (4 + 160 * cost * amount * bits + 16 * cost * amount * bits + bits +
      16 * cost * bits)%N with
      (4 + 176 * (cost * amount * bits) + bits + 16 * (cost * bits))%N by ring.
    replace (224 * cost * amount * bits)%N with (224 * (cost * amount * bits))%N by ring.
    lia.
  Qed.

  (** Insertion's finishing pass uses only the original width and the bounded final cursor. *)
  Lemma T_insert_finish_budget : forall r ix, valid ix ->
    (T_insert_finish r ix (fold_left insert_step_st r (start ix)) <=
      224 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (length r + 1) *
        N.of_nat (width ix r + 1))%N.
  Proof.
    intros r ix Hvalid. pose proof (valid_shape ix Hvalid) as Hshape.
    assert (Hcounter : Pos.size_nat (next ix) <= width ix r) by (apply node_bits_width, Pos.le_refl).
    assert (Hcells : forall c, In c r -> cell_bits V.encode c <= width ix r).
    { intros c Hin. now apply tuple_cell_width. }
    pose proof (T_contains_budget ix r (width ix r) Hshape Hcounter Hcells) as Hcontains.
    pose proof (T_tuple_bits_budget r (width ix r) Hcells) as Htuple.
    set (st := fold_left insert_step_st r (start ix)).
    assert (Hpoint : (snd st <= next (fst st))%positive).
    { unfold st. apply insert_walk_point_bound; [exact Hshape |].
      change (1 <= next ix)%positive. apply Pos.le_1_l. }
    assert (Hpoint_bits : Pos.size_nat (snd st) <= width ix r).
    { eapply Nat.le_trans; [apply positive_bits_mono; exact Hpoint |].
      unfold st. apply insert_prefix_counter_bits, Nat.le_refl. }
    pose proof (T_mark_terminal_budget (fst st) (snd st) true
      (Nat.max (index_cell_width ix) (tuple_bits r)) (width ix r) Hpoint_bits) as Hmark.
    assert (Hstored_bits : index_cell_width ix <= width ix r) by (unfold width, max_cell_bits; lia).
    assert (Hmax : (T_max (index_cell_width ix) (tuple_bits r) <= N.of_nat (width ix r + 1))%N).
    { pose proof (T_nat_max_le (index_cell_width ix) (tuple_bits r)). lia. }
    set (cost := (PTrieT.c_trie + V.c_key + 1)%N) in *.
    set (amount := N.of_nat (length r + 1)) in *.
    set (bits := N.of_nat (width ix r + 1)) in *.
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    assert (Hamount : (1 <= amount)%N) by (unfold amount; lia).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    pose proof (finish_budget cost amount bits Hcost Hamount Hbits) as Hbudget.
    clear Hvalid Hshape Hcounter Hcells Hpoint Hpoint_bits Hstored_bits.
    clearbody cost amount bits st.
    time_unfold T_insert_finish. destruct (contains r ix); time_simpl; time_cbn; lia.
  Qed.

  (** Removal's finishing pass uses the original counter and the surviving bounded cursor. *)
  Lemma T_remove_finish_budget : forall r ix, valid ix ->
    (T_remove_finish r ix (fold_left remove_step_st r (start ix)) <=
      224 * (PTrieT.c_trie + V.c_key + 1) * N.of_nat (length r + 1) *
        N.of_nat (width ix r + 1))%N.
  Proof.
    intros r ix Hvalid. pose proof (valid_shape ix Hvalid) as Hshape.
    assert (Hcounter : Pos.size_nat (next ix) <= width ix r) by (apply node_bits_width, Pos.le_refl).
    assert (Hcells : forall c, In c r -> cell_bits V.encode c <= width ix r).
    { intros c Hin. now apply tuple_cell_width. }
    pose proof (T_contains_budget ix r (width ix r) Hshape Hcounter Hcells) as Hcontains.
    set (st := fold_left remove_step_st r (start ix)).
    assert (Hpoint : (snd st <= next (fst st))%positive).
    { unfold st. apply remove_walk_point_bound; [exact Hshape |].
      change (1 <= next ix)%positive. apply Pos.le_1_l. }
    assert (Hpoint_bits : Pos.size_nat (snd st) <= width ix r).
    { eapply Nat.le_trans; [apply positive_bits_mono; exact Hpoint |].
      unfold st. rewrite remove_walk_counter. cbn [start fst]. exact Hcounter. }
    pose proof (T_mark_terminal_budget (fst st) (snd st) false
      (index_cell_width ix) (width ix r) Hpoint_bits) as Hmark.
    set (cost := (PTrieT.c_trie + V.c_key + 1)%N) in *.
    set (amount := N.of_nat (length r + 1)) in *.
    set (bits := N.of_nat (width ix r + 1)) in *.
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    assert (Hamount : (1 <= amount)%N) by (unfold amount; lia).
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    pose proof (finish_budget cost amount bits Hcost Hamount Hbits) as Hbudget.
    clear Hvalid Hshape Hcounter Hcells Hpoint Hpoint_bits.
    clearbody cost amount bits st.
    time_unfold T_remove_finish. destruct (contains r ix); time_simpl; time_cbn; lia.
  Qed.

  Definition inv := valid.
  Definition c_map : N := PTrieT.c_trie.
  Lemma inv_wf : forall a ix,
    wf a ix <-> inv ix /\ (forall u, mem ix u -> length u = a).
  Proof.
    intros a ix. reflexivity.
  Qed.

  Lemma insert_path : forall ix r, inv ix -> inv (insert r ix).
  Proof.
    intros ix r Hinv. now apply valid_insert.
  Qed.

  Lemma remove_path : forall ix r, inv ix -> inv (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma T_insert_step_le : forall ix n c,
    (T_insert_step ix n c <= 4 * c_map * N.of_nat (width ix [c] + 1) + 4)%N.
  Proof. Admitted. (* PLAN-DEFECT: eager Val encoding contributes V.T_encode; the fixed trie-only coefficient omits V.c_key. *)

  (** Edge maps use the shared binary trie contracts. *)
  Lemma c_map_source : c_map = PTrieT.c_trie.
  Proof.
    reflexivity.
  Qed.
  Definition k_walk : N := (512 * (PTrieT.c_trie + V.c_key + 1))%N.
  (** The public constant absorbs the aggregate path and wrapper charges. *)
  Lemma c_ix_walk : (4 * c_map + 4 + k_walk <= c_ix)%N.
  Proof.
    unfold c_map, k_walk, c_ix. lia.
  Qed.
  (** Each insertion step uses the width of the complete original walk. *)
  Lemma T_insert_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_insert_step_st (fold_left insert_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  Proof. Admitted. (* PLAN-DEFECT: even the empty valid prefix eagerly pays V.T_encode, which is absent from the fixed trie-only coefficient. *)

  (** Each removal step uses the width of the complete original walk. *)
  Lemma T_remove_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_remove_step_st (fold_left remove_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  Proof. Admitted. (* PLAN-DEFECT: even an absent edge in the empty valid prefix eagerly pays V.T_encode, omitted by the fixed trie-only coefficient. *)

  (** Initialization and both finishing passes fit the original walk budget. *)
  Lemma T_walk_ends : forall r ix, inv ix ->
    (T_start ix +
     T_insert_finish r ix (fold_left insert_step_st r (start ix)) +
     T_remove_finish r ix (fold_left remove_step_st r (start ix)) <=
      k_walk * N.of_nat (length r + 1) * N.of_nat (width ix r + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Insertion follows its named state walk. *)
  Lemma F_insert_steps : forall r ix, inv ix ->
    insert r ix = insert_finish r ix (fold_left insert_step_st r (start ix)).
  Proof.
    reflexivity.
  Qed.

  (** Removal follows its named state walk. *)
  Lemma F_remove_steps : forall r ix, inv ix ->
    remove r ix = remove_finish r ix (fold_left remove_step_st r (start ix)).
  Proof.
    reflexivity.
  Qed.

  (** Insertion aggregates the path-step charges. *)
  Lemma T_insert_steps : forall r ix, inv ix ->
    (T_insert r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.
  Proof. Admitted. (* STUB *)

  (** Removal aggregates the path-step charges. *)
  Lemma T_remove_steps : forall r ix, inv ix ->
    (T_remove r ix <= N.of_nat (length r + 1) *
      ((4 * c_map + k_walk) * N.of_nat (width ix r + 1) + 4))%N.
  Proof. Admitted. (* STUB *)

End IndexT.
