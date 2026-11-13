(** * Tuple indexes with stored prefix nodes

    Indexes store cell edges, live suffix counts and terminal prefix nodes.
    For example, removing one tuple preserves a prefix shared with another tuple.
    Builds on: IndexSig and positive-key tries. *)

From Stdlib Require Import List PArith NArith PeanoNat Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig Syntax IndexSig.

Import List.ListNotations.

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

  Lemma wf_insert : forall a r ix, wf a ix -> length r = a -> wf a (insert r ix).
  Proof. Admitted. (* STUB *)

  Lemma wf_remove : forall a r ix, wf a ix -> wf a (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma mem_insert : forall a r ix u, wf a ix -> length r = a ->
    (mem (insert r ix) u <-> u = r \/ mem ix u).
  Proof. Admitted. (* OPEN: insertion path and suffix-count preservation remain to be proved. *)

  Lemma mem_remove : forall a r ix u, wf a ix ->
    (mem (remove r ix) u <-> u <> r /\ mem ix u).
  Proof. Admitted. (* STUB *)

  Lemma mem_arity : forall a ix u, wf a ix -> mem ix u -> length u = a.
  Proof.
    intros a ix u [_ Harity]. apply Harity.
  Qed.

  Lemma node_root : forall a ix, wf a ix -> node ix (root ix) [].
  Proof.
    intros a ix _. reflexivity.
  Qed.

  Lemma node_live : forall a ix n pre, wf a ix -> node ix n pre -> pre <> [] ->
    exists suf, mem ix (pre ++ suf).
  Proof. Admitted. (* STUB *)

  Lemma node_fun : forall a ix n m pre, wf a ix ->
    node ix n pre -> node ix m pre -> n = m.
  Proof.
    intros a ix n m pre _ Hn Hm. unfold node in *. congruence.
  Qed.

  Lemma child_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (forall m, child ix n c = Some m <-> node ix m (pre ++ [c])) /\
    (child ix n c = None <-> ~ exists suf, mem ix (pre ++ c :: suf)).
  Proof. Admitted. (* STUB *)

  Lemma children_spec : forall a ix n pre c, wf a ix -> node ix n pre ->
    (In c (children ix n) <-> exists m, child ix n c = Some m) /\
    NoDup (children ix n).
  Proof. Admitted. (* STUB *)

  Lemma degree_spec : forall a ix n pre, wf a ix -> node ix n pre ->
    N.to_nat (degree ix n) = length (children ix n).
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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

  Lemma T_child_le : forall ix n c,
    (T_child ix n c <= c_ix * N.of_nat (width ix [c] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_children_le : forall a ix n, wf a ix ->
    (T_children ix n <= c_ix * N.of_nat (N.to_nat (degree ix n) + 1) *
      N.of_nat (width ix [] + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_degree_le : forall ix n,
    (T_degree ix n <= c_ix * N.of_nat (width ix [] + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition inv := valid.
  Definition c_map : N := PTrieT.c_trie.
  Lemma inv_wf : forall a ix,
    wf a ix <-> inv ix /\ (forall u, mem ix u -> length u = a).
  Proof.
    intros a ix. reflexivity.
  Qed.

  Lemma insert_path : forall ix r, inv ix -> inv (insert r ix).
  Proof. Admitted. (* STUB *)

  Lemma remove_path : forall ix r, inv ix -> inv (remove r ix).
  Proof. Admitted. (* STUB *)

  Lemma T_insert_step_le : forall ix n c,
    (T_insert_step ix n c <= 4 * c_map * N.of_nat (width ix [c] + 1) + 4)%N.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

  (** Each removal step uses the width of the complete original walk. *)
  Lemma T_remove_step_st_le : forall ix r pre c suf, inv ix -> r = pre ++ c :: suf ->
    (T_remove_step_st (fold_left remove_step_st pre (start ix)) c <=
      4 * c_map * N.of_nat (width ix r + 1) + 4)%N.
  Proof. Admitted. (* STUB *)

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
