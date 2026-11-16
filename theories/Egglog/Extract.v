(** * Minimum-cost extraction with checked finite witnesses

    A class queue finalises optimal constructor rows and resumes their waiting parents.
    For example, a finite nullary alternative can seed extraction through a cyclic e-graph.
    Builds on: ExtractSig, class tries, priority queues and bounded loops. *)

From Stdlib Require Import List PArith NArith Arith Bool Lia Relations.Relation_Operators
  Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Trie HeapSig Heap.
From Galois.Egglog Require Import ValueSig IndexSig DatabaseSig Syntax Model Sorts ExtractSig.

Import List.ListNotations.

(** A search row records its constructor, complete key and output class. *)
Definition search_row (V : Type) := (positive * list (cell V) * positive)%type.

(** A suspended row retains the unprocessed suffix and the consumed costs in reverse order. *)
Record extraction_frame (V : Type) := ExtractionFrame {
  frame_row : search_row V;
  frame_rest : list (cell V);
  frame_costs : list N
}.

Arguments ExtractionFrame {V}.
Arguments frame_row {V}.
Arguments frame_rest {V}.
Arguments frame_costs {V}.
TimeFun frame_row.
TimeFun frame_rest.
TimeFun frame_costs.

(** Search maps use class identifiers; the source rows and database remain unchanged. *)
Record extraction_state (V DB H : Type) := ExtractionState {
  search_database : DB;
  search_rows : list (search_row V);
  search_row_count : nat;
  search_final_costs : ptrie N;
  search_candidates : ptrie (N * extraction_row V);
  search_waiters : ptrie (list (extraction_frame V));
  search_queue : H;
  search_finalised : extraction_best V
}.

Arguments ExtractionState {V DB H}.
Arguments search_database {V DB H}.
Arguments search_rows {V DB H}.
Arguments search_row_count {V DB H}.
Arguments search_final_costs {V DB H}.
Arguments search_candidates {V DB H}.
Arguments search_waiters {V DB H}.
Arguments search_queue {V DB H}.
Arguments search_finalised {V DB H}.
TimeFun search_database.
TimeFun search_rows.
TimeFun search_row_count.
TimeFun search_final_costs.
TimeFun search_candidates.
TimeFun search_waiters.
TimeFun search_queue.
TimeFun search_finalised.

(** Replacing mutable search fields preserves the source and its cached row count. *)
Definition search_restate {V DB H} (s : extraction_state V DB H)
    (costs : ptrie N) (candidates : ptrie (N * extraction_row V))
    (waiters : ptrie (list (extraction_frame V))) (queue : H)
    (finals : extraction_best V) : extraction_state V DB H :=
  ExtractionState (search_database s) (search_rows s) (search_row_count s)
    costs candidates waiters queue finals.
TimeFun search_restate.

(** A new row has consumed no children. *)
Definition search_new_frame {V} (r : search_row V) : extraction_frame V :=
  ExtractionFrame r (snd (fst r)) [].
TimeFun search_new_frame.

(** A declaration trie retains the first declaration of each function name. *)
Fixpoint inventory_decl_table (ds : list decl) : ptrie (nat * output) :=
  match ds with
  | [] => Empty
  | d :: rest =>
    PTrieCode.set (name d) (length (arg_sorts d), out d) (inventory_decl_table rest)
  end.
TimeFun inventory_decl_table.

(** The full-slot check consumes at most the positions present in the layout. *)
Fixpoint inventory_sequence (start count : nat) (positions : list nat) : bool :=
  match count, positions with
  | O, [] => true
  | S count', i :: rest =>
    Nat.eqb i start && inventory_sequence (S start) count' rest
  | _, _ => false
  end.
TimeFun inventory_sequence.

(** Only a constructor's unpermuted full slot is selected. The check returns the
    constructor's argument count for a selected slot. *)
Definition inventory_slot (tb : ptrie (nat * output)) (f : positive)
    (positions : list nat) : option nat :=
  match trie_get f tb with
  | Some (arity, OId) =>
    if inventory_sequence 0 (S arity) positions then Some arity else None
  | _ => None
  end.
TimeFun inventory_slot.

(** A selected constructor is removed so that a later full slot cannot emit it again. Each
    emitted entry holds the slot number and the argument count. *)
Fixpoint inventory_scan (tb : ptrie (nat * output)) (sl : list (positive * list nat))
    (slot : N) : list (positive * (N * nat)) :=
  match sl with
  | [] => []
  | (f, positions) :: rest =>
    match inventory_slot tb f positions with
    | Some arity =>
      (f, (slot, arity)) :: inventory_scan (PTrieCode.remove f tb) rest (N.succ slot)
    | None => inventory_scan tb rest (N.succ slot)
    end
  end.
TimeFun inventory_scan.

(** Trie preparation agrees with the two first-declaration lookup functions. *)
Lemma inventory_decl_lookup : forall ds f,
  trie_get f (inventory_decl_table ds) =
    match lookup_sorts ds f, lookup_kind ds f with
    | Some ss, Some o => Some (length ss, o)
    | _, _ => None
    end.
Proof.
  induction ds as [|d ds IH]; intro f.
  - apply PTrie.get_empty.
  - cbn [inventory_decl_table lookup_sorts lookup_kind].
    destruct (Pos.eqb (name d) f) eqn:Hname.
    + apply Pos.eqb_eq in Hname. subst f. apply PTrie.get_set_same.
    + rewrite PTrie.get_set_other; [apply IH |].
      intro Heq. subst f. rewrite Pos.eqb_refl in Hname. discriminate.
Qed.

(** The position checker recognizes exactly one consecutive sequence. *)
Lemma inventory_sequence_spec : forall count start positions,
  inventory_sequence start count positions = true <-> positions = seq start count.
Proof.
  induction count as [|count IH]; intros start [|i rest]; cbn [inventory_sequence seq].
  - tauto.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, Nat.eqb_eq, IH.
    split.
    + intros [<- ->]. reflexivity.
    + intro Heq. injection Heq as -> ->. auto.
Qed.

(** The check returns n exactly for a constructor with n arguments whose slot lists the
    positions 0 to n in order. *)
Lemma inventory_slot_spec : forall tb f positions n,
  inventory_slot tb f positions = Some n <->
    trie_get f tb = Some (n, OId) /\ positions = seq 0 (S n).
Proof.
  intros tb f positions n. unfold inventory_slot.
  destruct (trie_get f tb) as [[arity out]|] eqn:Hget.
  - destruct out; try (split; [discriminate | intros [Hpair _]; discriminate]).
    destruct (inventory_sequence 0 (S arity) positions) eqn:Hseq.
    + apply inventory_sequence_spec in Hseq. split.
      * intro Hsome. injection Hsome as <-. auto.
      * intros [Hpair _]. injection Hpair as <-. reflexivity.
    + split; [discriminate |].
      intros [Hpair Hpositions]. injection Hpair as <-.
      apply inventory_sequence_spec in Hpositions. congruence.
  - split; [discriminate | intros [Hpair _]; discriminate].
Qed.

(** Each selected entry identifies its original position, its declaration and its argument
    count. *)
Lemma inventory_scan_sound : forall sl tb offset f slot n,
  In (f, (slot, n)) (inventory_scan tb sl offset) ->
  exists positions j, nth_error sl j = Some (f, positions) /\
    slot = (offset + N.of_nat j)%N /\ trie_get f tb = Some (n, OId) /\
    positions = seq 0 (S n).
Proof.
  induction sl as [|[head positions] sl IH]; intros tb offset f slot n Hin;
    cbn [inventory_scan] in Hin; [contradiction |].
  destruct (inventory_slot tb head positions) as [arity|] eqn:Hslot.
  - destruct Hin as [Heq | Hin].
    + injection Heq as <- <- <-.
      apply inventory_slot_spec in Hslot as [Hget Hseq].
      exists positions, 0. cbn [nth_error N.of_nat]. repeat split; auto; lia.
    + destruct (IH _ _ _ _ _ Hin) as [perm [j [Hnth [Hindex [Hget Hseq]]]]].
      assert (Hneq : f <> head).
      { intro Heq. subst f. rewrite PTrie.get_remove_same in Hget. discriminate. }
      rewrite PTrie.get_remove_other in Hget by exact Hneq.
      exists perm, (S j). cbn [nth_error]. repeat split; auto.
      rewrite Nat2N.inj_succ. lia.
  - destruct (IH _ _ _ _ _ Hin) as [perm [j [Hnth [Hindex [Hget Hseq]]]]].
    exists perm, (S j). cbn [nth_error]. repeat split; auto.
    rewrite Nat2N.inj_succ. lia.
Qed.

(** Removing each selected name makes the output duplicate free. *)
Lemma inventory_scan_nodup : forall sl tb offset,
  NoDup (map fst (inventory_scan tb sl offset)).
Proof.
  induction sl as [|[f positions] sl IH]; intros tb offset; cbn [inventory_scan].
  - constructor.
  - destruct (inventory_slot tb f positions) as [arity|]; [|apply IH].
    cbn [map fst]. constructor; [|apply IH].
    intro Hin. apply in_map_iff in Hin as [[g [slot n]] [Heq Hin]].
    cbn [fst] in Heq. subst g.
    destruct (inventory_scan_sound _ _ _ _ _ _ Hin)
      as [perm [j [_ [_ [Hget _]]]]].
    rewrite PTrie.get_remove_same in Hget. discriminate.
Qed.

(** Any constructor with a full slot is selected at that slot or an earlier full slot. *)
Lemma inventory_scan_complete : forall sl tb offset f n,
  trie_get f tb = Some (n, OId) -> In (f, seq 0 (S n)) sl ->
  In f (map fst (inventory_scan tb sl offset)).
Proof.
  induction sl as [|[head positions] sl IH]; intros tb offset f n Hget Hin;
    [contradiction |].
  cbn [inventory_scan].
  destruct (inventory_slot tb head positions) as [arity|] eqn:Hslot.
  - cbn [map fst]. destruct (Pos.eq_dec f head) as [-> | Hneq]; [now left |].
    right. eapply IH.
    + rewrite PTrie.get_remove_other by exact Hneq. exact Hget.
    + destruct Hin as [Heq | Hin]; [congruence |exact Hin].
  - eapply IH; [exact Hget |].
    destruct Hin as [Heq | Hin]; [|exact Hin].
    injection Heq as Hhead Hpositions. subst head positions.
    assert (Haccept : inventory_slot tb f (seq 0 (S n)) = Some n).
    { apply inventory_slot_spec. auto. }
    change (inventory_slot tb f (seq 0 (S n)) = None) in Hslot.
    rewrite Haccept in Hslot. discriminate.
Qed.

(** Every successful kind lookup has the same declaration's argument sorts. *)
Lemma inventory_lookup_sorts : forall ds f o,
  lookup_kind ds f = Some o -> exists ss, lookup_sorts ds f = Some ss.
Proof.
  induction ds as [|d ds IH]; intros f o Hkind; [discriminate |].
  cbn [lookup_kind lookup_sorts] in *.
  destruct (Pos.eqb (name d) f).
  - eexists. reflexivity.
  - eapply IH. exact Hkind.
Qed.

(** Selecting all valid positions in order returns the original tuple. *)
Lemma inventory_permute_full : forall A (xs : list A),
  flat_map (fun i => option_list (nth_error xs i)) (seq 0 (length xs)) = xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; [reflexivity |].
  cbn [length seq flat_map nth_error option_list app].
  f_equal. rewrite <- seq_shift, flat_map_concat_map, map_map.
  change (concat (map (fun i => option_list (nth_error xs i))
    (seq 0 (length xs))) = xs).
  rewrite <- flat_map_concat_map. exact IH.
Qed.

(** Slot syntax pays for each name and each position read in unary. *)
Definition inventory_slot_bits (sl : list (positive * list nat)) : nat :=
  fold_right (fun s n => Pos.size_nat (fst s) +
    fold_right (fun i m => i + 1 + m) 0 (snd s) + 1 + n) 0 sl.

(** A positive counter's width is its logarithm plus the leading bit. *)
Lemma inventory_positive_width : forall p,
  Pos.size_nat p = Nat.log2 (Pos.to_nat p) + 1.
Proof.
  induction p as [p IH|p IH|].
  - rewrite Pos2Nat.inj_xI.
    replace (S (2 * Pos.to_nat p)) with (2 * Pos.to_nat p + 1) by lia.
    rewrite Nat.log2_succ_double by apply Pos2Nat.is_pos.
    cbn [Pos.size_nat]. lia.
  - rewrite Pos2Nat.inj_xO, Nat.log2_double by apply Pos2Nat.is_pos.
    cbn [Pos.size_nat]. lia.
  - reflexivity.
Qed.

(** Every slot counter fits the bit width of the total number of slots. *)
Lemma inventory_counter_width : forall slot bound, N.to_nat slot <= bound ->
  N.size_nat slot <= Nat.log2 bound + 1.
Proof.
  intros [|slot] bound Hbound; [cbn [N.size_nat]; lia |].
  cbn [N.size_nat N.to_nat] in *. rewrite inventory_positive_width.
  apply Nat.add_le_mono_r, Nat.log2_le_mono. exact Hbound.
Qed.

(** Each emitted name is paid for by its original slot. *)
Lemma inventory_scan_size : forall sl tb offset bound,
  N.to_nat offset + length sl <= bound ->
  inventory_bits (inventory_scan tb sl offset) <=
    inventory_slot_bits sl * (Nat.log2 bound + 3).
Proof.
  induction sl as [|[f positions] sl IH]; intros tb offset bound Hbound.
  - exact (Nat.le_refl 0).
  - assert (Hnext : N.to_nat (N.succ offset) + length sl <= bound).
    { rewrite N2Nat.inj_succ. cbn [length] in Hbound. lia. }
    pose proof (inventory_counter_width offset bound ltac:(cbn [length] in Hbound; lia))
      as Hwidth.
    cbn [inventory_scan]. destruct (inventory_slot tb f positions) as [arity|].
    + specialize (IH (PTrieCode.remove f tb) (N.succ offset) bound Hnext).
      cbn [inventory_bits inventory_slot_bits fold_right fst snd] in *.
      unfold inventory_bits, inventory_slot_bits in IH. nia.
    + specialize (IH tb (N.succ offset) bound Hnext).
      cbn [inventory_slot_bits fold_right fst snd].
      unfold inventory_slot_bits in IH. nia.
Qed.

(** A position comparison is charged to the position read from the layout. *)
Lemma T_inventory_sequence_le : forall start count positions,
  (T_inventory_sequence start count positions <=
    8 * N.of_nat (fold_right (fun i m => (i + 1 + m)%nat) 0%nat positions + 1)%nat)%N.
Proof.
  intros start count. revert start.
  induction count as [|count IH]; intros start [|i rest]; time_step.
Qed.

(** Preparing declaration metadata pays for every name and argument sort once. *)
Lemma T_inventory_decl_table_le : forall ds,
  (T_inventory_decl_table ds <= 16 * (PTrieT.c_trie + 1) *
    N.of_nat (fold_right (fun d n => (decl_bits d + n)%nat) 0%nat ds + 1)%nat)%N.
Proof.
  induction ds as [|d ds IH].
  - time_step.
  - pose proof (PTrieT.T_set_le (nat * output) (name d)
      (length (arg_sorts d), out d) (inventory_decl_table ds)) as Hset.
    change (PTrieCode.T_set (name d) (length (arg_sorts d), out d)
      (inventory_decl_table ds) <= PTrieT.c_trie *
        N.of_nat (Pos.size_nat (name d) + 1))%N in Hset.
    pose proof (Datatypes.T_length_le (arg_sorts d)) as Hlength.
    unfold decl_bits in *.
    time_unfold @T_inventory_decl_table. time_simpl. time_cbn.
    rewrite !Nat2N.inj_add in *.
    unfold PTrieT.c_trie in *.
    lia.
Qed.

(** Each slot check pays for the name and the positions that it reads. *)
Lemma T_inventory_slot_le : forall tb f positions,
  (T_inventory_slot tb f positions <= 16 * (PTrieT.c_trie + 1) *
    N.of_nat (Pos.size_nat f +
      fold_right (fun i m => (i + 1 + m)%nat) 0%nat positions + 1)%nat)%N.
Proof.
  intros tb f positions.
  pose proof (PTrieT.T_trie_get_le (nat * output) f tb) as Hget.
  time_unfold @T_inventory_slot. time_simpl. time_cbn.
  destruct (trie_get f tb) as [[arity o] |]; [destruct o |].
  - rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. lia.
  - pose proof (T_inventory_sequence_le 0 (S arity) positions) as Hsequence.
    rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. lia.
  - rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. lia.
  - rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. lia.
Qed.

(** A scan visits every layout slot and advances a bounded binary counter. *)
Lemma T_inventory_scan_le : forall sl tb offset bound,
  N.to_nat offset + length sl <= bound ->
  (T_inventory_scan tb sl offset <= 64 * (PTrieT.c_trie + 1) *
    N.of_nat (inventory_slot_bits sl + 1) * N.of_nat (Nat.log2 bound + 1))%N.
Proof.
  induction sl as [|[f positions] sl IH]; intros tb offset bound Hbound.
  - unfold inventory_slot_bits. time_unfold @T_inventory_scan.
    time_simpl. time_cbn. rewrite Nat2N.inj_add. unfold PTrieT.c_trie. nia.
  - assert (Hnext : N.to_nat (N.succ offset) + length sl <= bound).
    { rewrite N2Nat.inj_succ. cbn [length] in Hbound. lia. }
    pose proof (inventory_counter_width offset bound ltac:(cbn [length] in Hbound; lia))
      as Hwidth.
    pose proof (T_inventory_slot_le tb f positions) as Hslot.
    pose proof (PTrieT.T_remove_le (nat * output) f tb) as Hremove.
    change (PTrieCode.T_remove f tb <= PTrieT.c_trie *
      N.of_nat (Pos.size_nat f + 1))%N in Hremove.
    pose proof (IH (PTrieCode.remove f tb) (N.succ offset) bound Hnext) as Hselected.
    pose proof (IH tb (N.succ offset) bound Hnext) as Hskipped.
    pose proof (Std.N.T_succ_le offset) as Hsucc.
    assert (HwidthN : (N.of_nat (N.size_nat offset) <=
      N.of_nat (Nat.log2 bound + 1))%N) by lia.
    time_unfold @T_inventory_scan. time_simpl. time_cbn.
    destruct (inventory_slot tb f positions) as [arity|];
      unfold inventory_slot_bits in *;
      cbn [fold_right fst snd] in *;
      rewrite !Nat2N.inj_add in *;
      unfold PTrieT.c_trie in *; nia.
Qed.

(** Resolving a row replaces literals directly and looks up its identifier children. *)
Fixpoint dag_resolve_cells {V} (resolve : positive -> option (@Model.expr V))
    (k : list (cell V)) : option (list (@Model.expr V)) :=
  match k with
  | [] => Some []
  | Val v :: rest =>
    match dag_resolve_cells resolve rest with
    | Some es => Some (Model.ELit v :: es)
    | None => None
    end
  | Id i :: rest =>
    match resolve i, dag_resolve_cells resolve rest with
    | Some e, Some es => Some (e :: es)
    | _, _ => None
    end
  end.
TimeFun dag_resolve_cells.

(** A reverse scan unfolds a selected entry only through its earlier prefix. *)
Fixpoint dag_unfold_reverse {V} (g : extraction_dag V) (c : positive)
    : option (@Model.expr V) :=
  match g with
  | [] => None
  | (i, (f, k)) :: rest =>
    if Pos.eqb c i then
      match dag_resolve_cells (dag_unfold_reverse rest) k with
      | Some es => Some (Model.EApp f es)
      | None => None
      end
    else dag_unfold_reverse rest c
  end.
TimeFun dag_unfold_reverse.

(** Specification unfolding follows the certificate's prefix order. *)
Definition dag_unfold {V} (g : extraction_dag V) (c : positive)
    : option (@Model.expr V) := dag_unfold_reverse (rev g) c.
TimeFun dag_unfold.

(** Sound identifier resolution gives a prefix representation of the whole key. *)
Lemma dag_resolve_cells_sound : forall V (g : extraction_dag V) resolve,
  (forall i e, resolve i = Some e -> dag_represents g i e) ->
  forall k es, dag_resolve_cells resolve k = Some es -> dag_cells g k es.
Proof.
  intros V g resolve Hresolve k.
  induction k as [|[i|v] k IH]; intros es Hrun.
  - inversion Hrun. constructor.
  - cbn [dag_resolve_cells] in Hrun.
    destruct (resolve i) as [e|] eqn:Hi; [|discriminate].
    destruct (dag_resolve_cells resolve k) as [rest|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst es. constructor.
    + apply Hresolve. exact Hi.
    + apply IH. reflexivity.
  - cbn [dag_resolve_cells] in Hrun.
    destruct (dag_resolve_cells resolve k) as [rest|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst es. constructor. apply IH. reflexivity.
Qed.

(** Complete identifier resolution recovers every represented key. *)
Lemma dag_resolve_cells_complete : forall V (g : extraction_dag V) resolve,
  (forall i e, dag_represents g i e -> resolve i = Some e) ->
  forall k es, dag_cells g k es -> dag_resolve_cells resolve k = Some es.
Proof.
  intros V g resolve Hresolve k es Hcells.
  induction Hcells as [g |g v k es Hcells IH |g i e k es Hrep Hcells IH].
  - reflexivity.
  - cbn [dag_resolve_cells]. rewrite IH by exact Hresolve. reflexivity.
  - cbn [dag_resolve_cells]. rewrite (Hresolve i e Hrep), IH by exact Hresolve.
    reflexivity.
Qed.

(** Successful reverse unfolding yields a finite prefix derivation. *)
Lemma dag_unfold_reverse_sound : forall V (g : extraction_dag V) c e,
  dag_unfold_reverse g c = Some e -> dag_represents (rev g) c e.
Proof.
  intros V g. induction g as [|[i [f k]] g IH]; intros c e Hrun.
  - discriminate.
  - cbn [dag_unfold_reverse] in Hrun.
    cbn [rev]. destruct (Pos.eqb c i) eqn:Hci.
    + apply Pos.eqb_eq in Hci. subst c.
      destruct (dag_resolve_cells (dag_unfold_reverse g) k) as [es|] eqn:Hcells;
        [|discriminate].
      inversion Hrun; subst e. constructor.
      eapply dag_resolve_cells_sound; [exact IH |exact Hcells].
    + apply dag_later. apply IH. exact Hrun.
Qed.

(** A represented class identifier is named by the certificate. *)
Lemma dag_represents_name : forall V (g : extraction_dag V) c e,
  dag_represents g c e -> In c (map fst g).
Proof.
  intros V g c e Hrep. induction Hrep as [pre c f k es Hcells |pre c e entry Hrep IH].
  - rewrite map_app. apply in_or_app. right. now left.
  - rewrite map_app. apply in_or_app. now left.
Qed.

(** A final entry either introduces the represented tree or preserves an earlier one. *)
Lemma dag_represents_last : forall V (pre : extraction_dag V) i f k c e,
  dag_represents (pre ++ [(i, (f, k))]) c e ->
  (c = i /\ exists es, e = Model.EApp f es /\ dag_cells pre k es) \/
    dag_represents pre c e.
Proof.
  intros V pre i f k c e Hrep.
  remember (pre ++ [(i, (f, k))]) as g eqn:Hg in Hrep.
  destruct Hrep as [prefix c f' k' es Hcells |prefix c e entry Hrep].
  - apply app_inj_tail in Hg as [Hprefix Hentry].
    subst prefix. injection Hentry as Hci Hf Hk. subst c f' k'.
    left. split; [reflexivity |]. exists es. auto.
  - apply app_inj_tail in Hg as [Hprefix Hentry]. subst prefix.
    now right.
Qed.

(** Distinct certificate names make every finite prefix derivation executable. *)
Lemma dag_unfold_complete : forall V (g : extraction_dag V) c e,
  NoDup (map fst g) -> dag_represents g c e -> dag_unfold g c = Some e.
Proof.
  intros V g. induction g as [|entry g IH] using rev_ind; intros c e Hnodup Hrep.
  - pose proof (dag_represents_name _ _ _ _ Hrep) as Hname. contradiction.
  - destruct entry as [i [f k]].
    rewrite map_app in Hnodup. cbn [map fst] in Hnodup.
    destruct (NoDup_remove (map fst g) [] i Hnodup) as [Hprefix Hfresh].
    rewrite app_nil_r in Hprefix, Hfresh.
    apply dag_represents_last in Hrep as [[Hci [es [He Hcells]]] |Hrep].
    + subst c e. unfold dag_unfold. rewrite rev_app_distr.
      cbn [rev app dag_unfold_reverse]. rewrite Pos.eqb_refl.
      assert (Hresolved : dag_resolve_cells (dag_unfold_reverse (rev g)) k = Some es).
      { eapply dag_resolve_cells_complete; [|exact Hcells].
        intros child tree Hchild. exact (IH child tree Hprefix Hchild). }
      rewrite Hresolved. reflexivity.
    + assert (Hci : Pos.eqb c i = false).
      { apply Pos.eqb_neq. intro Heq. subst c. apply Hfresh.
        eapply dag_represents_name. exact Hrep. }
      unfold dag_unfold. rewrite rev_app_distr.
      cbn [rev app dag_unfold_reverse]. rewrite Hci.
      exact (IH c e Hprefix Hrep).
Qed.

(** Unfolding agrees exactly with prefix representation when names are distinct. *)
Lemma dag_unfold_spec : forall V (g : extraction_dag V) c e,
  NoDup (map fst g) -> (dag_unfold g c = Some e <-> dag_represents g c e).
Proof.
  intros V g c e Hnodup. split.
  - intro Hrun. apply dag_unfold_reverse_sound in Hrun.
    now rewrite rev_involutive in Hrun.
  - apply dag_unfold_complete. exact Hnodup.
Qed.

(** A trie records which certificate identifiers have already been validated. *)
Definition dag_seen (seen : ptrie unit) (i : positive) : bool :=
  match trie_get i seen with
  | Some _ => true
  | None => false
  end.
TimeFun dag_seen.

(** Every identifier child must have an earlier validated entry. *)
Fixpoint dag_children_seen {V} (seen : ptrie unit) (k : list (cell V)) : bool :=
  match k with
  | [] => true
  | Val _ :: rest => dag_children_seen seen rest
  | Id i :: rest => dag_seen seen i && dag_children_seen seen rest
  end.
TimeFun dag_children_seen.

(** Validation checks every row and then confirms that the requested root was present. *)
Fixpoint dag_validate {V}
    (check_row : positive -> positive -> list (cell V) -> bool)
    (seen : ptrie unit) (g : extraction_dag V) (root : positive) : bool :=
  match g with
  | [] => dag_seen seen root
  | (i, (f, k)) :: rest =>
    if dag_seen seen i then false
    else if dag_children_seen seen k then
      if check_row i f k then
        dag_validate check_row (PTrieCode.set i tt seen) rest root
      else false
    else false
  end.
TimeFun dag_validate.

(** Ordered entries introduce fresh names and use only names from their prefix. *)
Fixpoint dag_ordered_from {V} (known : list positive) (g : extraction_dag V) : Prop :=
  match g with
  | [] => True
  | (i, (_, k)) :: rest =>
    ~ In i known /\ (forall child, In (Id child) k -> In child known) /\
      dag_ordered_from (i :: known) rest
  end.

(** Marking one name preserves all earlier membership decisions. *)
Lemma dag_seen_set : forall seen i j,
  dag_seen (PTrieCode.set i tt seen) j =
    if Pos.eqb j i then true else dag_seen seen j.
Proof.
  intros seen i j. destruct (Pos.eqb j i) eqn:Hji.
  - apply Pos.eqb_eq in Hji. subst j. unfold dag_seen.
    rewrite PTrie.get_set_same. reflexivity.
  - apply Pos.eqb_neq in Hji. unfold dag_seen.
    rewrite PTrie.get_set_other by exact Hji. reflexivity.
Qed.

(** Child membership checking reflects membership of every identifier in the key. *)
Lemma dag_children_seen_spec : forall V seen (k : list (cell V)),
  dag_children_seen seen k = true <->
    forall i, In (Id i) k -> dag_seen seen i = true.
Proof.
  intros V seen k. induction k as [|[j|v] k IH]; cbn [dag_children_seen].
  - split; [intros _ i Hin; contradiction |intros; reflexivity].
  - rewrite andb_true_iff, IH. split.
    + intros [Hj Hrest] i [Heq|Hin].
      * injection Heq as Heq. subst i. exact Hj.
      * now apply Hrest.
    + intro H. split; [apply H; now left |].
      intros i Hin. apply H. now right.
  - rewrite IH. split.
    + intros H i [Heq|Hin]; [discriminate |now apply H].
    + intros H i Hin. apply H. now right.
Qed.

(** Validation establishes order, successful row checks and the root's membership. *)
Lemma dag_validate_sound : forall V check_row (g : extraction_dag V) seen root known,
  (forall i, dag_seen seen i = true <-> In i known) ->
  dag_validate check_row seen g root = true ->
  dag_ordered_from known g /\
    Forall (fun entry => check_row (fst entry) (fst (snd entry)) (snd (snd entry)) = true) g /\
    In root (known ++ map fst g).
Proof.
  intros V check_row g. induction g as [|[i [f k]] g IH];
    intros seen root known Hseen Hrun.
  - cbn [dag_validate] in Hrun. split; [exact I |].
    split; [constructor |]. rewrite app_nil_r. now apply Hseen.
  - cbn [dag_validate] in Hrun.
    destruct (dag_seen seen i) eqn:Hi; [discriminate |].
    destruct (dag_children_seen seen k) eqn:Hchildren; [|discriminate].
    destruct (check_row i f k) eqn:Hrow; [|discriminate].
    assert (Hmarked : forall j,
      dag_seen (PTrieCode.set i tt seen) j = true <-> In j (i :: known)).
    { intro j. rewrite dag_seen_set. destruct (Pos.eqb j i) eqn:Hji.
      - apply Pos.eqb_eq in Hji. subst j. cbn. intuition.
      - apply Pos.eqb_neq in Hji. rewrite Hseen. cbn. intuition congruence. }
    destruct (IH _ _ _ Hmarked Hrun) as [Hordered [Hrows Hroot]].
    split.
    + cbn [dag_ordered_from]. split.
      * intro Hin. apply Hseen in Hin. congruence.
      * split; [|exact Hordered]. intros child Hin. apply Hseen.
        now apply (proj1 (dag_children_seen_spec V seen k) Hchildren).
    + split; [constructor; assumption |].
      cbn [map fst] in *. rewrite !in_app_iff in *. cbn in Hroot |- *. tauto.
Qed.

(** Ordered entries have distinct names, all fresh with respect to the initial prefix. *)
Lemma dag_ordered_names : forall V known (g : extraction_dag V),
  dag_ordered_from known g ->
  NoDup (map fst g) /\ forall i, In i (map fst g) -> ~ In i known.
Proof.
  intros V known g. revert known.
  induction g as [|[i [f k]] g IH]; intros known Hordered.
  - split; [constructor |]. cbn. tauto.
  - destruct Hordered as [Hfresh [Hchildren Hordered]].
    destruct (IH _ Hordered) as [Hnodup Hnames]. cbn [map fst]. split.
    + constructor; [|exact Hnodup]. intro Hin. exact (Hnames i Hin (or_introl eq_refl)).
    + intros j [Hji|Hin]; [subst j; exact Hfresh |].
      intro Hknown. exact (Hnames j Hin (or_intror Hknown)).
Qed.

(** A decomposition exposes exactly the names available before the current entry. *)
Lemma dag_ordered_prefix : forall V known (g : extraction_dag V),
  dag_ordered_from known g -> forall pre i f k post,
  g = pre ++ (i, (f, k)) :: post ->
  forall child, In (Id child) k -> In child (known ++ map fst pre).
Proof.
  intros V known g. revert known.
  induction g as [|[j [f' k']] g IH]; intros known Hordered pre i f k post Heq child Hin.
  - destruct pre; discriminate.
  - destruct Hordered as [Hfresh [Hchildren Hordered]].
    destruct pre as [|entry pre].
    + injection Heq as Hji Hf Hk Hpost. subst j f' k'.
      cbn [map]. rewrite app_nil_r. now apply Hchildren.
    + injection Heq as Hentry Htail. subst entry.
      specialize (IH _ Hordered pre i f k post Htail child Hin).
      cbn [map fst] in *. rewrite !in_app_iff in *. cbn in IH |- *. tauto.
Qed.

(** Resolving a key preserves any relation established by its literal and identifier cases. *)
Lemma dag_resolve_cells_relation : forall V (R : cell V -> @Model.expr V -> Prop) resolve,
  (forall v, R (Val v) (Model.ELit v)) ->
  (forall i e, resolve i = Some e -> R (Id i) e) ->
  forall k es, dag_resolve_cells resolve k = Some es -> Forall2 R k es.
Proof.
  intros V R resolve Hlit Hid k.
  induction k as [|[i|v] k IH]; intros es Hrun.
  - inversion Hrun. constructor.
  - cbn [dag_resolve_cells] in Hrun.
    destruct (resolve i) as [e|] eqn:Hi; [|discriminate].
    destruct (dag_resolve_cells resolve k) as [rest|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst es. constructor; [now apply Hid |apply IH; reflexivity].
  - cbn [dag_resolve_cells] in Hrun.
    destruct (dag_resolve_cells resolve k) as [rest|] eqn:Hrest; [|discriminate].
    inversion Hrun; subst es. constructor; [apply Hlit |apply IH; reflexivity].
Qed.

(** Present rows turn a successful reverse unfolding into a represented model expression. *)
Lemma dag_unfold_reverse_model : forall V (w : Model.view (V := V)) g c e,
  (forall i, Model.same w i i) ->
  Forall (fun entry => Model.row w (fst (snd entry)) (snd (snd entry))
    (Some (Id (fst entry)))) g ->
  dag_unfold_reverse g c = Some e -> Model.represents w (Id c) e.
Proof.
  intros V w g. induction g as [|[i [f k]] g IH]; intros c e Hsame Hrows Hrun.
  - discriminate.
  - inversion Hrows as [|entry rest Hrow Htail]; subst entry rest.
    cbn [fst snd] in Hrow. cbn [dag_unfold_reverse] in Hrun.
    destruct (Pos.eqb c i) eqn:Hci.
    + apply Pos.eqb_eq in Hci. subst c.
      destruct (dag_resolve_cells (dag_unfold_reverse g) k) as [es|] eqn:Hcells;
        [|discriminate].
      inversion Hrun; subst e. eapply Model.rep_app; [exact Hrow |apply Hsame |].
      eapply dag_resolve_cells_relation; [apply Model.rep_lit | |exact Hcells].
      intros child tree Hchild. exact (IH child tree Hsame Htail Hchild).
    + exact (IH c e Hsame Htail Hrun).
Qed.

(** Successful specification unfolding is sound whenever the certificate rows are present. *)
Lemma dag_unfold_model : forall V (w : Model.view (V := V)) g c e,
  (forall i, Model.same w i i) ->
  Forall (fun entry => Model.row w (fst (snd entry)) (snd (snd entry))
    (Some (Id (fst entry)))) g ->
  dag_unfold g c = Some e -> Model.represents w (Id c) e.
Proof.
  intros V w g c e Hsame Hrows Hrun.
  eapply dag_unfold_reverse_model; [exact Hsame |apply Forall_rev; exact Hrows |exact Hrun].
Qed.

(** Only allocated, canonical identifiers are passed to exact database lookup. *)
Fixpoint dag_check_key {V} (ids : N) (repr : positive -> positive)
    (k : list (cell V)) : bool :=
  match k with
  | [] => true
  | Val _ :: rest => dag_check_key ids repr rest
  | Id i :: rest =>
    if N.leb (Npos i) ids then
      if Pos.eqb i (repr i) then dag_check_key ids repr rest else false
    else false
  end.
TimeFun dag_check_key.

(** A row check compares the database output with the certificate's exact class name. *)
Definition dag_check_row {V} (ids : N) (repr : positive -> positive)
    (lookup : positive -> list (cell V) -> option (option (cell V)))
    (i f : positive) (k : list (cell V)) : bool :=
  if dag_check_key ids repr k then
    match lookup f k with
    | Some (Some (Id j)) => Pos.eqb i j
    | _ => false
    end
  else false.
TimeFun dag_check_row.

(** A successful key check guarantees allocation and canonical identifiers. *)
Lemma dag_check_key_spec : forall V ids repr (k : list (cell V)),
  dag_check_key ids repr k = true ->
  forall i, In (Id i) k -> (Npos i <= ids)%N /\ repr i = i.
Proof.
  intros V ids repr k. induction k as [|[j|v] k IH]; intros Hrun i Hin.
  - contradiction.
  - cbn [dag_check_key] in Hrun.
    destruct (N.leb (Npos j) ids) eqn:Halloc; [|discriminate].
    destruct (Pos.eqb j (repr j)) eqn:Hrepr; [|discriminate].
    destruct Hin as [Heq|Hin].
    + injection Heq as Heq. subst i. split.
      * now apply N.leb_le.
      * symmetry. now apply Pos.eqb_eq.
    + now apply IH.
  - destruct Hin as [Heq|Hin]; [discriminate |]. now apply IH.
Qed.


(** Marking a row adds each identifier child to the needed set. *)
Fixpoint dag_mark_cells {V} (needed : ptrie unit) (k : list (cell V)) : ptrie unit :=
  match k with
  | [] => needed
  | Val _ :: rest => dag_mark_cells needed rest
  | Id i :: rest => dag_mark_cells (PTrieCode.set i tt needed) rest
  end.
TimeFun dag_mark_cells.

(** A backward pass propagates root requirements through earlier children. *)
Fixpoint dag_needed {V} (g : extraction_dag V) (needed : ptrie unit) : ptrie unit :=
  match g with
  | [] => needed
  | (i, (_, k)) :: rest =>
    let later := dag_needed rest needed in
    if dag_seen later i then dag_mark_cells later k else later
  end.
TimeFun dag_needed.

(** Marking children adds exactly the identifier names appearing in the row key. *)
Lemma dag_mark_cells_spec : forall V (k : list (cell V)) needed i,
  dag_seen (dag_mark_cells needed k) i = true <->
    dag_seen needed i = true \/ In (Id i) k.
Proof.
  intros V k. induction k as [|[j|v] k IH]; intros needed i.
  - cbn [dag_mark_cells In]. tauto.
  - cbn [dag_mark_cells]. rewrite IH, dag_seen_set.
    destruct (Pos.eqb i j) eqn:Hij.
    + apply Pos.eqb_eq in Hij. subst i. cbn. intuition.
    + apply Pos.eqb_neq in Hij. cbn. intuition congruence.
  - cbn [dag_mark_cells]. rewrite IH. cbn. intuition congruence.
Qed.

(** Backward marking preserves every incoming requirement. *)
Lemma dag_needed_monotone : forall V (g : extraction_dag V) needed i,
  dag_seen needed i = true -> dag_seen (dag_needed g needed) i = true.
Proof.
  intros V g. induction g as [|[j [f k]] g IH]; intros needed i Hin.
  - exact Hin.
  - cbn [dag_needed]. destruct (dag_seen (dag_needed g needed) j).
    + apply dag_mark_cells_spec. left. now apply IH.
    + now apply IH.
Qed.

(** New requirements always come from a child mentioned by the scanned certificate. *)
Lemma dag_needed_added : forall V (g : extraction_dag V) needed i,
  dag_seen (dag_needed g needed) i = true ->
  dag_seen needed i = true \/
    exists j f k, In (j, (f, k)) g /\ In (Id i) k.
Proof.
  intros V g. induction g as [|[j [f k]] g IH]; intros needed i Hneeded.
  - now left.
  - cbn [dag_needed] in Hneeded.
    destruct (dag_seen (dag_needed g needed) j).
    + apply dag_mark_cells_spec in Hneeded as [Hneeded|Hchild].
      * destruct (IH _ _ Hneeded) as [Hinitial|[j' [f' [k' [Hin Hchild]]]]].
        -- now left.
        -- right. exists j', f', k'. split; [now right |exact Hchild].
      * right. exists j, f, k. split; [now left |exact Hchild].
    + destruct (IH _ _ Hneeded) as [Hinitial|[j' [f' [k' [Hin Hchild]]]]].
      * now left.
      * right. exists j', f', k'. split; [now right |exact Hchild].
Qed.

(** Ordered keys mention only names in the initial prefix or this certificate. *)
Lemma dag_ordered_children : forall V known (g : extraction_dag V),
  dag_ordered_from known g -> forall i f k,
  In (i, (f, k)) g -> forall child, In (Id child) k ->
  In child (known ++ map fst g).
Proof.
  intros V known g. revert known.
  induction g as [|[j [f' k']] g IH]; intros known Hordered i f k Hin child Hchild.
  - contradiction.
  - destruct Hordered as [Hfresh [Hchildren Hordered]].
    destruct Hin as [Heq|Hin].
    + injection Heq as Hji Hf Hk. subst j f' k'.
      apply in_or_app. left. now apply Hchildren.
    + specialize (IH _ Hordered i f k Hin child Hchild).
      cbn [map fst] in *. rewrite !in_app_iff in *. cbn in IH |- *. tauto.
Qed.

(** A certificate prefix inherits the order guarantees of the whole certificate. *)
Lemma dag_ordered_app_left : forall V known (g more : extraction_dag V),
  dag_ordered_from known (g ++ more) -> dag_ordered_from known g.
Proof.
  intros V known g. revert known.
  induction g as [|[i [f k]] g IH]; intros known more Hordered; [exact I |].
  destruct Hordered as [Hfresh [Hchildren Hordered]].
  cbn [dag_ordered_from]. repeat split; try assumption. now apply IH with more.
Qed.

(** Marking a prefix cannot add an identifier that the prefix never names. *)
Lemma dag_needed_fresh : forall V known (g : extraction_dag V) needed i,
  dag_ordered_from known g -> ~ In i (known ++ map fst g) ->
  dag_seen (dag_needed g needed) i = dag_seen needed i.
Proof.
  intros V known g needed i Hordered Hfresh.
  destruct (dag_seen (dag_needed g needed) i) eqn:Hfinal,
    (dag_seen needed i) eqn:Hinitial; try reflexivity.
  - apply dag_needed_added in Hfinal as [Hinitial'|[j [f [k [Hin Hchild]]]]];
      [congruence |].
    exfalso. apply Hfresh. eapply dag_ordered_children; eassumption.
  - pose proof (dag_needed_monotone V g needed i Hinitial) as Hfinal'. congruence.
Qed.

(** Backward marking composes from the suffix into the prefix. *)
Lemma dag_needed_app : forall V (g more : extraction_dag V) needed,
  dag_needed (g ++ more) needed = dag_needed g (dag_needed more needed).
Proof.
  intros V g. induction g as [|[i [f k]] g IH]; intros more needed.
  - reflexivity.
  - cbn [dag_needed app]. now rewrite IH.
Qed.

(** Every marked row in an ordered certificate has all its identifier children marked. *)
Lemma dag_needed_closed : forall V (g : extraction_dag V) needed,
  dag_ordered_from [] g -> forall i f k,
  In (i, (f, k)) g -> dag_seen (dag_needed g needed) i = true ->
  forall child, In (Id child) k -> dag_seen (dag_needed g needed) child = true.
Proof.
  intros V g needed Hordered i f k Hin Hmarked child Hchild.
  apply in_split in Hin as [pre [post Heq]]. subst g.
  pose proof (proj1 (dag_ordered_names V [] _ Hordered)) as Hnodup.
  rewrite map_app in Hnodup. cbn [map fst] in Hnodup.
  pose proof (NoDup_remove_2 (map fst pre) (map fst post) i Hnodup) as Hfresh.
  assert (Hpre : dag_ordered_from [] pre).
  { now apply dag_ordered_app_left with ((i, (f, k)) :: post). }
  rewrite dag_needed_app in Hmarked |- *.
  rewrite (dag_needed_fresh V [] pre _ i Hpre
    ltac:(cbn; intro H; apply Hfresh; apply in_or_app; now left)) in Hmarked.
  cbn [dag_needed] in Hmarked.
  destruct (dag_seen (dag_needed post needed) i) eqn:Hlater; [|congruence].
  apply dag_needed_monotone. cbn [dag_needed]. rewrite Hlater.
  apply dag_mark_cells_spec. now right.
Qed.

(** A property closed under certificate edges is preserved by backward marking. *)
Lemma dag_needed_preserves : forall V (g : extraction_dag V) needed (P : positive -> Prop),
  (forall i f k, In (i, (f, k)) g -> P i -> forall child, In (Id child) k -> P child) ->
  (forall i, dag_seen needed i = true -> P i) ->
  forall i, dag_seen (dag_needed g needed) i = true -> P i.
Proof.
  intros V g. induction g as [|[j [f k]] g IH]; intros needed P Hedges Hinitial i Hmarked.
  - now apply Hinitial.
  - assert (Hlater : forall x, dag_seen (dag_needed g needed) x = true -> P x).
    { apply IH; [|exact Hinitial]. intros x f' k' Hin Hx child Hchild.
      apply (Hedges x f' k' (or_intror Hin) Hx child Hchild). }
    cbn [dag_needed] in Hmarked.
    destruct (dag_seen (dag_needed g needed) j) eqn:Hj.
    + apply dag_mark_cells_spec in Hmarked as [Hmarked|Hchild].
      * now apply Hlater.
      * apply (Hedges j f k (or_introl eq_refl) (Hlater j Hj) i Hchild).
    + now apply Hlater.
Qed.

(** Missing costs have value zero while earlier selected rows populate the table. *)
Definition dag_get_cost (costs : ptrie N) (i : positive) : N :=
  match trie_get i costs with Some n => n | None => 0%N end.
TimeFun dag_get_cost.

(** A constructor reads stored identifier costs and evaluates its literal costs. *)
Fixpoint dag_cost_cells {V} (val_cost : V -> N) (costs : ptrie N)
    (k : list (cell V)) : list N :=
  match k with
  | [] => []
  | Val v :: rest => val_cost v :: dag_cost_cells val_cost costs rest
  | Id i :: rest => dag_get_cost costs i :: dag_cost_cells val_cost costs rest
  end.
TimeFun dag_cost_cells.

(** A selected row records its constructor cost after all its children are available. *)
Definition dag_cost_step {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (needed : ptrie unit) (costs : ptrie N) (entry : positive * extraction_row V) : ptrie N :=
  let '(i, (f, k)) := entry in
  if dag_seen needed i then
    PTrieCode.set i (fn_cost f (dag_cost_cells val_cost costs k)) costs
  else costs.
TimeFun dag_cost_step.

(** A forward pass evaluates only rows marked by the ancestor pass. *)
Fixpoint dag_cost_table {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (needed : ptrie unit) (g : extraction_dag V) (costs : ptrie N) : ptrie N :=
  match g with
  | [] => costs
  | entry :: rest =>
    dag_cost_table fn_cost val_cost needed rest
      (dag_cost_step fn_cost val_cost needed costs entry)
  end.
TimeFun dag_cost_table.

(** The checker validates every entry before evaluating the requested root's ancestors. *)
Definition dag_check {V} (check_row : positive -> positive -> list (cell V) -> bool)
    (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (g : extraction_dag V) (root : positive) : option N :=
  if dag_validate check_row Empty g root then
    let needed := dag_needed g (PTrieCode.set root tt Empty) in
    Some (dag_get_cost (dag_cost_table fn_cost val_cost needed g Empty) root)
  else None.
TimeFun dag_check.

(** Setting a class cost makes that exact cost available. *)
Lemma dag_get_cost_same : forall costs i n,
  dag_get_cost (PTrieCode.set i n costs) i = n.
Proof.
  intros costs i n. unfold dag_get_cost. now rewrite PTrie.get_set_same.
Qed.

(** Setting another class does not change an earlier class cost. *)
Lemma dag_get_cost_other : forall costs i j n, i <> j ->
  dag_get_cost (PTrieCode.set j n costs) i = dag_get_cost costs i.
Proof.
  intros costs i j n Hneq. unfold dag_get_cost. now rewrite PTrie.get_set_other.
Qed.

(** Key costs agree with finite key witnesses whenever all identifier costs do. *)
Lemma dag_cost_cells_witness : forall V fn_cost val_cost costs (pre : extraction_dag V) k,
  (forall i, In (Id i) k -> exists e, dag_represents pre i e /\
    dag_get_cost costs i = expression_cost fn_cost val_cost e) ->
  exists es, dag_cells pre k es /\
    dag_cost_cells val_cost costs k = map (expression_cost fn_cost val_cost) es.
Proof.
  intros V fn_cost val_cost costs pre k. induction k as [|[i|v] k IH]; intro Hchildren.
  - exists []. split; [constructor |reflexivity].
  - destruct (Hchildren i (or_introl eq_refl)) as [e [Hrep Hcost]].
    destruct (IH ltac:(intros child Hin; apply Hchildren; now right)) as [es [Hcells Hcosts]].
    exists (e :: es). split; [now constructor |].
    cbn [dag_cost_cells map]. rewrite Hcost.
    change (expression_cost fn_cost val_cost e :: dag_cost_cells val_cost costs k =
      expression_cost fn_cost val_cost e :: map (expression_cost fn_cost val_cost) es).
    now rewrite Hcosts.
  - destruct (IH ltac:(intros child Hin; apply Hchildren; now right)) as [es [Hcells Hcosts]].
    exists (Model.ELit v :: es). split; [now constructor |].
    cbn [dag_cost_cells map expression_cost].
    change (val_cost v :: dag_cost_cells val_cost costs k =
      val_cost v :: map (expression_cost fn_cost val_cost) es).
    now rewrite Hcosts.
Qed.

(** Selected known names have finite witnesses whose tree costs match their stored costs. *)
Definition dag_cost_witness {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (needed : ptrie unit) (costs : ptrie N) (known : list positive)
    (pre : extraction_dag V) : Prop :=
  forall i, In i known -> dag_seen needed i = true ->
    exists e, dag_represents pre i e /\
      dag_get_cost costs i = expression_cost fn_cost val_cost e.

(** One forward cost step preserves finite cost witnesses for every selected known name. *)
Lemma dag_cost_step_witness : forall V fn_cost val_cost needed costs known
    (pre : extraction_dag V) i f k,
  ~ In i known -> (forall child, In (Id child) k -> In child known) ->
  (dag_seen needed i = true -> forall child, In (Id child) k -> dag_seen needed child = true) ->
  dag_cost_witness fn_cost val_cost needed costs known pre ->
  dag_cost_witness fn_cost val_cost needed
    (dag_cost_step fn_cost val_cost needed costs (i, (f, k)))
    (i :: known) (pre ++ [(i, (f, k))]).
Proof.
  intros V fn_cost val_cost needed costs known pre i f k Hfresh Hchildren Hclosed Hcosts.
  intros child [Hchild|Hchild] Hmarked.
  - subst child. unfold dag_cost_step. rewrite Hmarked.
    destruct (dag_cost_cells_witness V fn_cost val_cost costs pre k
      ltac:(intros j Hin; apply Hcosts; [now apply Hchildren |now apply Hclosed]))
      as [es [Hcells Hvalues]].
    exists (Model.EApp f es). split; [now constructor |].
    rewrite dag_get_cost_same. cbn [expression_cost]. now rewrite Hvalues.
  - destruct (Hcosts child Hchild Hmarked) as [e [Hrep Hvalue]].
    exists e. split; [now apply dag_later |].
    unfold dag_cost_step. destruct (dag_seen needed i); [|exact Hvalue].
    rewrite dag_get_cost_other; [exact Hvalue |]. intro Heq. subst child. contradiction.
Qed.

(** The forward pass maintains the finite-witness invariant across all ordered rows. *)
Lemma dag_cost_table_witness : forall V fn_cost val_cost needed (g : extraction_dag V)
    costs known pre,
  dag_ordered_from known g ->
  (forall i f k, In (i, (f, k)) g -> dag_seen needed i = true ->
    forall child, In (Id child) k -> dag_seen needed child = true) ->
  dag_cost_witness fn_cost val_cost needed costs known pre ->
  dag_cost_witness fn_cost val_cost needed
    (dag_cost_table fn_cost val_cost needed g costs)
    (known ++ map fst g) (pre ++ g).
Proof.
  intros V fn_cost val_cost needed g. induction g as [|[i [f k]] g IH];
    intros costs known pre Hordered Hclosed Hcosts.
  - cbn [dag_cost_table map]. now rewrite !app_nil_r.
  - destruct Hordered as [Hfresh [Hchildren Hordered]].
    pose proof (dag_cost_step_witness V fn_cost val_cost needed costs known pre i f k
      Hfresh Hchildren
      ltac:(intros Hi child Hin; exact (Hclosed i f k (or_introl eq_refl) Hi child Hin))
      Hcosts) as Hnext.
    assert (Htail : forall j f' k', In (j, (f', k')) g -> dag_seen needed j = true ->
      forall child, In (Id child) k' -> dag_seen needed child = true).
    { intros j f' k' Hin Hj child Hchild.
      exact (Hclosed j f' k' (or_intror Hin) Hj child Hchild). }
    specialize (IH _ _ _ Hordered Htail Hnext).
    intros child Hin Hmarked.
    assert (Hin' : In child ((i :: known) ++ map fst g)).
    { cbn [map fst] in Hin. rewrite !in_app_iff in *. cbn in *. tauto. }
    destruct (IH child Hin' Hmarked) as [e [Hrep Hvalue]].
    exists e. split; [rewrite <- app_assoc in Hrep; exact Hrep |exact Hvalue].
Qed.

(** Accepted generic checks report the tree cost of a finite unfolding and certify each row. *)
Lemma dag_check_correct : forall V check_row fn_cost val_cost (g : extraction_dag V) c n,
  dag_check check_row fn_cost val_cost g c = Some n ->
  dag_ordered_from [] g /\
  Forall (fun entry => check_row (fst entry) (fst (snd entry)) (snd (snd entry)) = true) g /\
  exists e, dag_represents g c e /\ dag_unfold g c = Some e /\
    n = expression_cost fn_cost val_cost e.
Proof.
  intros V check_row fn_cost val_cost g c n Hrun. unfold dag_check in Hrun.
  destruct (dag_validate check_row Empty g c) eqn:Hvalid; [|discriminate].
  inversion Hrun; subst n.
  destruct (dag_validate_sound V check_row g Empty c []
    ltac:(intro i; unfold dag_seen; rewrite PTrie.get_empty; cbn;
      split; [discriminate |contradiction]) Hvalid)
    as [Hordered [Hrows Hroot]].
  split; [exact Hordered |]. split; [exact Hrows |].
  pose proof (dag_cost_table_witness V fn_cost val_cost
    (dag_needed g (PTrieCode.set c tt Empty)) g Empty [] [] Hordered
    (dag_needed_closed V g _ Hordered)
    ltac:(intros i Hin; contradiction)) as Hcosts.
  assert (Hmarked : dag_seen (dag_needed g (PTrieCode.set c tt Empty)) c = true).
  { apply dag_needed_monotone. rewrite dag_seen_set, Pos.eqb_refl. reflexivity. }
  destruct (Hcosts c Hroot Hmarked) as [e [Hrep Hvalue]].
  exists e. split; [exact Hrep |]. split; [|exact Hvalue].
  apply dag_unfold_complete; [exact (proj1 (dag_ordered_names V [] g Hordered)) |exact Hrep].
Qed.

(** Key syntax charges each cell's encoded width and its list cell. *)
Definition dag_key_bits {V} (encode : V -> positive) (k : list (cell V)) : nat :=
  fold_right (fun c n => cell_bits encode c + 1 + n) 0 k.

(** Key syntax always pays for the key's length. *)
Lemma dag_key_length : forall V encode (k : list (cell V)),
  length k <= dag_key_bits encode k.
Proof.
  intros V encode k. induction k as [|c k IH]; unfold dag_key_bits in *;
    cbn [length fold_right] in *; lia.
Qed.

(** Uniformly bounded cells turn encoded key size into a length bound. *)
Lemma dag_key_uniform : forall V encode (k : list (cell V)) w,
  (forall c, In c k -> cell_bits encode c <= w) ->
  dag_key_bits encode k <= length k * (w + 1).
Proof.
  intros V encode k. induction k as [|c k IH]; intros w Hwidth.
  - reflexivity.
  - pose proof (Hwidth c (or_introl eq_refl)) as Hhead.
    specialize (IH w (fun d Hd => Hwidth d (or_intror Hd))).
    unfold dag_key_bits in *. cbn [fold_right length]. nia.
Qed.

(** Row work counts one constructor and its argument occurrences per certificate entry. *)
Definition dag_row_work {V} (g : extraction_dag V) : nat :=
  fold_right (fun entry n => length (snd (snd entry)) + 1 + n) 0 g.

(** A uniform key-length bound controls the complete certificate's row work. *)
Lemma dag_row_work_length : forall V (g : extraction_dag V) a,
  (forall i f k, In (i, (f, k)) g -> length k <= a) ->
  dag_row_work g <= length g * (a + 1).
Proof.
  intros V g. induction g as [|[i [f k]] g IH]; intros a Harity.
  - reflexivity.
  - pose proof (Harity i f k (or_introl eq_refl)) as Hhead.
    specialize (IH a (fun j h l Hl => Harity j h l (or_intror Hl))).
    unfold dag_row_work in *. cbn [fold_right fst snd length]. nia.
Qed.

(** Row work pays for encoded certificate syntax once at a uniform stored width. *)
Lemma dag_certificate_uniform : forall V encode (g : extraction_dag V) w,
  (forall i f k, In (i, (f, k)) g ->
    Pos.size_nat i <= w /\ Pos.size_nat f <= w /\
    forall c, In c k -> cell_bits encode c <= w) ->
  cert_size encode g <= 3 * dag_row_work g * (w + 1).
Proof.
  intros V encode g. induction g as [|[i [f k]] g IH]; intros w Hwidth.
  - reflexivity.
  - destruct (Hwidth i f k (or_introl eq_refl)) as [Hi [Hf Hcells]].
    pose proof (dag_key_uniform V encode k w Hcells) as Hkey.
    specialize (IH w (fun j h l Hl => Hwidth j h l (or_intror Hl))).
    unfold cert_size, dag_row_work, dag_key_bits in *.
    cbn [fold_right fst snd]. nia.
Qed.

(** Membership checks follow one trie path for the queried identifier. *)
Lemma T_dag_seen_le : forall seen i,
  (T_dag_seen seen i <= 8 * N.of_nat (Pos.size_nat i + 1))%N.
Proof.
  intros seen i. pose proof (PTrieT.T_trie_get_le unit i seen) as Hget.
  time_unfold @T_dag_seen. time_simpl. time_cbn.
  destruct (trie_get i seen); rewrite !Nat2N.inj_add; lia.
Qed.

(** Cost lookup follows one trie path without inspecting the stored number. *)
Lemma T_dag_get_cost_le : forall costs i,
  (T_dag_get_cost costs i <= 8 * N.of_nat (Pos.size_nat i + 1))%N.
Proof.
  intros costs i. pose proof (PTrieT.T_trie_get_le N i costs) as Hget.
  time_unfold @T_dag_get_cost. time_simpl. time_cbn.
  destruct (trie_get i costs); rewrite !Nat2N.inj_add; lia.
Qed.

(** Child membership checks pay only for the identifier cells that they read. *)
Lemma T_dag_children_seen_le : forall V encode (k : list (cell V)) seen,
  (T_dag_children_seen seen k <= 32 * N.of_nat (dag_key_bits encode k + 1))%N.
Proof.
  intros V encode k. induction k as [|[i|v] k IH]; intro seen.
  - unfold dag_key_bits. time_step.
  - pose proof (T_dag_seen_le seen i) as Hseen. specialize (IH seen).
    unfold dag_key_bits in *. time_unfold @T_dag_children_seen. time_simpl. time_cbn.
    cbn [fold_right cell_bits Pos.size_nat]. rewrite !Nat2N.inj_add in *. lia.
  - specialize (IH seen). unfold dag_key_bits in *.
    time_unfold @T_dag_children_seen. time_simpl. time_cbn.
    cbn [fold_right cell_bits Pos.size_nat]. rewrite !Nat2N.inj_add in *. lia.
Qed.

(** Marking a key pays for each inserted identifier's encoded width. *)
Lemma T_dag_mark_cells_le : forall V encode (k : list (cell V)) needed,
  (T_dag_mark_cells needed k <= 16 * (PTrieT.c_trie + 1) *
    N.of_nat (dag_key_bits encode k + 1))%N.
Proof.
  intros V encode k. induction k as [|[i|v] k IH]; intro needed.
  - unfold dag_key_bits. time_step.
  - pose proof (PTrieT.T_set_le unit i tt needed) as Hset.
    change (PTrieCode.T_set i tt needed <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    specialize (IH (PTrieCode.set i tt needed)). unfold dag_key_bits in *.
    time_unfold @T_dag_mark_cells. time_simpl. time_cbn.
    cbn [fold_right cell_bits Pos.size_nat]. rewrite !Nat2N.inj_add in *.
    unfold PTrieT.c_trie in *. lia.
  - specialize (IH needed). unfold dag_key_bits in *.
    time_unfold @T_dag_mark_cells. time_simpl. time_cbn.
    cbn [fold_right cell_bits Pos.size_nat]. rewrite !Nat2N.inj_add in *.
    unfold PTrieT.c_trie in *. lia.
Qed.

(** The backward ancestor pass is linear in the certificate's encoded syntax. *)
Lemma T_dag_needed_le : forall V encode (g : extraction_dag V) needed,
  (T_dag_needed g needed <= 32 * (PTrieT.c_trie + 1) *
    N.of_nat (cert_size encode g + 1))%N.
Proof.
  intros V encode g. induction g as [|[i [f k]] g IH]; intro needed.
  - unfold cert_size. time_step.
  - specialize (IH needed).
    pose proof (T_dag_seen_le (dag_needed g needed) i) as Hseen.
    pose proof (T_dag_mark_cells_le V encode k (dag_needed g needed)) as Hmark.
    time_unfold @T_dag_needed. time_simpl. time_cbn.
    destruct (dag_seen (dag_needed g needed) i);
      unfold cert_size, dag_key_bits in *;
      cbn [fold_right fst snd] in *; rewrite !Nat2N.inj_add in *;
      unfold PTrieT.c_trie in *; lia.
Qed.

(** Canonical-key checking charges comparisons to the supplied identifiers. *)
Lemma T_dag_check_key_le : forall V encode ids repr T_repr (k : list (cell V)) b,
  (forall i, (Npos i <= ids)%N -> (T_repr i <= b)%N) ->
  (T_dag_check_key ids repr T_repr k <=
    32 * (b + 1) * N.of_nat (dag_key_bits encode k + 1))%N.
Proof.
  intros V encode ids repr T_repr k. induction k as [|[i|v] k IH]; intros b Hrepr.
  - unfold dag_key_bits. time_step.
  - specialize (IH b Hrepr).
    pose proof (N.T_leb_le (Npos i) ids) as Hleb.
    pose proof (Pos.T_eqb_le i (repr i)) as Heqb.
    time_unfold @T_dag_check_key. time_simpl. time_cbn.
    destruct (N.leb (Npos i) ids) eqn:Halloc.
    + pose proof (Hrepr i (proj1 (N.leb_le _ _) Halloc)) as Hfind.
      destruct (Pos.eqb i (repr i)); unfold dag_key_bits in *;
        cbn [fold_right cell_bits Pos.size_nat N.size_nat] in *;
        rewrite !Nat2N.inj_add in *; nia.
    + unfold dag_key_bits in *.
      cbn [fold_right cell_bits Pos.size_nat N.size_nat] in *;
        rewrite !Nat2N.inj_add in *; nia.
  - specialize (IH b Hrepr). unfold dag_key_bits in *.
    time_unfold @T_dag_check_key. time_simpl. time_cbn.
    cbn [fold_right cell_bits Pos.size_nat] in *; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** A stored key pays once per identifier for its callback and its encoded width. *)
Lemma T_dag_check_key_additive : forall V ids repr T_repr (k : list (cell V)) b w,
  (forall i, (Npos i <= ids)%N -> (T_repr i <= b)%N) ->
  (forall i, In (Id i) k -> Pos.size_nat i <= w) ->
  (T_dag_check_key ids repr T_repr k <=
    32 * (b + N.of_nat (w + 1)) * N.of_nat (length k + 1))%N.
Proof.
  intros V ids repr T_repr k. induction k as [|[i|v] k IH]; intros b w Hrepr Hwidth.
  - time_unfold @T_dag_check_key. time_simpl. time_cbn. cbn [length].
    rewrite Nat2N.inj_add. nia.
  - pose proof (Hwidth i (or_introl eq_refl)) as Hbit.
    specialize (IH b w Hrepr (fun j Hj => Hwidth j (or_intror Hj))).
    pose proof (N.T_leb_le (Npos i) ids) as Hleb.
    pose proof (Pos.T_eqb_le i (repr i)) as Heqb.
    time_unfold @T_dag_check_key. time_simpl. time_cbn.
    destruct (N.leb (Npos i) ids) eqn:Halloc.
    + pose proof (Hrepr i (proj1 (N.leb_le _ _) Halloc)) as Hfind.
      destruct (Pos.eqb i (repr i)); cbn [length N.size_nat] in *;
        rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *; nia.
    + cbn [length N.size_nat] in *.
      rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *. nia.
  - specialize (IH b w Hrepr (fun j Hj => Hwidth j (or_intror Hj))).
    time_unfold @T_dag_check_key. time_simpl. time_cbn.
    cbn [length]. rewrite !Nat2N.inj_add, ?Nat2N.inj_succ in *. nia.
Qed.

(** A cost-key traversal is the pointwise map of identifier and literal costs. *)
Lemma dag_cost_cells_map : forall V val_cost costs (k : list (cell V)),
  dag_cost_cells val_cost costs k =
    map (fun c => match c with Id i => dag_get_cost costs i | Val v => val_cost v end) k.
Proof.
  intros V val_cost costs k. induction k as [|[i|v] k IH];
    cbn [dag_cost_cells map]; now try rewrite IH.
Qed.

(** Every key cell contributes its cost to the constructor's child-cost list. *)
Lemma dag_cost_cells_member : forall V val_cost costs (k : list (cell V)) c,
  In c k ->
  In (match c with Id i => dag_get_cost costs i | Val v => val_cost v end)
    (dag_cost_cells val_cost costs k).
Proof.
  intros V val_cost costs k c Hin. rewrite dag_cost_cells_map.
  apply in_map_iff. exists c. now split.
Qed.

(** Equal identifier costs give equal key-cost lists. *)
Lemma dag_cost_cells_ext : forall V val_cost left right (k : list (cell V)),
  (forall i, In (Id i) k -> dag_get_cost left i = dag_get_cost right i) ->
  dag_cost_cells val_cost left k = dag_cost_cells val_cost right k.
Proof.
  intros V val_cost left right k Hsame. rewrite !dag_cost_cells_map.
  apply map_ext_in. intros [i|v] Hin; [now apply Hsame |reflexivity].
Qed.

(** Forward cost traversal composes across a certificate split. *)
Lemma dag_cost_table_app : forall V fn_cost val_cost needed (g more : extraction_dag V) costs,
  dag_cost_table fn_cost val_cost needed (g ++ more) costs =
  dag_cost_table fn_cost val_cost needed more
    (dag_cost_table fn_cost val_cost needed g costs).
Proof.
  intros V fn_cost val_cost needed g. induction g as [|entry g IH]; intros more costs.
  - reflexivity.
  - cbn [dag_cost_table app]. now rewrite IH.
Qed.

(** Traversing rows with other names preserves an existing class cost. *)
Lemma dag_cost_table_fresh : forall V fn_cost val_cost needed (g : extraction_dag V) costs i,
  ~ In i (map fst g) ->
  dag_get_cost (dag_cost_table fn_cost val_cost needed g costs) i = dag_get_cost costs i.
Proof.
  intros V fn_cost val_cost needed g. induction g as [|[j [f k]] g IH]; intros costs i Hfresh.
  - reflexivity.
  - cbn [dag_cost_table]. rewrite IH by (intro Hin; apply Hfresh; now right).
    unfold dag_cost_step. destruct (dag_seen needed j); [|reflexivity].
    apply dag_get_cost_other. intro Heq. subst i. apply Hfresh. now left.
Qed.

(** Distinct names in concatenated lists cannot occur on both sides of the split. *)
Lemma dag_nodup_disjoint : forall A (left right : list A), NoDup (left ++ right) ->
  forall i, In i left -> ~ In i right.
Proof.
  intros A left right Hnodup i Hleft Hright.
  apply in_split in Hleft as [pre [post Heq]]. subst left.
  rewrite <- app_assoc in Hnodup.
  pose proof (NoDup_remove_2 pre (post ++ right) i Hnodup) as Hfresh.
  apply Hfresh. apply in_or_app. right. apply in_or_app. now right.
Qed.

(** All key costs are final when an ordered row is evaluated. *)
Lemma dag_cost_table_key_stable : forall V fn_cost val_cost needed
    (pre : extraction_dag V) i f k post costs,
  dag_ordered_from [] (pre ++ (i, (f, k)) :: post) ->
  dag_cost_cells val_cost
    (dag_cost_table fn_cost val_cost needed (pre ++ (i, (f, k)) :: post) costs) k =
  dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed pre costs) k.
Proof.
  intros V fn_cost val_cost needed pre i f k post costs Hordered.
  pose proof (proj1 (dag_ordered_names V [] _ Hordered)) as Hnodup.
  rewrite map_app in Hnodup. rewrite dag_cost_table_app.
  apply dag_cost_cells_ext. intros child Hchild. apply dag_cost_table_fresh.
  apply (dag_nodup_disjoint positive _ _ Hnodup child).
  exact (dag_ordered_prefix V [] _ Hordered pre i f k post eq_refl child Hchild).
Qed.

(** Every selected row satisfies its constructor-cost equation in the final table. *)
Lemma dag_cost_table_row : forall V fn_cost val_cost needed (g : extraction_dag V) costs i f k,
  dag_ordered_from [] g -> In (i, (f, k)) g -> dag_seen needed i = true ->
  dag_get_cost (dag_cost_table fn_cost val_cost needed g costs) i =
  fn_cost f (dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed g costs) k).
Proof.
  intros V fn_cost val_cost needed g costs i f k Hordered Hin Hmarked.
  apply in_split in Hin as [pre [post Heq]]. subst g.
  pose proof (proj1 (dag_ordered_names V [] _ Hordered)) as Hnodup.
  rewrite map_app in Hnodup. cbn [map fst] in Hnodup.
  pose proof (NoDup_remove_2 (map fst pre) (map fst post) i Hnodup) as Hfresh.
  pose proof (dag_cost_table_key_stable V fn_cost val_cost needed pre i f k post costs Hordered)
    as Hstable.
  transitivity (fn_cost f
    (dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed pre costs) k)).
  - rewrite dag_cost_table_app. cbn [dag_cost_table].
    rewrite dag_cost_table_fresh by (intro Hin; apply Hfresh; apply in_or_app; now right).
    unfold dag_cost_step. now rewrite Hmarked, dag_get_cost_same.
  - f_equal. symmetry. exact Hstable.
Qed.

(** Every marked class costs at most the requested root when constructors bound their children. *)
Lemma dag_cost_root_bound : forall V fn_cost val_cost,
  (forall f cs n, In n cs -> (n <= fn_cost f cs)%N) ->
  forall (g : extraction_dag V) c, dag_ordered_from [] g ->
  let needed := dag_needed g (PTrieCode.set c tt Empty) in
  let costs := dag_cost_table fn_cost val_cost needed g Empty in
  forall i, dag_seen needed i = true -> (dag_get_cost costs i <= dag_get_cost costs c)%N.
Proof.
  intros V fn_cost val_cost Hsuper g c Hordered needed costs i Hmarked.
  assert (Hroot : dag_seen needed c = true).
  { unfold needed. apply dag_needed_monotone. rewrite dag_seen_set, Pos.eqb_refl.
    reflexivity. }
  set (P := fun j => dag_seen needed j = true /\
    (dag_get_cost costs j <= dag_get_cost costs c)%N).
  assert (Hedges : forall j f k, In (j, (f, k)) g -> P j ->
    forall child, In (Id child) k -> P child).
  { intros j f k Hin [Hj Hbound] child Hchild. split.
    - exact (dag_needed_closed V g _ Hordered j f k Hin Hj child Hchild).
    - eapply N.le_trans; [|exact Hbound]. unfold costs.
      rewrite (dag_cost_table_row V fn_cost val_cost needed g Empty j f k Hordered Hin Hj).
      apply Hsuper. exact (dag_cost_cells_member V val_cost _ k (Id child) Hchild). }
  assert (Hinitial : forall j, dag_seen (PTrieCode.set c tt Empty) j = true -> P j).
  { intros j Hj. rewrite dag_seen_set in Hj. destruct (Pos.eqb j c) eqn:Hjc.
    - apply Pos.eqb_eq in Hjc. subst j. split; [exact Hroot |apply N.le_refl].
    - unfold dag_seen in Hj. rewrite PTrie.get_empty in Hj. discriminate. }
  exact (proj2 (dag_needed_preserves V g _ P Hedges Hinitial i Hmarked)).
Qed.

(** Literal and identifier child costs of selected rows are bounded by the root cost. *)
Lemma dag_cost_root_cell_bound : forall V fn_cost val_cost,
  (forall f cs n, In n cs -> (n <= fn_cost f cs)%N) ->
  forall (g : extraction_dag V) c, dag_ordered_from [] g ->
  let needed := dag_needed g (PTrieCode.set c tt Empty) in
  let costs := dag_cost_table fn_cost val_cost needed g Empty in
  forall i f k, In (i, (f, k)) g -> dag_seen needed i = true ->
  forall cell, In cell k ->
  (match cell with Id child => dag_get_cost costs child | Val v => val_cost v end <=
    dag_get_cost costs c)%N.
Proof.
  intros V fn_cost val_cost Hsuper g c Hordered needed costs i f k Hin Hmarked cell Hcell.
  eapply N.le_trans;
    [|exact (dag_cost_root_bound V fn_cost val_cost Hsuper g c Hordered i Hmarked)].
  change (match cell with Id child => dag_get_cost costs child | Val v => val_cost v end <=
    dag_get_cost costs i)%N.
  unfold costs. rewrite (dag_cost_table_row V fn_cost val_cost needed g Empty i f k
    Hordered Hin Hmarked).
  apply Hsuper. exact (dag_cost_cells_member V val_cost _ k cell Hcell).
Qed.

(** Binary natural width is monotone in the represented number. *)
Lemma dag_cost_size_mono : forall a b, (a <= b)%N -> N.size_nat a <= N.size_nat b.
Proof.
  intros [|a] [|b] Hle; cbn [N.size_nat]; try lia.
  rewrite !inventory_positive_width. apply Nat.add_le_mono_r, Nat.log2_le_mono. lia.
Qed.

(** A pointwise numerical bound also bounds the largest child-cost width. *)
Lemma dag_cost_width_le : forall cs n,
  (forall c, In c cs -> (c <= n)%N) ->
  fold_right (fun c w => Nat.max (N.size_nat c) w) 0 cs <= N.size_nat n.
Proof.
  induction cs as [|c cs IH]; intros n Hbound; [cbn; lia |].
  cbn [fold_right]. apply Nat.max_lub.
  - apply dag_cost_size_mono, Hbound. now left.
  - apply IH. intros value Hin. apply Hbound. now right.
Qed.

(** At each selected row, the live child-cost widths fit the final root's width. *)
Lemma dag_cost_prefix_width : forall V fn_cost val_cost,
  (forall f cs n, In n cs -> (n <= fn_cost f cs)%N) ->
  forall (g pre : extraction_dag V) c i f k post,
  dag_ordered_from [] g -> g = pre ++ (i, (f, k)) :: post ->
  let needed := dag_needed g (PTrieCode.set c tt Empty) in
  dag_seen needed i = true ->
  fold_right (fun n w => Nat.max (N.size_nat n) w) 0
    (dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed pre Empty) k) <=
  N.size_nat (dag_get_cost (dag_cost_table fn_cost val_cost needed g Empty) c).
Proof.
  intros V fn_cost val_cost Hsuper g pre c i f k post Hordered Heq needed Hmarked.
  assert (Hstable :
    dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed pre Empty) k =
    dag_cost_cells val_cost (dag_cost_table fn_cost val_cost needed g Empty) k).
  { symmetry. subst g. now apply dag_cost_table_key_stable. }
  apply dag_cost_width_le. intros n Hin. rewrite Hstable, dag_cost_cells_map in Hin.
  apply in_map_iff in Hin as [cell [Hvalue Hcell]]. subst n.
  apply (dag_cost_root_cell_bound V fn_cost val_cost Hsuper g c Hordered i f k);
    [rewrite Heq; apply in_or_app; right; now left |exact Hmarked |exact Hcell].
Qed.

(** Row validation adds one key check, one lookup and one exact output comparison. *)
Lemma T_dag_check_row_le : forall V encode ids repr T_repr lookup T_lookup
    i f (k : list (cell V)) b,
  (forall j, (Npos j <= ids)%N -> (T_repr j <= b)%N) ->
  (T_lookup f k <= b * N.of_nat (dag_key_bits encode k + 1))%N ->
  (T_dag_check_row ids repr T_repr lookup T_lookup i f k <=
    64 * (b + 1) * N.of_nat (Pos.size_nat i + dag_key_bits encode k + 1))%N.
Proof.
  intros V encode ids repr T_repr lookup T_lookup i f k b Hrepr Hlookup.
  pose proof (T_dag_check_key_le V encode ids repr T_repr k b Hrepr) as Hkey.
  time_unfold @T_dag_check_row. time_simpl. time_cbn.
  destruct (dag_check_key ids repr k); [destruct (lookup f k) as [[[j|v]|]|] |];
    try pose proof (Pos.T_eqb_le i j);
    rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Stored-row validation adds callback and identifier budgets without multiplying them. *)
Lemma T_dag_check_row_additive : forall V ids repr T_repr lookup T_lookup
    i f (k : list (cell V)) b w,
  (forall j, (Npos j <= ids)%N -> (T_repr j <= b)%N) ->
  (T_lookup f k <= b * N.of_nat (length k + 1))%N ->
  Pos.size_nat i <= w ->
  (forall j, In (Id j) k -> Pos.size_nat j <= w) ->
  (T_dag_check_row ids repr T_repr lookup T_lookup i f k <=
    64 * (b + N.of_nat (w + 1)) * N.of_nat (length k + 1))%N.
Proof.
  intros V ids repr T_repr lookup T_lookup i f k b w Hrepr Hlookup Hi Hwidth.
  pose proof (T_dag_check_key_additive V ids repr T_repr k b w Hrepr Hwidth) as Hkey.
  time_unfold @T_dag_check_row. time_simpl. time_cbn.
  destruct (dag_check_key ids repr k); [destruct (lookup f k) as [[[j|v]|]|] |];
    try pose proof (Pos.T_eqb_le i j);
    rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Full validation is linear in syntax when each row check has a linear bound. *)
Lemma T_dag_validate_le : forall V encode check_row T_check_row b,
  (forall i f (k : list (cell V)),
    (T_check_row i f k <= b *
      N.of_nat (Pos.size_nat i + Pos.size_nat f + dag_key_bits encode k + 1))%N) ->
  forall g seen root,
  (T_dag_validate check_row T_check_row seen g root <=
    64 * (PTrieT.c_trie + b + 1) *
    N.of_nat (cert_size encode g + Pos.size_nat root + 1))%N.
Proof.
  intros V encode check_row T_check_row b Hrow g.
  induction g as [|[i [f k]] g IH]; intros seen root.
  - pose proof (T_dag_seen_le seen root) as Hseen. unfold cert_size.
    time_unfold @T_dag_validate. time_simpl. time_cbn.
    rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. nia.
  - pose proof (T_dag_seen_le seen i) as Hseen.
    pose proof (T_dag_children_seen_le V encode k seen) as Hchildren.
    pose proof (Hrow i f k) as Hcheck.
    pose proof (PTrieT.T_set_le unit i tt seen) as Hset.
    change (PTrieCode.T_set i tt seen <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    specialize (IH (PTrieCode.set i tt seen) root).
    time_unfold @T_dag_validate. time_simpl. time_cbn.
    destruct (dag_seen seen i); [|destruct (dag_children_seen seen k);
      [destruct (check_row i f k) |]];
      unfold cert_size, dag_key_bits in *; cbn [fold_right fst snd] in *;
      rewrite !Nat2N.inj_add in *; unfold PTrieT.c_trie in *; nia.
Qed.

(** Stored-row validation sums row work and charges the common identifier width once. *)

(** One row's scalar charges fit the additive validation allowance. *)
Lemma dag_validate_row_budget : forall t b u l seen children checked inserted : N,
  (1 <= u)%N -> (1 <= l)%N -> (seen <= 8 * u)%N ->
  (children <= 32 * l * u)%N -> (checked <= b * l)%N -> (inserted <= t * u)%N ->
  (1 + seen + children + checked + inserted <= 128 * (t * u + b + u) * l)%N.
Proof.
  intros t b u l seen children checked inserted Hu Hl Hseen Hchildren Hchecked Hinserted.
  assert (Hscale : (t * u + 9 * u <= (t * u + 9 * u) * l)%N).
  { rewrite <- (N.mul_1_r (t * u + 9 * u)) at 1.
    apply N.mul_le_mono_l. exact Hl. }
  eapply N.le_trans with (m := ((t * u + 9 * u) * l + 32 * l * u + b * l)%N).
  - lia.
  - replace ((t * u + 9 * u) * l + 32 * l * u + b * l)%N with
      ((t * u + b + 41 * u) * l)%N by ring.
    apply N.mul_le_mono_r. lia.
Qed.

(** Uniform row clocks add over the certificate without a second identifier-width factor. *)
Lemma T_dag_validate_rows_le : forall V encode check_row T_check_row b w
    (g : extraction_dag V) seen root,
  (forall i f k, In (i, (f, k)) g ->
    (T_check_row i f k <= b * N.of_nat (length k + 1))%N) ->
  (forall i f k, In (i, (f, k)) g -> Pos.size_nat i <= w /\
    forall c, In c k -> cell_bits encode c <= w) ->
  (T_dag_validate check_row T_check_row seen g root <=
    128 * (PTrieT.c_trie * N.of_nat (w + 1) + b + N.of_nat (w + 1)) *
      N.of_nat (dag_row_work g + 1) + 8 * N.of_nat (Pos.size_nat root + 1))%N.
Proof.
  intros V encode check_row T_check_row b w g.
  induction g as [|[i [f k]] g IH]; intros seen root Hrow Hwidth.
  - pose proof (T_dag_seen_le seen root) as Hseen.
    time_unfold @T_dag_validate. time_simpl. time_cbn.
    unfold dag_row_work. cbn [fold_right]. rewrite Nat2N.inj_add. nia.
  - pose proof (Hrow i f k (or_introl eq_refl)) as Hcheck.
    destruct (Hwidth i f k (or_introl eq_refl)) as [Hi Hcells].
    pose proof (T_dag_seen_le seen i) as Hseen.
    pose proof (T_dag_children_seen_le V encode k seen) as Hchildren.
    pose proof (dag_key_uniform V encode k w Hcells) as Hkey.
    assert (Hsyntax : (N.of_nat (dag_key_bits encode k + 1) <=
      N.of_nat (length k + 1) * N.of_nat (w + 1))%N).
    { rewrite <- Nat2N.inj_mul. clear - Hkey. nia. }
    pose proof (PTrieT.T_set_le unit i tt seen) as Hset.
    change (PTrieCode.T_set i tt seen <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    specialize (IH (PTrieCode.set i tt seen) root
      (fun j h l Hl => Hrow j h l (or_intror Hl))
      (fun j h l Hl => Hwidth j h l (or_intror Hl))).
    assert (Hseen' : (T_dag_seen seen i <= 8 * N.of_nat (w + 1))%N).
    { eapply N.le_trans; [exact Hseen |]. apply N.mul_le_mono_l. lia. }
    assert (Hchildren' : (T_dag_children_seen seen k <=
      32 * N.of_nat (length k + 1) * N.of_nat (w + 1))%N).
    { eapply N.le_trans; [exact Hchildren |]. rewrite <- N.mul_assoc.
      apply N.mul_le_mono_l. exact Hsyntax. }
    assert (Hset' : (PTrieCode.T_set i tt seen <=
      PTrieT.c_trie * N.of_nat (w + 1))%N).
    { eapply N.le_trans; [exact Hset |]. apply N.mul_le_mono_l. lia. }
    pose proof (dag_validate_row_budget PTrieT.c_trie b (N.of_nat (w + 1))
      (N.of_nat (length k + 1)) _ _ _ _ ltac:(lia) ltac:(lia)
      Hseen' Hchildren' Hcheck Hset') as Hbudget.
    clear Hrow Hwidth Hi Hcells Hkey Hsyntax Hseen Hchildren Hset Hcheck
      Hseen' Hchildren' Hset'.
    set (budget := (128 * (PTrieT.c_trie * N.of_nat (w + 1) + b +
      N.of_nat (w + 1)))%N) in *. clearbody budget.
    replace (dag_row_work ((i, (f, k)) :: g) + 1) with
      ((length k + 1) + (dag_row_work g + 1)) by
      (unfold dag_row_work; cbn [fold_right fst snd]; lia).
    rewrite Nat2N.inj_add, N.mul_add_distr_l.
    time_unfold @T_dag_validate. time_simpl. time_cbn.
    destruct (dag_seen seen i); [|destruct (dag_children_seen seen k);
      [destruct (check_row i f k) |]];
      unfold dag_row_work in *; rewrite !Nat2N.inj_add in *;
      rewrite !N.mul_add_distr_l in *; lia.
Qed.

(** Reading child costs pays for their identifiers and the encoded literals. *)
Lemma T_dag_cost_cells_le : forall V encode val_cost T_val_cost b,
  (forall v, (T_val_cost v <= b * N.of_nat (Pos.size_nat (encode v) + 1))%N) ->
  forall (k : list (cell V)) costs,
  (T_dag_cost_cells val_cost T_val_cost costs k <=
    32 * (b + 1) * N.of_nat (dag_key_bits encode k + 1))%N.
Proof.
  intros V encode val_cost T_val_cost b Hval k. induction k as [|[i|v] k IH]; intro costs.
  - unfold dag_key_bits. time_step.
  - pose proof (T_dag_get_cost_le costs i) as Hget. specialize (IH costs).
    time_unfold @T_dag_cost_cells. time_simpl. time_cbn.
    unfold dag_key_bits in *; cbn [fold_right cell_bits Pos.size_nat] in *;
      rewrite !Nat2N.inj_add in *; nia.
  - pose proof (Hval v) as Hliteral. specialize (IH costs).
    time_unfold @T_dag_cost_cells. time_simpl. time_cbn.
    unfold dag_key_bits in *; cbn [fold_right cell_bits Pos.size_nat] in *;
      rewrite !Nat2N.inj_add in *; nia.
Qed.

(** A selected constructor step pays for syntax and the bound on its child-cost widths. *)
Lemma T_dag_cost_step_le : forall V encode fn_cost T_fn_cost val_cost T_val_cost b,
  (forall f cs, (T_fn_cost f cs <= b * N.of_nat (length cs + 1) *
    N.of_nat (fold_right (fun n w => Nat.max (N.size_nat n) w) 0%nat cs + 1))%N) ->
  (forall v, (T_val_cost v <= b * N.of_nat (Pos.size_nat (encode v) + 1))%N) ->
  forall needed costs i f (k : list (cell V)) w,
  (dag_seen needed i = true ->
    fold_right (fun n width => Nat.max (N.size_nat n) width) 0
      (dag_cost_cells val_cost costs k) <= w) ->
  (T_dag_cost_step fn_cost T_fn_cost val_cost T_val_cost needed costs (i, (f, k)) <=
    128 * (PTrieT.c_trie + b + 1) *
    N.of_nat (Pos.size_nat i + Pos.size_nat f + dag_key_bits encode k + 1) *
    N.of_nat (w + 1))%N.
Proof.
  intros V encode fn_cost T_fn_cost val_cost T_val_cost b Hfn Hval
    needed costs i f k w Hwidth.
  pose proof (T_dag_cost_cells_le V encode val_cost T_val_cost b Hval k costs) as Hcells.
  pose proof (T_dag_seen_le needed i) as Hseen.
  pose proof (PTrieT.T_set_le N i (fn_cost f (dag_cost_cells val_cost costs k)) costs) as Hset.
  change (PTrieCode.T_set i (fn_cost f (dag_cost_cells val_cost costs k)) costs <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
  time_unfold @T_dag_cost_step. time_simpl. time_cbn.
  destruct (dag_seen needed i) eqn:Hmarked.
  - specialize (Hwidth eq_refl).
    pose proof (Hfn f (dag_cost_cells val_cost costs k)) as Hfunction.
    assert (Hlength : length (dag_cost_cells val_cost costs k) = length k).
    { rewrite dag_cost_cells_map, length_map. reflexivity. }
    rewrite Hlength in Hfunction.
    pose proof (dag_key_length V encode k) as Hkey.
    assert (Hfunction' : (T_fn_cost f (dag_cost_cells val_cost costs k) <=
      b * N.of_nat (dag_key_bits encode k + 1) * N.of_nat (w + 1))%N).
    { eapply N.le_trans; [exact Hfunction |]. apply N.mul_le_mono.
      - apply N.mul_le_mono_l. lia.
      - lia. }
    rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. nia.
  - rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. nia.
Qed.

(** Every suffix of the selective cost pass is funded by syntax and the final root width. *)
Lemma T_dag_cost_table_prefix_le : forall V encode fn_cost T_fn_cost val_cost T_val_cost b,
  (forall f cs n, In n cs -> (n <= fn_cost f cs)%N) ->
  (forall f cs, (T_fn_cost f cs <= b * N.of_nat (length cs + 1) *
    N.of_nat (fold_right (fun n w => Nat.max (N.size_nat n) w) 0%nat cs + 1))%N) ->
  (forall v, (T_val_cost v <= b * N.of_nat (Pos.size_nat (encode v) + 1))%N) ->
  forall (g : extraction_dag V) c, dag_ordered_from [] g ->
  let needed := dag_needed g (PTrieCode.set c tt Empty) in
  let w := N.size_nat (dag_get_cost (dag_cost_table fn_cost val_cost needed g Empty) c) in
  forall remaining pre, g = pre ++ remaining ->
  (T_dag_cost_table fn_cost T_fn_cost val_cost T_val_cost needed remaining
      (dag_cost_table fn_cost val_cost needed pre Empty) <=
    256 * (PTrieT.c_trie + b + 1) *
    N.of_nat (cert_size encode remaining + 1) * N.of_nat (w + 1))%N.
Proof.
  intros V encode fn_cost T_fn_cost val_cost T_val_cost b Hsuper Hfn Hval
    g c Hordered needed w remaining.
  induction remaining as [|[i [f k]] remaining IH]; intros pre Heq.
  - time_unfold @T_dag_cost_table. time_simpl. time_cbn. unfold cert_size.
    rewrite !Nat2N.inj_add. unfold PTrieT.c_trie. nia.
  - pose proof (T_dag_cost_step_le V encode fn_cost T_fn_cost val_cost T_val_cost b Hfn Hval
      needed (dag_cost_table fn_cost val_cost needed pre Empty) i f k w
      (dag_cost_prefix_width V fn_cost val_cost Hsuper g pre c i f k remaining Hordered Heq))
      as Hstep.
    assert (Heq' : g = (pre ++ [(i, (f, k))]) ++ remaining).
    { rewrite <- app_assoc. exact Heq. }
    pose proof (IH (pre ++ [(i, (f, k))]) Heq') as Hrest.
    rewrite dag_cost_table_app in Hrest. cbn [dag_cost_table] in Hrest.
    unfold dag_cost_step in Hrest.
    time_unfold @T_dag_cost_table. time_simpl. time_cbn.
    eapply N.le_trans with (m := (1 +
      (128 * (PTrieT.c_trie + b + 1) *
        N.of_nat (Pos.size_nat i + Pos.size_nat f + dag_key_bits encode k + 1) *
        N.of_nat (w + 1) +
       256 * (PTrieT.c_trie + b + 1) *
        N.of_nat (cert_size encode remaining + 1) * N.of_nat (w + 1)))%N).
    + apply N.add_le_mono_l. apply N.add_le_mono; [exact Hstep |exact Hrest].
    +
    unfold cert_size, dag_key_bits in *; cbn [fold_right fst snd] in *;
      rewrite !Nat2N.inj_add in *; unfold PTrieT.c_trie in *; nia.
Qed.

(** Key syntax covers the sum of all encoded cell widths. *)
Lemma dag_key_cells : forall V encode (k : list (cell V)),
  fold_right (fun c n => cell_bits encode c + n) 0 k <= dag_key_bits encode k.
Proof.
  intros V encode k. induction k as [|c k IH]; unfold dag_key_bits in *;
    cbn [fold_right] in *; lia.
Qed.

(** Multiplication by a positive budget never decreases a charge. *)
Lemma dag_budget_scale : forall x factor : N, (1 <= factor)%N -> (x <= x * factor)%N.
Proof.
  intros x factor Hfactor. nia.
Qed.

(** The composed checker budgets fit one common syntax, database and cost-width product. *)
Lemma dag_check_budget : forall t d a m s r u w : N,
  (1 <= m)%N -> (1 <= u)%N -> (1 <= w)%N -> (s <= m)%N -> (r <= m)%N ->
  (1 + (d + (1 +
    (64 * (t + 64 * (4 * (d + 1) * u + 1) + 1) * m +
      (t * r + 32 * (t + 1) * s + (256 * (t + a + 1) * s * w + 8 * r))))) <=
    (64 * 1024) * (t + d + a + 1) * m * u * w)%N.
Proof.
  intros t d a m s r u w Hm Hu Hw Hs Hr.
  set (b := (t + d + a + 1)%N). set (q := (m * u * w)%N).
  fold b. replace ((64 * 1024) * b * m * u * w)%N with ((64 * 1024) * b * q)%N
    by (unfold q; ring).
  assert (Hb1 : (1 <= b)%N) by (unfold b; lia).
  assert (Hbt : (t + 1 <= b)%N) by (unfold b; lia).
  assert (Hbd : (d + 1 <= b)%N) by (unfold b; lia).
  assert (Hba : (t + a + 1 <= b)%N) by (unfold b; lia).
  assert (Hmu : (m <= m * u)%N) by (apply dag_budget_scale; exact Hu).
  assert (Hmuq : (m * u <= q)%N) by (unfold q; apply dag_budget_scale; exact Hw).
  assert (Hmq : (m <= q)%N) by lia.
  assert (Hmwq : (m * w <= q)%N).
  { unfold q. now apply N.mul_le_mono_r. }
  assert (Hsq : (s <= q)%N) by lia.
  assert (Hrq : (r <= q)%N) by lia.
  assert (Hswq : (s * w <= q)%N).
  { eapply N.le_trans; [apply N.mul_le_mono_r; exact Hs |exact Hmwq]. }
  assert (Hq1 : (1 <= q)%N) by lia.
  clearbody b q.
  assert (Hcoefficient :
    (64 * (t + 64 * (4 * (d + 1) * u + 1) + 1) <= 32768 * b * u)%N).
  { clear - Hbt Hbd Hb1 Hu. nia. }
  assert (Hvalidation :
    (64 * (t + 64 * (4 * (d + 1) * u + 1) + 1) * m <= 32768 * b * q)%N).
  { eapply N.le_trans; [apply N.mul_le_mono_r; exact Hcoefficient |].
    replace (32768 * b * u * m)%N with (32768 * b * (m * u))%N by ring.
    now apply N.mul_le_mono_l. }
  assert (Hseed : (t * r <= b * q)%N).
  { apply N.mul_le_mono; [lia |exact Hrq]. }
  assert (Hneeded : (32 * (t + 1) * s <= 32 * b * q)%N).
  { apply N.mul_le_mono; [now apply N.mul_le_mono_l |exact Hsq]. }
  assert (Hcosts : (256 * (t + a + 1) * s * w <= 256 * b * q)%N).
  { eapply N.le_trans with (m := (256 * b * s * w)%N).
    - apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_l. exact Hba.
    - replace (256 * b * s * w)%N with (256 * b * (s * w))%N by ring.
      now apply N.mul_le_mono_l. }
  assert (Hget : (8 * r <= 8 * b * q)%N) by (clear - Hrq Hb1; nia).
  assert (Hfixed : (2 + d <= 3 * b * q)%N) by (clear - Hbd Hq1 Hb1; nia).
  clear Hm Hu Hw Hs Hr Hb1 Hbt Hbd Hba Hmu Hmuq Hmq Hmwq Hsq Hrq Hswq Hq1 Hcoefficient.
  nia.
Qed.

(** The stored-row checker charges its syntax at one database unit. *)
Lemma dag_stored_check_budget : forall t d a m s r u w : N,
  (1 <= m)%N -> (1 <= u)%N -> (1 <= w)%N ->
  (s <= 3 * m * u)%N -> (r <= u)%N ->
  (1 + (d + (1 +
    ((128 * 1024) * (t + d + 1) * m * u + 8 * r +
      (t * r + 32 * (t + 1) * s + (256 * (t + a + 1) * s * w + 8 * r))))) <=
    (256 * 1024) * (t + d + a + 1) * m * u * w)%N.
Proof.
  intros t d a m s r u w Hm Hu Hw Hs Hr.
  set (b := (t + d + a + 1)%N). set (q := (m * u * w)%N).
  fold b. replace ((256 * 1024) * b * m * u * w)%N with
    ((256 * 1024) * b * q)%N by (unfold q; ring).
  assert (Hb1 : (1 <= b)%N) by (unfold b; lia).
  assert (Hbt : (t + 1 <= b)%N) by (unfold b; lia).
  assert (Hbd : (d + 1 <= b)%N) by (unfold b; lia).
  assert (Hbtd : (t + d + 1 <= b)%N) by (unfold b; lia).
  assert (Hba : (t + a + 1 <= b)%N) by (unfold b; lia).
  assert (Hmuq : (m * u <= q)%N) by (unfold q; apply dag_budget_scale; exact Hw).
  assert (Hum : (u <= m * u)%N).
  { rewrite <- (N.mul_1_l u) at 1. now apply N.mul_le_mono_r. }
  assert (Huq : (u <= q)%N) by lia.
  assert (Hrq : (r <= q)%N) by lia.
  assert (Hsq : (s <= 3 * q)%N).
  { eapply N.le_trans; [exact Hs |].
    rewrite <- N.mul_assoc. now apply N.mul_le_mono_l. }
  assert (Hswq : (s * w <= 3 * q)%N).
  { eapply N.le_trans; [apply N.mul_le_mono_r; exact Hs |].
    unfold q. ring_simplify. apply N.le_refl. }
  assert (Hq1 : (1 <= q)%N) by lia.
  clearbody b q.
  assert (Hvalidation :
    ((128 * 1024) * (t + d + 1) * m * u <= (128 * 1024) * b * q)%N).
  { replace ((128 * 1024) * (t + d + 1) * m * u)%N with
      ((128 * 1024) * (t + d + 1) * (m * u))%N by ring.
    apply N.mul_le_mono; [now apply N.mul_le_mono_l |exact Hmuq]. }
  assert (Hseed : (t * r <= b * q)%N).
  { apply N.mul_le_mono; [lia |exact Hrq]. }
  assert (Hneeded : (32 * (t + 1) * s <= 96 * b * q)%N).
  { eapply N.le_trans with (m := (32 * b * (3 * q))%N).
    - apply N.mul_le_mono; [now apply N.mul_le_mono_l |exact Hsq].
    - ring_simplify. apply N.le_refl. }
  assert (Hcosts : (256 * (t + a + 1) * s * w <= 768 * b * q)%N).
  { replace (256 * (t + a + 1) * s * w)%N with
      (256 * (t + a + 1) * (s * w))%N by ring.
    eapply N.le_trans with (m := (256 * b * (3 * q))%N).
    - apply N.mul_le_mono; [now apply N.mul_le_mono_l |exact Hswq].
    - ring_simplify. apply N.le_refl. }
  assert (Hget : (16 * r <= 16 * b * q)%N) by (clear - Hrq Hb1; nia).
  assert (Hfixed : (2 + d <= 3 * b * q)%N) by (clear - Hbd Hq1 Hb1; nia).
  clear Hm Hu Hw Hs Hr Hb1 Hbt Hbd Hbtd Hba Hmuq Hum Huq Hrq Hsq Hswq Hq1.
  nia.
Qed.

(** Guarding, selecting and copying fit the same row and width product as the checker. *)
Lemma extraction_driver_overhead : forall d r a u w l : N,
  (1 <= r)%N -> (1 <= a)%N -> (1 <= u)%N -> (1 <= w)%N -> (l <= r)%N ->
  (d * u + d + u + 32 * l * u + 8 * w + 8 <= 64 * (d + 1) * r * a * u * w)%N.
Proof.
  intros d r a u w l Hr Ha Hu Hw Hl.
  set (m := (r * a * u * w)%N).
  replace (64 * (d + 1) * r * a * u * w)%N with (64 * (d + 1) * m)%N
    by (unfold m; ring).
  assert (Hra : (1 <= r * a)%N) by nia.
  assert (Hrau : (1 <= r * a * u)%N) by nia.
  assert (Hrauw : (r * a * u <= m)%N).
  { unfold m. apply dag_budget_scale. exact Hw. }
  assert (Hum : (u <= m)%N).
  { eapply N.le_trans; [|exact Hrauw].
    rewrite <- (N.mul_1_l u) at 1. now apply N.mul_le_mono_r. }
  assert (Hwm : (w <= m)%N).
  { unfold m. rewrite <- (N.mul_1_l w) at 1. now apply N.mul_le_mono_r. }
  assert (Hlum : (l * u <= m)%N).
  { eapply N.le_trans; [|exact Hrauw]. apply N.mul_le_mono_r.
    eapply N.le_trans; [exact Hl |]. apply dag_budget_scale. exact Ha. }
  assert (Hm : (1 <= m)%N) by lia.
  clearbody m. clear Hr Ha Hu Hw Hl Hra Hrau Hrauw. nia.
Qed.

(** The public extraction coefficient dominates stored checking and its driver overhead. *)
Lemma extraction_total_budget : forall t i d c q r a u w l : N,
  (1 <= r)%N -> (1 <= a)%N -> (1 <= u)%N -> (1 <= w)%N -> (l <= r)%N ->
  ((256 * 1024) * (t + d + c + 1) * r * a * u * w +
    (d * u + d + u + 32 * l * u + 8 * w + 8) <=
    (1024 * 1024) * (t + i + d + c + q + 1) * r * a * u * w)%N.
Proof.
  intros t i d c q r a u w l Hr Ha Hu Hw Hl.
  pose proof (extraction_driver_overhead d r a u w l Hr Ha Hu Hw Hl) as Hdriver.
  eapply N.le_trans; [apply N.add_le_mono_l; exact Hdriver |].
  replace ((256 * 1024) * (t + d + c + 1) * r * a * u * w +
    64 * (d + 1) * r * a * u * w)%N with
    (((256 * 1024) * (t + d + c + 1) + 64 * (d + 1)) * r * a * u * w)%N by ring.
  apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_r. nia.
Qed.

(** The closed step coefficient pays a fixed wrapper and the generic queue-step fee. *)
Lemma extraction_step_fee_budget : forall t i d c q fee allowance : N,
  (1 <= allowance)%N -> (fee <= allowance)%N ->
  (1 + 64 * (t + q + 1) * fee <=
    (256 * 1024) * (t + i + d + c + q + 1) * allowance)%N.
Proof.
  intros t i d c q fee allowance Hpositive Hfee.
  eapply N.le_trans with (m := (allowance + 64 * (t + q + 1) * allowance)%N).
  - apply N.add_le_mono; [exact Hpositive |]. now apply N.mul_le_mono_l.
  - replace (allowance + 64 * (t + q + 1) * allowance)%N with
      ((64 * (t + q + 1) + 1) * allowance)%N by ring.
    apply N.mul_le_mono_r. nia.
Qed.

Module List.
  TimeFun flat_map.
End List.

(** Bounded index walks enumerate suffixes by following each listed child once per depth. *)
Fixpoint index_paths {A} (child : positive -> cell A -> option positive)
    (children : positive -> list (cell A)) (fuel : nat) (n : positive)
    : list (list (cell A)) :=
  match fuel with
  | 0 => [[]]
  | S rest =>
      flat_map (fun c =>
        match child n c with
        | Some next => map (cons c) (index_paths child children rest next)
        | None => []
        end) (children n)
  end.
TimeFun index_paths.

(** Splitting the final identifier uses two linear reverse traversals. *)
Definition extraction_decode {V} (f : positive) (u : list (cell V))
    : list (positive * list (cell V) * positive) :=
  match rev_append u [] with
  | Id i :: tail => [(f, rev_append tail [], i)]
  | _ => []
  end.
TimeFun extraction_decode.

(** An inventory entry supplies the depth of its full constructor index. *)
Definition inventory_entry_rows {V Ix} (index : N -> Ix)
    (child : Ix -> positive -> cell V -> option positive)
    (children : Ix -> positive -> list (cell V)) (root : Ix -> positive)
    (entry : positive * (N * nat)) : list (positive * list (cell V) * positive) :=
  let '(f, (slot, arity)) := entry in
  let ix := index slot in
  flat_map (extraction_decode f)
    (index_paths (child ix) (children ix) (S arity) (root ix)).
TimeFun inventory_entry_rows.

(** Constructor enumeration walks each named slot once in inventory order. *)
Definition inventory_rows {V Ix} (index : N -> Ix)
    (child : Ix -> positive -> cell V -> option positive)
    (children : Ix -> positive -> list (cell V)) (root : Ix -> positive)
    (cs : list (positive * (N * nat))) : list (positive * list (cell V) * positive) :=
  flat_map (inventory_entry_rows index child children root) cs.
TimeFun inventory_rows.

(** A decoded tuple retains its constructor and splits exactly at its final identifier. *)
Lemma extraction_decode_sound : forall V f (u : list (cell V)) g k i,
  In (g, k, i) (extraction_decode f u) -> f = g /\ u = k ++ [Id i].
Proof.
  intros V f u g k i Hin. unfold extraction_decode in Hin.
  destruct (rev_append u []) as [|[j|v] tail] eqn:Hreverse; try contradiction.
  destruct Hin as [Heq |Hbad]; [|contradiction]. injection Heq as <- <- <-.
  split; [reflexivity |]. rewrite <- rev_alt in Hreverse.
  apply (f_equal (@rev (cell V))) in Hreverse. rewrite rev_involutive in Hreverse.
  cbn [rev] in Hreverse. now rewrite rev_alt in Hreverse.
Qed.

(** A complete constructor tuple always decodes to its unique row. *)
Lemma extraction_decode_complete : forall V f (k : list (cell V)) i,
  extraction_decode f (k ++ [Id i]) = [(f, k, i)].
Proof.
  intros V f k i. unfold extraction_decode.
  rewrite <- rev_alt, rev_app_distr. cbn [rev app].
  rewrite <- rev_alt, rev_involutive. reflexivity.
Qed.

(** A tuple decoder emits at most one row. *)
Lemma extraction_decode_nodup : forall V f (u : list (cell V)),
  NoDup (extraction_decode f u).
Proof.
  intros V f u. unfold extraction_decode.
  destruct (rev_append u []) as [|[i|v] tail].
  - constructor.
  - constructor; [intro Hin; contradiction |constructor].
  - constructor.
Qed.

(** Duplicate-free branch keys and disjoint outputs give duplicate-free concatenation. *)
Lemma extraction_flat_map_nodup : forall A B K (key : A -> K) (branch : A -> list B) xs,
  NoDup (map key xs) ->
  (forall x, In x xs -> NoDup (branch x)) ->
  (forall x y b, In b (branch x) -> In b (branch y) -> key x = key y) ->
  NoDup (flat_map branch xs).
Proof.
  intros A B K key branch xs. induction xs as [|x xs IH];
    intros Hkeys Hbranches Hdisjoint; [constructor |].
  inversion Hkeys as [|kx keys Hfresh Htail]; subst.
  cbn [flat_map]. apply NoDup_app.
  - apply Hbranches. now left.
  - apply IH; [exact Htail | |exact Hdisjoint].
    intros y Hy. apply Hbranches. now right.
  - intros b Hhead Hrest. apply in_flat_map in Hrest as [y [Hy Hbranch]].
    apply Hfresh. rewrite (Hdisjoint x y b Hhead Hbranch). now apply in_map.
Qed.

(** Every enumerated suffix has exactly the supplied walk depth. *)
Lemma index_paths_length : forall A child children fuel n (u : list (cell A)),
  In u (index_paths child children fuel n) -> length u = fuel.
Proof.
  intros A child children fuel. induction fuel as [|fuel IH]; intros n u Hin.
  - cbn [index_paths] in Hin. destruct Hin as [<-|Hbad]; [reflexivity|contradiction].
  - cbn [index_paths] in Hin. apply in_flat_map in Hin.
    destruct Hin as [c [Hchild Hin]].
    destruct (child n c) as [next|] eqn:Hnext; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [rest [<- Hin]]. cbn [length].
    f_equal. exact (IH next rest Hin).
Qed.

Module IndexPaths (V : VALUE) (I : INDEX V).

  (** Every member suffix is found by a walk using its own length as fuel. *)
  Lemma index_paths_complete : forall fuel a ix n pre u,
    I.wf a ix -> I.node ix n pre -> I.mem ix (pre ++ u) -> length u = fuel ->
    In u (index_paths (I.child ix) (I.children ix) fuel n).
  Proof.
    intros fuel a ix n pre u Hwf Hnode Hmem Hlength. subst fuel.
    revert n pre Hnode Hmem.
    induction u as [|c u IH]; intros n pre Hnode Hmem.
    - cbn [length index_paths]. left. reflexivity.
    - cbn [length index_paths].
      destruct (I.child ix n c) as [next|] eqn:Hchild.
      + apply in_flat_map. exists c. split.
        * apply (proj2 (proj1 (I.children_spec a ix n pre c Hwf Hnode))).
          exists next. exact Hchild.
        * rewrite Hchild. apply in_map. apply (IH next (pre ++ [c])).
          -- apply (proj1 (proj1 (I.child_spec a ix n pre c Hwf Hnode) next)).
             exact Hchild.
          -- rewrite <- app_assoc. exact Hmem.
      + exfalso. apply (proj1 (proj2 (I.child_spec a ix n pre c Hwf Hnode)) Hchild).
        exists u. exact Hmem.
  Qed.

  (** A full member appears among the paths from the root at the declared index arity. *)
  Lemma index_paths_root : forall a ix u, I.wf a ix -> I.mem ix u ->
    In u (index_paths (I.child ix) (I.children ix) a (I.root ix)).
  Proof.
    intros a ix u Hwf Hmem. eapply index_paths_complete with (pre := []) (a := a).
    - exact Hwf.
    - apply I.node_root with a. exact Hwf.
    - exact Hmem.
    - eapply I.mem_arity; eassumption.
  Qed.

  (** Every enumerated suffix reaches the node for the corresponding extended prefix. *)
  Lemma index_paths_nodes : forall fuel a ix n pre u,
    I.wf a ix -> I.node ix n pre ->
    In u (index_paths (I.child ix) (I.children ix) fuel n) ->
    exists m, I.node ix m (pre ++ u).
  Proof.
    induction fuel as [|fuel IH]; intros a ix n pre u Hwf Hnode Hin.
    - cbn [index_paths] in Hin. destruct Hin as [<- |Hbad]; [|contradiction].
      exists n. now rewrite app_nil_r.
    - cbn [index_paths] in Hin. apply in_flat_map in Hin as [c [_ Hin]].
      destruct (I.child ix n c) as [next|] eqn:Hchild; [|contradiction].
      apply in_map_iff in Hin as [tail [<- Htail]].
      assert (Hnext : I.node ix next (pre ++ [c])).
      { apply (proj1 (proj1 (I.child_spec a ix n pre c Hwf Hnode) next)).
        exact Hchild. }
      destruct (IH a ix next (pre ++ [c]) tail Hwf Hnext Htail) as [last Hlast].
      exists last. rewrite <- app_assoc in Hlast. exact Hlast.
  Qed.

  (** Distinct child labels make the bounded path enumeration duplicate free. *)
  Lemma index_paths_nodup : forall fuel a ix n pre,
    I.wf a ix -> I.node ix n pre ->
    NoDup (index_paths (I.child ix) (I.children ix) fuel n).
  Proof.
    induction fuel as [|fuel IH]; intros a ix n pre Hwf Hnode.
    - cbn [index_paths]. constructor; [intro Hin; contradiction |constructor].
    - cbn [index_paths].
      eapply extraction_flat_map_nodup with (key := fun c => c).
      + rewrite map_id.
        exact (proj2 (I.children_spec a ix n pre (Id 1%positive) Hwf Hnode)).
      + intros c Hc. destruct (I.child ix n c) as [next|] eqn:Hchild; [|constructor].
        apply NoDup_map_NoDup_ForallPairs.
        * intros left right _ _ Heq. now injection Heq.
        * eapply IH with (pre := pre ++ [c]); [exact Hwf |].
          apply (proj1 (proj1 (I.child_spec a ix n pre c Hwf Hnode) next)).
          exact Hchild.
      + intros c d u Hc Hd.
        destruct (I.child ix n c) as [left|] eqn:Hleft; [|contradiction].
        destruct (I.child ix n d) as [right|] eqn:Hright; [|contradiction].
        apply in_map_iff in Hc as [us [Hus _]].
        apply in_map_iff in Hd as [vs [Hvs _]]. congruence.
  Qed.

End IndexPaths.

(** The first finalized entry for a class supplies its certificate cost budget. *)
Fixpoint extraction_cost_lookup {V} (c : positive) (entries : extraction_best V) : option N :=
  match entries with
  | [] => None
  | (i, (cost, _)) :: rest =>
    if Pos.eqb c i then Some cost else extraction_cost_lookup c rest
  end.
TimeFun extraction_cost_lookup.

(** Reversing finalization order builds the proposed constructor certificate. *)
Definition extraction_certificate {V} (entries : extraction_best V) : extraction_dag V :=
  rev_append (map (fun entry => (fst entry, snd (snd entry))) entries) [].
TimeFun extraction_certificate.

(** A candidate is returned only after checking its certificate and selected cost budget. *)
Definition extraction_candidate {V}
    (check : positive -> extraction_dag V -> option N) (c target : positive)
    (entries : extraction_best V) : option (extraction_dag V) :=
  match extraction_cost_lookup target entries with
  | None => None
  | Some budget =>
    let g := extraction_certificate entries in
    match check c g with
    | None => None
    | Some cost => if N.leb cost budget then Some g else None
    end
  end.
TimeFun extraction_candidate.

(** The binary size code denotes the natural bit width. *)
Lemma extraction_positive_size_value : forall p, Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof.
  intro p. induction p; cbn [Pos.size Pos.size_nat];
    rewrite ?Pos2Nat.inj_succ, ?IHp; reflexivity.
Qed.

(** Every binary natural fits its logarithmic width, including zero. *)
Lemma extraction_N_width_log : forall n, N.size_nat n <= N.to_nat (N.log2 n) + 1.
Proof.
  intros [|[p|p|]]; cbn [N.size_nat N.log2 N.to_nat Pos.size_nat];
    rewrite ?extraction_positive_size_value; lia.
Qed.

(** Equality stops within the width of its stored right-hand identifier. *)
Lemma extraction_eqb_right_clock : forall p q,
  (Pos.T_eqb p q <= N.of_nat (Pos.size_nat q))%N.
Proof.
  intros p q. revert p. induction q as [q IH|q IH|]; intros [p|p|]; time_step.
Qed.

(** Linear selected-cost lookup pays for stored identifier widths. *)
Lemma T_extraction_cost_lookup_le : forall V (entries : extraction_best V) target w,
  (forall i n ch, In (i, (n, ch)) entries -> Pos.size_nat i <= w) ->
  (T_extraction_cost_lookup target entries <=
    8 * N.of_nat (length entries + 1) * N.of_nat (w + 1))%N.
Proof.
  intros V entries. induction entries as [|[i [n ch]] entries IH]; intros target w Hwidth.
  - time_unfold @T_extraction_cost_lookup. cbn [length]. lia.
  - pose proof (extraction_eqb_right_clock target i) as Heq.
    pose proof (Hwidth i n ch (or_introl eq_refl)) as Hi.
    specialize (IH target w (fun j cost row Hrow => Hwidth j cost row (or_intror Hrow))).
    time_unfold @T_extraction_cost_lookup. time_simpl. time_cbn.
    destruct (Pos.eqb target i); cbn [length]; rewrite !Nat2N.inj_add in *; nia.
Qed.

(** Projecting and reversing a selected table is linear in its number of entries. *)
Lemma T_extraction_certificate_le : forall V (entries : extraction_best V),
  (T_extraction_certificate entries <= 8 * N.of_nat (length entries + 1))%N.
Proof.
  intros V entries.
  pose proof (ListDef.T_map_le (fun entry : positive * (N * extraction_row V) =>
    (fst entry, snd (snd entry))) (fun _ => 4%N) 4%N entries
    (fun _ => N.le_refl _)) as Hmap.
  pose proof (List.T_rev_append_le
    (map (fun entry : positive * (N * extraction_row V) =>
      (fst entry, snd (snd entry))) entries) []) as Hreverse.
  rewrite length_map in Hreverse.
  time_unfold @T_extraction_certificate. time_simpl. time_cbn.
  change (fun _ : positive * (N * extraction_row V) => (1 + (1 + (1 + 1)))%N)
    with (fun _ : positive * (N * extraction_row V) => 4%N).
  rewrite !Nat2N.inj_add. lia.
Qed.

(** Candidate construction adds linear selection and copying to its checker callback. *)
Lemma T_extraction_candidate_le : forall V check T_check c target
    (entries : extraction_best V) u w b,
  (forall i n ch, In (i, (n, ch)) entries -> Pos.size_nat i <= u) ->
  (T_check c (extraction_certificate entries) <= b)%N ->
  (match check c (extraction_certificate entries) with
    | Some n => N.size_nat n | None => 0 end <= w) ->
  (T_extraction_candidate check T_check c target entries <=
    b + 32 * N.of_nat (length entries + 1) * N.of_nat (u + 1) +
      8 * N.of_nat (w + 1))%N.
Proof.
  intros V check T_check c target entries u w b Hwidth Hcheck Hresult.
  pose proof (T_extraction_cost_lookup_le V entries target u Hwidth) as Hlookup.
  pose proof (T_extraction_certificate_le V entries) as Hcertificate.
  time_unfold @T_extraction_candidate. time_simpl. time_cbn.
  destruct (extraction_cost_lookup target entries) as [budget|]; [|nia].
  destruct (check c (extraction_certificate entries)) as [cost|] eqn:Hcost; [|nia].
  pose proof (N.T_leb_le cost budget) as Hcompare. nia.
Qed.

(** The allocation guard reads only the cached allocation counter's bit width. *)
Lemma extraction_guard_clock : forall ids c,
  (N.T_ltb ids (Npos c) <= N.of_nat (N.size_nat ids) + 3)%N.
Proof.
  intros ids c. pose proof (N.T_compare_le ids (Npos c)) as Hcompare.
  time_unfold @N.T_ltb. time_simpl. time_cbn. lia.
Qed.

(** A successful cost lookup comes from an actual finalized row. *)
Lemma extraction_cost_lookup_sound : forall V (entries : extraction_best V) c n,
  extraction_cost_lookup c entries = Some n -> exists ch, In (c, (n, ch)) entries.
Proof.
  intros V entries. induction entries as [|[i [cost ch]] rest IH]; intros c n Hlookup;
    cbn [extraction_cost_lookup] in Hlookup; [discriminate|].
  destruct (Pos.eqb c i) eqn:Hci.
  - apply Pos.eqb_eq in Hci. subst i. injection Hlookup as <-.
    exists ch. now left.
  - destruct (IH c n Hlookup) as [row Hin]. exists row. now right.
Qed.

(** A returned candidate has an accepted cost bounded by its selected finalized entry. *)
Lemma extraction_candidate_checked : forall V check c target (entries : extraction_best V) g,
  extraction_candidate check c target entries = Some g -> exists n m ch,
    check c g = Some n /\ In (target, (m, ch)) entries /\ (n <= m)%N.
Proof.
  intros V check c target entries g Hcandidate. unfold extraction_candidate in Hcandidate.
  destruct (extraction_cost_lookup target entries) as [budget|] eqn:Hbudget;
    [|discriminate].
  destruct (check c (extraction_certificate entries)) as [cost|] eqn:Hcheck;
    [|discriminate].
  destruct (N.leb cost budget) eqn:Hle; [|discriminate]. injection Hcandidate as <-.
  destruct (extraction_cost_lookup_sound V entries target budget Hbudget) as [ch Hin].
  exists cost, budget, ch. split; [exact Hcheck|]. split; [exact Hin|].
  now apply N.leb_le.
Qed.

(** Literal width observations omit identifier cells. *)
Definition extraction_literal_widths {V} (val_cost : V -> N) (k : list (cell V)) : list nat :=
  flat_map (fun c => match c with
    | Id _ => []
    | Val v => [N.size_nat (val_cost v)]
    end) k.

(** A row contributes its constructor-cost width followed by its literal widths. *)
Definition extraction_row_widths {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (best : extraction_best V) (entry : positive * list (cell V) * positive) : list nat :=
  let '((f, k), _) := entry in
  N.size_nat (fn_cost f (map (chosen_cost val_cost best) k)) ::
    extraction_literal_widths val_cost k.

(** The finite row-width maximum observes all constructor costs and their literal leaves. *)
Definition extraction_rows_width {V} (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (best : extraction_best V) (rs : list (positive * list (cell V) * positive)) : nat :=
  list_max (flat_map (extraction_row_widths fn_cost val_cost best) rs).

(** A finite maximum is zero or is one of its observations. *)
Lemma extraction_max_attained : forall widths,
  list_max widths = 0 \/ In (list_max widths) widths.
Proof.
  induction widths as [|w widths IH]; [now left |].
  change (Nat.max w (list_max widths) = 0 \/
    In (Nat.max w (list_max widths)) (w :: widths)).
  destruct (Nat.le_ge_cases w (list_max widths)) as [Hle |Hge].
  - rewrite Nat.max_r by exact Hle. destruct IH as [Hzero |Hin].
    + now left.
    + right. now right.
  - rewrite Nat.max_l by exact Hge. right. now left.
Qed.

(** Every finite observation is below its maximum. *)
Lemma extraction_max_member : forall widths w, In w widths -> w <= list_max widths.
Proof.
  intros widths w Hin.
  pose proof (proj1 (list_max_le widths (list_max widths)) (Nat.le_refl _)) as Hbound.
  exact (proj1 (Forall_forall _ _) Hbound w Hin).
Qed.

(** Every row's constructor-cost width is included in the finite maximum. *)
Lemma extraction_rows_width_constructor : forall V fn_cost val_cost best rs f k i,
  In (f, k, i) rs ->
  N.size_nat (fn_cost f (map (chosen_cost val_cost best) k)) <=
    @extraction_rows_width V fn_cost val_cost best rs.
Proof.
  intros V fn_cost val_cost best rs f k i Hin.
  apply extraction_max_member. apply in_flat_map.
  exists (f, k, i). split; [exact Hin |]. now left.
Qed.

(** Every literal cost appearing in a row is included in the finite maximum. *)
Lemma extraction_rows_width_literal : forall V fn_cost val_cost best rs f k i v,
  In (f, k, i) rs -> In (Val v) k ->
  N.size_nat (val_cost v) <= @extraction_rows_width V fn_cost val_cost best rs.
Proof.
  intros V fn_cost val_cost best rs f k i v Hrow Hliteral.
  apply extraction_max_member. apply in_flat_map.
  exists (f, k, i). split; [exact Hrow |].
  right. apply in_flat_map. exists (Val v). split; [exact Hliteral |]. now left.
Qed.

(** A nonzero row-width maximum is attained by a row cost or one of its literals. *)
Lemma extraction_rows_width_attained : forall V fn_cost val_cost best rs,
  @extraction_rows_width V fn_cost val_cost best rs = 0 \/
  (exists f k i, In (f, k, i) rs /\
    N.size_nat (fn_cost f (map (chosen_cost val_cost best) k)) =
      extraction_rows_width fn_cost val_cost best rs) \/
  (exists f k i v, In (f, k, i) rs /\ In (Val v) k /\
    N.size_nat (val_cost v) = extraction_rows_width fn_cost val_cost best rs).
Proof.
  intros V fn_cost val_cost best rs.
  destruct (extraction_max_attained
    (flat_map (extraction_row_widths fn_cost val_cost best) rs)) as [Hzero |Hin].
  - now left.
  - right. apply in_flat_map in Hin as [[[f k] i] [Hrow Hin]].
    cbn [extraction_row_widths] in Hin. destruct Hin as [Hcost |Hliteral].
    + left. exists f, k, i. now split.
    + right. apply in_flat_map in Hliteral as [c [Hcell Hwidth]].
      destruct c as [j|v]; [contradiction |].
      destruct Hwidth as [Hcost |Hbad]; [|contradiction].
      exists f, k, i, v. split; [exact Hrow |]. now split.
Qed.

(** Equal costs on all row keys leave the row-width maximum unchanged. *)
Lemma extraction_rows_width_agrees : forall V fn_cost val_cost left right rs,
  (forall f k i, In (f, k, i) rs -> forall c, In c k ->
    chosen_cost val_cost left c = chosen_cost val_cost right c) ->
  @extraction_rows_width V fn_cost val_cost left rs =
    extraction_rows_width fn_cost val_cost right rs.
Proof.
  intros V fn_cost val_cost left right rs Hagree.
  unfold extraction_rows_width. f_equal. revert Hagree.
  induction rs as [|[[f k] i] rs IH]; intro Hagree; [reflexivity |].
  assert (Hkey : map (chosen_cost val_cost left) k = map (chosen_cost val_cost right) k).
  { apply map_ext_in. intros c Hc. exact (Hagree f k i (or_introl eq_refl) c Hc). }
  cbn [flat_map extraction_row_widths]. rewrite Hkey.
  rewrite IH; [reflexivity |].
  intros h l j Hj c Hc. exact (Hagree h l j (or_intror Hj) c Hc).
Qed.


(** Every listed class has a successful first-match cost lookup. *)
Lemma extraction_cost_lookup_present : forall V (entries : extraction_best V) c n ch,
  In (c, (n, ch)) entries -> exists m, extraction_cost_lookup c entries = Some m.
Proof.
  intros V entries. induction entries as [|[i [value row]] entries IH];
    intros c n ch Hin; [contradiction|].
  cbn [extraction_cost_lookup]. destruct (Pos.eqb c i) eqn:Hci.
  - exists value. reflexivity.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <- <-. rewrite Pos.eqb_refl in Hci. discriminate.
    + now apply IH with n ch.
Qed.

(** The public provisional cost is the first-match selected cost, or zero if absent. *)
Lemma chosen_cost_extraction_lookup : forall V val_cost (entries : extraction_best V) i,
  chosen_cost val_cost entries (Id i) =
    match extraction_cost_lookup i entries with Some n => n | None => 0%N end.
Proof.
  intros V val_cost entries. induction entries as [|[j [n ch]] entries IH]; intro i.
  - reflexivity.
  - cbn [chosen_cost extraction_cost_lookup]. destruct (Pos.eqb i j); [reflexivity|apply IH].
Qed.

(** Finite trees over a row list use exact class identifiers. *)
Inductive search_represents {V} (rs : list (positive * list (cell V) * positive))
    : cell V -> @Model.expr V -> Prop :=
  | search_rep_lit v : search_represents rs (Val v) (Model.ELit v)
  | search_rep_app f k i args : In (f, k, i) rs ->
      Forall2 (search_represents rs) k args ->
      search_represents rs (Id i) (Model.EApp f args).

(** Adding rows preserves every finite constructor witness. *)
Lemma search_represents_mono : forall V (rs more : list (positive * list (cell V) * positive)),
  (forall r, In r rs -> In r more) -> forall c e,
  search_represents rs c e -> search_represents more c e.
Proof.
  intros V rs more Hin c e Hrep.
  induction Hrep as [v|f k i args Hrow Hargs IHargs].
  - constructor.
  - eapply search_rep_app with (k := k); [exact (Hin (f, k, i) Hrow)|].
    clear Hrow.
    induction IHargs as [|c e ks es Hr Hhead Htail Hall IH].
    + constructor.
    + constructor; assumption.
Qed.

(** The frontier argument depends on cost laws and finite rows, independently of the queue. *)
Module SearchSemantics (V : VALUE) (C : COST V).

  Definition search_known (costs : ptrie N) (k : list (cell V.t)) : Prop :=
    forall i, In (Id i) k -> exists n, trie_get i costs = Some n.

  Definition search_knuth (rs : list (positive * list (cell V.t) * positive))
      (costs : ptrie N) : Prop :=
    forall i n, trie_get i costs = Some n -> forall e,
      search_represents rs (Id i) e ->
      (n <= expression_cost C.fn_cost C.val_cost e)%N.

  Definition search_covered (rs : list (positive * list (cell V.t) * positive))
      (costs : ptrie N) (prio : positive -> option N) : Prop :=
    forall f k i, In (f, k, i) rs -> search_known costs k ->
      trie_get i costs = None -> exists n, prio i = Some n /\
        (n <= C.fn_cost f (dag_cost_cells C.val_cost costs k))%N.

  Definition search_tree_bound (costs : ptrie N) (prio : positive -> option N)
      (c : cell V.t) (e : @Model.expr V.t) : Prop :=
    match c with
    | Val v => C.val_cost v = expression_cost C.fn_cost C.val_cost e
    | Id i =>
      match trie_get i costs with
      | Some n => (n <= expression_cost C.fn_cost C.val_cost e)%N
      | None => exists j n, prio j = Some n /\
          (n <= expression_cost C.fn_cost C.val_cost e)%N
      end
    end.

  (** Children either all have bounded final costs, or expose a bounded queue candidate. *)
  Lemma search_children_frontier : forall costs prio k es,
    Forall2 (search_tree_bound costs prio) k es ->
    (search_known costs k /\
      Forall2 N.le (dag_cost_cells C.val_cost costs k)
        (map (expression_cost C.fn_cost C.val_cost) es)) \/
    exists i n child, prio i = Some n /\ In child es /\
      (n <= expression_cost C.fn_cost C.val_cost child)%N.
  Proof.
    intros costs prio k es Hbounds.
    induction Hbounds as [|c e k es Hhead Htail IH].
    - left. split; [intros i Hin; contradiction |constructor].
    - destruct c as [i|v].
      + unfold search_tree_bound in Hhead.
        destruct (trie_get i costs) as [n|] eqn:Hget.
        * destruct IH as [[Hknown Hcosts]|[j [m [child [Hprio [Hin Hle]]]]]].
          -- left. split.
             ++ intros j [Heq|Hin].
                ** injection Heq as <-. exists n. exact Hget.
                ** now apply Hknown.
             ++ cbn [dag_cost_cells map]. constructor.
                ** unfold dag_get_cost. rewrite Hget. exact Hhead.
                ** exact Hcosts.
          -- right. exists j, m, child. split; [exact Hprio|].
             split; [now right|exact Hle].
        * destruct Hhead as [j [n [Hprio Hle]]].
          right. exists j, n, e. split; [exact Hprio|].
          split; [now left|exact Hle].
      + unfold search_tree_bound in Hhead.
        destruct IH as [[Hknown Hcosts]|[j [m [child [Hprio [Hin Hle]]]]]].
        * left. split.
          -- intros j [Heq|Hin]; [discriminate|now apply Hknown].
          -- cbn [dag_cost_cells map]. constructor.
             ++ rewrite Hhead. apply N.le_refl.
             ++ exact Hcosts.
        * right. exists j, m, child. split; [exact Hprio|].
          split; [now right|exact Hle].
  Qed.

  (** Every represented tree is bounded by its final cost or by a live frontier candidate. *)
  Lemma search_tree_bound_all : forall rs costs prio,
    search_knuth rs costs -> search_covered rs costs prio ->
    forall c e, search_represents rs c e -> search_tree_bound costs prio c e.
  Proof.
    intros rs costs prio Hoptimal Hcovered c e Hrep.
    induction Hrep as [v|f k i args Hrow Hargs IHargs].
    - reflexivity.
    - unfold search_tree_bound. destruct (trie_get i costs) as [n|] eqn:Hget.
      + apply (Hoptimal i n Hget). econstructor; eassumption.
      + assert (Hbounds : Forall2 (search_tree_bound costs prio) k args).
        { clear Hrow Hget.
          induction IHargs as [|c e ks es Hr Hhead Htail Hall IH].
          - constructor.
          - constructor; assumption. }
        destruct (search_children_frontier costs prio k args Hbounds)
          as [[Hknown Hcosts]|[j [n [child [Hprio [Hin Hle]]]]]].
        * destruct (Hcovered f k i Hrow Hknown Hget) as [n [Hprio Hle]].
          exists i, n. split; [exact Hprio|].
          eapply N.le_trans; [exact Hle|].
          cbn [expression_cost]. now apply C.fn_cost_mono.
        * exists j, n. split; [exact Hprio|].
          eapply N.le_trans; [exact Hle|]. cbn [expression_cost].
          apply C.fn_cost_super. now apply in_map.
  Qed.

  (** An unfinished finite tree always has a live candidate no more expensive than itself. *)
  Lemma search_frontier : forall rs costs prio i e,
    search_knuth rs costs -> search_covered rs costs prio ->
    search_represents rs (Id i) e -> trie_get i costs = None ->
    exists j n, prio j = Some n /\ (n <= expression_cost C.fn_cost C.val_cost e)%N.
  Proof.
    intros rs costs prio i e Hoptimal Hcovered Hrep Hmissing.
    pose proof (search_tree_bound_all rs costs prio Hoptimal Hcovered (Id i) e Hrep)
      as Hbound.
    unfold search_tree_bound in Hbound. now rewrite Hmissing in Hbound.
  Qed.

  (** Finalising the least live candidate preserves all optimal-cost inequalities. *)
  Lemma search_finalise_optimal : forall rs costs prio i n,
    search_knuth rs costs -> search_covered rs costs prio ->
    trie_get i costs = None -> prio i = Some n ->
    (forall j m, prio j = Some m -> (n <= m)%N) ->
    search_knuth rs (PTrieCode.set i n costs).
  Proof.
    intros rs costs prio i n Hoptimal Hcovered Hmissing Hprio Hminimum.
    intros j m Hget e Hrep. destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget. injection Hget as <-.
      destruct (search_frontier rs costs prio i e Hoptimal Hcovered Hrep Hmissing)
        as [child [p [Hchild Hbound]]].
      eapply N.le_trans; [exact (Hminimum child p Hchild)|exact Hbound].
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      exact (Hoptimal j m Hget e Hrep).
  Qed.

  Definition search_attained (rs : list (positive * list (cell V.t) * positive))
      (costs : ptrie N) : Prop :=
    forall i n, trie_get i costs = Some n -> exists e,
      search_represents rs (Id i) e /\ expression_cost C.fn_cost C.val_cost e = n.

  (** A known key has finite child witnesses with exactly its computed cost list. *)
  Lemma search_cells_witness : forall rs costs k,
    search_attained rs costs -> search_known costs k ->
    exists es, Forall2 (search_represents rs) k es /\
      map (expression_cost C.fn_cost C.val_cost) es = dag_cost_cells C.val_cost costs k.
  Proof.
    intros rs costs k Hattained. induction k as [|[i|v] k IH]; intro Hknown.
    - exists []. split; [constructor|reflexivity].
    - destruct (Hknown i (or_introl eq_refl)) as [n Hget].
      destruct (Hattained i n Hget) as [e [Hrep Hcost]].
      destruct (IH ltac:(intros j Hin; apply Hknown; now right)) as [es [Hreps Hcosts]].
      exists (e :: es). split; [now constructor|].
      cbn [map dag_cost_cells]. unfold dag_get_cost. now rewrite Hget, Hcost, Hcosts.
    - destruct (IH ltac:(intros j Hin; apply Hknown; now right)) as [es [Hreps Hcosts]].
      exists (Model.ELit v :: es). split.
      + constructor; [constructor|exact Hreps].
      + cbn [map dag_cost_cells expression_cost]. now rewrite Hcosts.
  Qed.

  (** A row becomes a finite witness once all of its identifier children are final. *)
  Lemma search_row_witness : forall rs costs f k i,
    In (f, k, i) rs -> search_attained rs costs -> search_known costs k ->
    exists e, search_represents rs (Id i) e /\
      expression_cost C.fn_cost C.val_cost e =
        C.fn_cost f (dag_cost_cells C.val_cost costs k).
  Proof.
    intros rs costs f k i Hrow Hattained Hknown.
    destruct (search_cells_witness rs costs k Hattained Hknown) as [es [Hreps Hcosts]].
    exists (Model.EApp f es). split.
    - econstructor; eassumption.
    - cbn [expression_cost]. now rewrite Hcosts.
  Qed.

  (** Adding one attained final cost preserves all stored finite witnesses. *)
  Lemma search_attained_set : forall rs costs i n,
    search_attained rs costs ->
    (exists e, search_represents rs (Id i) e /\ expression_cost C.fn_cost C.val_cost e = n) ->
    search_attained rs (PTrieCode.set i n costs).
  Proof.
    intros rs costs i n Hattained Hnew j m Hget.
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget. injection Hget as <-. exact Hnew.
    - rewrite PTrie.get_set_other in Hget by exact Hneq. exact (Hattained j m Hget).
  Qed.

  Definition search_best_attained (rs : list (positive * list (cell V.t) * positive))
      (entries : extraction_best V.t) : Prop :=
    forall i n ch, In (i, (n, ch)) entries -> exists e,
      search_represents rs (Id i) e /\ expression_cost C.fn_cost C.val_cost e = n.

  Definition search_best_optimal (rs : list (positive * list (cell V.t) * positive))
      (entries : extraction_best V.t) : Prop :=
    forall i n ch, In (i, (n, ch)) entries -> forall e,
      search_represents rs (Id i) e -> (n <= expression_cost C.fn_cost C.val_cost e)%N.

  Definition search_best_complete (rs : list (positive * list (cell V.t) * positive))
      (entries : extraction_best V.t) : Prop :=
    forall i e, search_represents rs (Id i) e ->
      exists n ch, In (i, (n, ch)) entries.

  (** Attained optimal results agree on every class cost independently of row order. *)
  Lemma search_best_costs_agree : forall rs more left_entries right_entries,
    (forall r, In r rs <-> In r more) ->
    search_best_attained rs left_entries -> search_best_optimal rs left_entries ->
    search_best_complete rs left_entries ->
    search_best_attained more right_entries -> search_best_optimal more right_entries ->
    search_best_complete more right_entries ->
    forall c, chosen_cost C.val_cost left_entries c = chosen_cost C.val_cost right_entries c.
  Proof.
    intros rs more left_entries right_entries Hrows Hleft_att Hleft_opt Hleft_all
      Hright_att Hright_opt Hright_all [i|v].
    2: { destruct left_entries, right_entries; reflexivity. }
    rewrite !chosen_cost_extraction_lookup.
    destruct (extraction_cost_lookup i left_entries) as [n|] eqn:Hleft;
      destruct (extraction_cost_lookup i right_entries) as [m|] eqn:Hright;
      [| | |reflexivity].
    - destruct (extraction_cost_lookup_sound V.t left_entries i n Hleft) as [ch Hch].
      destruct (extraction_cost_lookup_sound V.t right_entries i m Hright) as [ch' Hch'].
      destruct (Hleft_att i n ch Hch) as [e [Hrep Hcost]].
      destruct (Hright_att i m ch' Hch') as [e' [Hrep' Hcost']].
      assert (Hnm : (n <= m)%N).
      { rewrite <- Hcost'. apply (Hleft_opt i n ch Hch e').
        eapply search_represents_mono; [|exact Hrep'].
        intros r Hin. now apply (proj2 (Hrows r)). }
      assert (Hmn : (m <= n)%N).
      { rewrite <- Hcost. apply (Hright_opt i m ch' Hch' e).
        eapply search_represents_mono; [|exact Hrep].
        intros r Hin. now apply (proj1 (Hrows r)). }
      now apply N.le_antisymm.
    - exfalso.
      destruct (extraction_cost_lookup_sound V.t left_entries i n Hleft) as [ch Hch].
      destruct (Hleft_att i n ch Hch) as [e [Hrep Hcost]].
      assert (Hrep' : search_represents more (Id i) e).
      { eapply search_represents_mono; [|exact Hrep].
        intros r Hin. now apply (proj1 (Hrows r)). }
      destruct (Hright_all i e Hrep') as [m [ch' Hch']].
      destruct (extraction_cost_lookup_present V.t right_entries i m ch' Hch') as [p Hp].
      congruence.
    - exfalso.
      destruct (extraction_cost_lookup_sound V.t right_entries i m Hright) as [ch Hch].
      destruct (Hright_att i m ch Hch) as [e [Hrep Hcost]].
      assert (Hrep' : search_represents rs (Id i) e).
      { eapply search_represents_mono; [|exact Hrep].
        intros r Hin. now apply (proj2 (Hrows r)). }
      destruct (Hleft_all i e Hrep') as [n [ch' Hch']].
      destruct (extraction_cost_lookup_present V.t left_entries i n ch' Hch') as [p Hp].
      congruence.
  Qed.

End SearchSemantics.

(** Resolving a key computes the fixed class costs whenever every resolved child does. *)
Lemma dag_resolve_cells_costs : forall V fn_cost val_cost resolve costs,
  (forall i e, resolve i = Some e ->
    expression_cost fn_cost val_cost e = dag_get_cost costs i) ->
  forall (k : list (cell V)) es, dag_resolve_cells resolve k = Some es ->
    map (expression_cost fn_cost val_cost) es = dag_cost_cells val_cost costs k.
Proof.
  intros V fn_cost val_cost resolve costs Hresolve k.
  induction k as [|[i|v] k IH]; intros es Hrun; cbn [dag_resolve_cells] in Hrun.
  - injection Hrun as <-. reflexivity.
  - destruct (resolve i) as [e|] eqn:Hhead; [|discriminate].
    destruct (dag_resolve_cells resolve k) as [tail|] eqn:Htail; [|discriminate].
    injection Hrun as <-. cbn [map dag_cost_cells].
    rewrite (Hresolve i e Hhead), (IH tail eq_refl). reflexivity.
  - destruct (dag_resolve_cells resolve k) as [tail|] eqn:Htail; [|discriminate].
    injection Hrun as <-. cbn [map dag_cost_cells expression_cost].
    now rewrite (IH tail eq_refl).
Qed.

(** Reverse unfolding respects every constructor equation of a fixed cost table. *)
Lemma dag_unfold_reverse_costs : forall V fn_cost val_cost costs (g : extraction_dag V),
  (forall i f k, In (i, (f, k)) g ->
    dag_get_cost costs i = fn_cost f (dag_cost_cells val_cost costs k)) ->
  forall i e, dag_unfold_reverse g i = Some e ->
    expression_cost fn_cost val_cost e = dag_get_cost costs i.
Proof.
  intros V fn_cost val_cost costs g. induction g as [|[j [f k]] g IH];
    intros Hrows i e Hrun; [discriminate |].
  assert (Htail : forall child name key, In (child, (name, key)) g ->
    dag_get_cost costs child = fn_cost name (dag_cost_cells val_cost costs key)).
  { intros child name key Hin. apply Hrows. now right. }
  cbn [dag_unfold_reverse] in Hrun. destruct (Pos.eqb i j) eqn:Hij.
  - apply Pos.eqb_eq in Hij. subst i.
    destruct (dag_resolve_cells (dag_unfold_reverse g) k) as [es|] eqn:Hcells;
      [|discriminate].
    injection Hrun as <-. cbn [expression_cost].
    rewrite (dag_resolve_cells_costs V fn_cost val_cost (dag_unfold_reverse g) costs
      (IH Htail) k es Hcells).
    symmetry. apply Hrows. now left.
  - exact (IH Htail i e Hrun).
Qed.

(** Finite certificate unfolding has the cost fixed by all of its row equations. *)
Lemma dag_unfold_costs : forall V fn_cost val_cost costs (g : extraction_dag V),
  (forall i f k, In (i, (f, k)) g ->
    dag_get_cost costs i = fn_cost f (dag_cost_cells val_cost costs k)) ->
  forall i e, dag_unfold g i = Some e ->
    expression_cost fn_cost val_cost e = dag_get_cost costs i.
Proof.
  intros V fn_cost val_cost costs g Hrows i e Hrun.
  unfold dag_unfold in Hrun. eapply dag_unfold_reverse_costs; [|exact Hrun].
  intros child f k Hin. apply Hrows. exact (proj2 (in_rev g (child, (f, k))) Hin).
Qed.

(** Selective evaluation agrees with a fixed cost table at every marked output. *)
Lemma dag_cost_table_agrees : forall V fn_cost val_cost needed (g : extraction_dag V) costs,
  dag_ordered_from [] g ->
  (forall i f k, In (i, (f, k)) g -> dag_seen needed i = true ->
    forall child, In (Id child) k -> dag_seen needed child = true) ->
  (forall i f k, In (i, (f, k)) g ->
    dag_get_cost costs i = fn_cost f (dag_cost_cells val_cost costs k)) ->
  forall i, In i (map fst g) -> dag_seen needed i = true ->
    dag_get_cost (dag_cost_table fn_cost val_cost needed g Empty) i = dag_get_cost costs i.
Proof.
  intros V fn_cost val_cost needed g costs Hordered Hclosed Hrows i Hin Hmarked.
  pose proof (dag_cost_table_witness V fn_cost val_cost needed g Empty [] []
    Hordered Hclosed ltac:(intros child Hchild; contradiction)) as Htable.
  destruct (Htable i Hin Hmarked) as [e [Hrep Hvalue]]. rewrite Hvalue.
  eapply dag_unfold_costs; [exact Hrows |].
  apply dag_unfold_complete; [exact (proj1 (dag_ordered_names V [] g Hordered)) |exact Hrep].
Qed.

(** Finalized rows preserve their source, finite witnesses and exact class costs. *)
Module SearchFinals (V : VALUE) (C : COST V).
  Module Semantics := SearchSemantics V C.

  (** The class trie and the duplicate-free output list record the same final costs. *)
  Definition finalised_agrees (costs : ptrie N) (entries : extraction_best V.t) : Prop :=
    NoDup (map fst entries) /\
    forall i n, trie_get i costs = Some n <-> exists ch, In (i, (n, ch)) entries.

  (** Selected rows come from the source and use only final child costs. *)
  Definition finalised_rows_valid (rs : list (positive * list (cell V.t) * positive))
      (costs : ptrie N) (entries : extraction_best V.t) : Prop :=
    forall i n f k, In (i, (n, (f, k))) entries ->
      In (f, k, i) rs /\ Semantics.search_known costs k /\
      n = C.fn_cost f (dag_cost_cells C.val_cost costs k).

  (** A valid finalized table has consistent observations and finite attained costs. *)
  Definition finalised_valid (rs : list (positive * list (cell V.t) * positive))
      (costs : ptrie N) (entries : extraction_best V.t) : Prop :=
    finalised_agrees costs entries /\ finalised_rows_valid rs costs entries /\
      Semantics.search_attained rs costs.

  (** Empty observations agree before any class has been finalized. *)
  Lemma finalised_agrees_empty : finalised_agrees Empty [].
  Proof.
    split; [constructor |]. intros i n. rewrite PTrie.get_empty.
    split; [discriminate |intros [ch Hin]; contradiction].
  Qed.

  (** Initial finalized observations satisfy the complete table invariant. *)
  Lemma finalised_empty : forall rs, finalised_valid rs Empty [].
  Proof.
    intro rs. split; [apply finalised_agrees_empty |]. split.
    - intros i n f k Hin. contradiction.
    - intros i n Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** No class occurs twice in a valid finalized list. *)
  Lemma finalised_nodup : forall rs costs entries,
    finalised_valid rs costs entries -> NoDup (map fst entries).
  Proof.
    intros rs costs entries [[Hnames _] _]. exact Hnames.
  Qed.

  (** The class-trie membership law exposes the exact listed cost. *)
  Lemma finalised_lookup_spec : forall rs costs entries i n,
    finalised_valid rs costs entries ->
    (trie_get i costs = Some n <-> exists ch, In (i, (n, ch)) entries).
  Proof.
    intros rs costs entries i n [[_ Hlookup] _]. apply Hlookup.
  Qed.

  (** First-match list lookup returns exactly the class-trie observation. *)
  Lemma finalised_lookup_agrees : forall costs entries,
    finalised_agrees costs entries -> forall i,
    extraction_cost_lookup i entries = trie_get i costs.
  Proof.
    intros costs entries [_ Hlookup] i.
    destruct (extraction_cost_lookup i entries) as [n|] eqn:Hlist.
    - symmetry. apply (proj2 (Hlookup i n)).
      exact (extraction_cost_lookup_sound V.t entries i n Hlist).
    - destruct (trie_get i costs) as [n|] eqn:Hget; [|reflexivity].
      destruct (proj1 (Hlookup i n) Hget) as [ch Hin].
      destruct (extraction_cost_lookup_present V.t entries i n ch Hin) as [m Hpresent].
      congruence.
  Qed.

  (** Provisional cell costs agree with the class trie and the literal cost operation. *)
  Lemma finalised_chosen_cost : forall costs entries,
    finalised_agrees costs entries -> forall c,
    chosen_cost C.val_cost entries c =
      match c with Id i => dag_get_cost costs i | Val v => C.val_cost v end.
  Proof.
    intros costs entries Hagrees [i|v].
    - rewrite chosen_cost_extraction_lookup, (finalised_lookup_agrees costs entries Hagrees i).
      reflexivity.
    - destruct entries; reflexivity.
  Qed.

  (** Reading a complete selected key agrees with the public list-based cost observation. *)
  Lemma finalised_key_costs : forall costs entries,
    finalised_agrees costs entries -> forall k,
    map (chosen_cost C.val_cost entries) k = dag_cost_cells C.val_cost costs k.
  Proof.
    intros costs entries Hagrees k. rewrite dag_cost_cells_map.
    apply map_ext. intro c. now apply finalised_chosen_cost.
  Qed.

  (** A class absent from the final-cost trie is absent from the finalized list. *)
  Lemma finalised_fresh : forall costs entries,
    finalised_agrees costs entries -> forall i,
    trie_get i costs = None -> ~ In i (map fst entries).
  Proof.
    intros costs entries [_ Hlookup] i Hmissing Hin.
    apply in_map_iff in Hin as [[j [n ch]] [Heq Hentry]]. cbn [fst] in Heq. subst j.
    assert (Hget : trie_get i costs = Some n).
    { apply (proj2 (Hlookup i n)). exists ch. exact Hentry. }
    rewrite Hmissing in Hget. discriminate.
  Qed.

  (** Adding a fresh class updates both final-cost observations consistently. *)
  Lemma finalised_agrees_add : forall costs entries i n row,
    finalised_agrees costs entries -> trie_get i costs = None ->
    finalised_agrees (PTrieCode.set i n costs) ((i, (n, row)) :: entries).
  Proof.
    intros costs entries i n row Hagrees Hmissing.
    destruct Hagrees as [Hnames Hlookup]. split.
    - cbn [map fst]. constructor; [|exact Hnames].
      apply (finalised_fresh costs entries); [now split |exact Hmissing].
    - intros j m. destruct (Pos.eq_dec j i) as [-> |Hneq].
      + rewrite PTrie.get_set_same. split.
        * intro Heq. injection Heq as <-. exists row. now left.
        * intros [choice [Heq |Hin]].
          -- now injection Heq as <- <-.
          -- pose proof (proj2 (Hlookup i m) (ex_intro _ choice Hin)) as Hget.
             rewrite Hmissing in Hget. discriminate.
      + rewrite PTrie.get_set_other by exact Hneq. rewrite Hlookup.
        split.
        * intros [choice Hin]. exists choice. now right.
        * intros [choice [Heq |Hin]].
          -- injection Heq as Heq _ _. congruence.
          -- exists choice. exact Hin.
  Qed.

  (** A known key remains known when a fresh class is finalized. *)
  Lemma finalised_known_add : forall costs i n k,
    trie_get i costs = None -> Semantics.search_known costs k ->
    Semantics.search_known (PTrieCode.set i n costs) k.
  Proof.
    intros costs i n k Hmissing Hknown j Hin.
    destruct (Hknown j Hin) as [m Hget]. exists m.
    destruct (Pos.eq_dec j i) as [-> |Hneq].
    - rewrite Hmissing in Hget. discriminate.
    - now rewrite PTrie.get_set_other by exact Hneq.
  Qed.

  (** Adding a fresh final class does not change any previously known key cost. *)
  Lemma finalised_key_add : forall costs i n k,
    trie_get i costs = None -> Semantics.search_known costs k ->
    dag_cost_cells C.val_cost (PTrieCode.set i n costs) k =
      dag_cost_cells C.val_cost costs k.
  Proof.
    intros costs i n k Hmissing Hknown. apply dag_cost_cells_ext. intros j Hin.
    destruct (Hknown j Hin) as [m Hget].
    destruct (Pos.eq_dec j i) as [-> |Hneq].
    - rewrite Hmissing in Hget. discriminate.
    - unfold dag_get_cost. now rewrite PTrie.get_set_other by exact Hneq.
  Qed.

  (** A newly selected ready row preserves provenance and every constructor-cost equation. *)
  Lemma finalised_rows_add : forall rs costs entries i n f k,
    finalised_rows_valid rs costs entries -> trie_get i costs = None ->
    In (f, k, i) rs -> Semantics.search_known costs k ->
    n = C.fn_cost f (dag_cost_cells C.val_cost costs k) ->
    finalised_rows_valid rs (PTrieCode.set i n costs) ((i, (n, (f, k))) :: entries).
  Proof.
    intros rs costs entries i n f k Hrows Hmissing Hrow Hknown Hcost.
    intros j m g key [Heq |Hin].
    - injection Heq as <- <- <- <-. split; [exact Hrow |]. split.
      + now apply finalised_known_add.
      + rewrite finalised_key_add by assumption. exact Hcost.
    - destruct (Hrows j m g key Hin) as [Hsource [Hready Hvalue]].
      split; [exact Hsource |]. split.
      + now apply finalised_known_add.
      + rewrite finalised_key_add by assumption. exact Hvalue.
  Qed.

  (** Finalizing a fresh ready row preserves the complete finalized-table invariant. *)
  Lemma finalised_valid_add : forall rs costs entries i n f k,
    finalised_valid rs costs entries -> trie_get i costs = None ->
    In (f, k, i) rs -> Semantics.search_known costs k ->
    n = C.fn_cost f (dag_cost_cells C.val_cost costs k) ->
    finalised_valid rs (PTrieCode.set i n costs) ((i, (n, (f, k))) :: entries).
  Proof.
    intros rs costs entries i n f k [Hagrees [Hrows Hattained]] Hmissing Hrow Hknown Hcost.
    split; [now apply finalised_agrees_add |]. split.
    - now apply finalised_rows_add.
    - apply Semantics.search_attained_set; [exact Hattained |].
      destruct (Semantics.search_row_witness rs costs f k i Hrow Hattained Hknown)
        as [e [Hrep Hvalue]].
      exists e. split; [exact Hrep |]. now rewrite Hcost.
  Qed.

  (** The public selected-row equation follows from the internal cost-trie invariant. *)
  Lemma finalised_row : forall rs costs entries i n f k,
    finalised_valid rs costs entries -> In (i, (n, (f, k))) entries ->
    In (f, k, i) rs /\ n = C.fn_cost f (map (chosen_cost C.val_cost entries) k).
  Proof.
    intros rs costs entries i n f k [Hagrees [Hrows _]] Hin.
    destruct (Hrows i n f k Hin) as [Hsource [_ Hcost]]. split; [exact Hsource |].
    rewrite (finalised_key_costs costs entries Hagrees k). exact Hcost.
  Qed.

  (** Every finalized list entry inherits an attained finite tree from its class cost. *)
  Lemma finalised_attained : forall rs costs entries,
    finalised_valid rs costs entries -> Semantics.search_best_attained rs entries.
  Proof.
    intros rs costs entries [[_ Hlookup] [_ Hattained]] i n ch Hin.
    apply Hattained. apply (proj2 (Hlookup i n)). exists ch. exact Hin.
  Qed.

  (** The optimal-cost trie invariant gives the same bound for each finalized list entry. *)
  Lemma finalised_optimal : forall rs costs entries,
    finalised_valid rs costs entries -> Semantics.search_knuth rs costs ->
    Semantics.search_best_optimal rs entries.
  Proof.
    intros rs costs entries [[_ Hlookup] _] Hoptimal i n ch Hin e Hrep.
    apply (Hoptimal i n); [|exact Hrep]. apply (proj2 (Hlookup i n)). exists ch. exact Hin.
  Qed.

  (** An empty frontier leaves no finite represented class outside the finalized table. *)
  Lemma finalised_complete : forall rs costs entries prio,
    finalised_valid rs costs entries -> Semantics.search_knuth rs costs ->
    Semantics.search_covered rs costs prio -> (forall i, prio i = None) ->
    Semantics.search_best_complete rs entries.
  Proof.
    intros rs costs entries prio [[_ Hlookup] _] Hoptimal Hcovered Hempty i e Hrep.
    destruct (trie_get i costs) as [n|] eqn:Hget.
    - destruct (proj1 (Hlookup i n) Hget) as [ch Hin]. exists n, ch. exact Hin.
    - destruct (Semantics.search_frontier rs costs prio i e Hoptimal Hcovered Hrep Hget)
        as [j [n [Hprio _]]]. rewrite Hempty in Hprio. discriminate.
  Qed.

  (** Forgetting final costs retains each selected constructor row and its output class. *)
  Definition selected_rows (entries : extraction_best V.t)
      : list (positive * list (cell V.t) * positive) :=
    map (fun '(i, (_, (f, k))) => (f, k, i)) entries.

  (** Distinct finalized class names make their selected source rows distinct. *)
  Lemma selected_rows_nodup : forall costs entries,
    finalised_agrees costs entries -> NoDup (selected_rows entries).
  Proof.
    intros costs entries [Hnames _].
    apply NoDup_map_inv with (f := @snd (positive * list (cell V.t)) positive).
    assert (Houtputs : map snd (selected_rows entries) = map fst entries).
    { unfold selected_rows. rewrite map_map. apply map_ext.
      intros [i [n [f k]]]. reflexivity. }
    now rewrite Houtputs.
  Qed.

  (** Every selected row belongs to the immutable source row list. *)
  Lemma selected_rows_source : forall rs costs entries,
    finalised_rows_valid rs costs entries -> incl (selected_rows entries) rs.
  Proof.
    intros rs costs entries Hrows r Hin. unfold selected_rows in Hin.
    apply in_map_iff in Hin as [[i [n [f k]]] [<- Hentry]].
    exact (proj1 (Hrows i n f k Hentry)).
  Qed.

  (** There can be no more finalized classes than source constructor rows. *)
  Lemma finalised_cardinality : forall rs costs entries,
    finalised_valid rs costs entries -> length entries <= length rs.
  Proof.
    intros rs costs entries [Hagrees [Hrows _]].
    pose proof (NoDup_incl_length (selected_rows_nodup costs entries Hagrees)
      (selected_rows_source rs costs entries Hrows)) as Hlength.
    unfold selected_rows in Hlength. now rewrite length_map in Hlength.
  Qed.

  (** Certificate entries are exactly selected rows with their recorded costs forgotten. *)
  Lemma certificate_entry : forall (entries : extraction_best V.t) i f k,
    In (i, (f, k)) (extraction_certificate entries) <->
      exists n, In (i, (n, (f, k))) entries.
  Proof.
    intros entries i f k. unfold extraction_certificate. rewrite <- rev_alt, <- in_rev.
    rewrite in_map_iff. split.
    - intros [[j [n [g key]]] [Heq Hin]]. cbn [fst snd] in Heq.
      injection Heq as <- <- <-. exists n. exact Hin.
    - intros [n Hin]. exists (i, (n, (f, k))). split; [reflexivity |exact Hin].
  Qed.

  (** Every selected certificate row satisfies the finalized class-cost equation. *)
  Lemma certificate_row_costs : forall rs costs entries,
    finalised_valid rs costs entries -> forall i f k,
    In (i, (f, k)) (extraction_certificate entries) ->
    dag_get_cost costs i = C.fn_cost f (dag_cost_cells C.val_cost costs k).
  Proof.
    intros rs costs entries [[_ Hlookup] [Hrows _]] i f k Hin.
    apply certificate_entry in Hin as [n Hentry].
    destruct (Hrows i n f k Hentry) as [_ [_ Hcost]].
    pose proof (proj2 (Hlookup i n) (ex_intro _ (f, k) Hentry)) as Hget.
    unfold dag_get_cost. now rewrite Hget.
  Qed.

  (** Selective certificate evaluation agrees with the final trie at every marked output. *)
  Lemma certificate_cost_table_agrees : forall rs costs entries seed,
    finalised_valid rs costs entries -> dag_ordered_from [] (extraction_certificate entries) ->
    let g := extraction_certificate entries in
    let needed := dag_needed g seed in
    forall i, In i (map fst g) -> dag_seen needed i = true ->
    dag_get_cost (dag_cost_table C.fn_cost C.val_cost needed g Empty) i = dag_get_cost costs i.
  Proof.
    intros rs costs entries seed Hvalid Hordered g needed i Hin Hmarked.
    apply dag_cost_table_agrees; [exact Hordered | | |exact Hin |exact Hmarked].
    - exact (dag_needed_closed V.t g seed Hordered).
    - exact (certificate_row_costs rs costs entries Hvalid).
  Qed.

  (** An accepted selected certificate reports exactly the finalized root cost. *)
  Lemma certificate_check_cost : forall rs costs entries check_row c n,
    finalised_valid rs costs entries ->
    dag_check check_row C.fn_cost C.val_cost (extraction_certificate entries) c = Some n ->
    n = dag_get_cost costs c.
  Proof.
    intros rs costs entries check_row c n Hvalid Hcheck.
    destruct (dag_check_correct V.t check_row C.fn_cost C.val_cost
      (extraction_certificate entries) c n Hcheck) as [_ [_ [e [_ [Hunfold Hcost]]]]].
    rewrite Hcost. eapply dag_unfold_costs; [|exact Hunfold].
    exact (certificate_row_costs rs costs entries Hvalid).
  Qed.

  (** An accepted selected root has the same exact cost in the final output list. *)
  Lemma certificate_check_lookup : forall rs costs entries check_row c n,
    finalised_valid rs costs entries ->
    dag_check check_row C.fn_cost C.val_cost (extraction_certificate entries) c = Some n ->
    extraction_cost_lookup c entries = Some n.
  Proof.
    intros rs costs entries check_row c n Hvalid Hcheck.
    pose proof (certificate_check_cost rs costs entries check_row c n Hvalid Hcheck) as Hcost.
    destruct (dag_check_correct V.t check_row C.fn_cost C.val_cost
      (extraction_certificate entries) c n Hcheck) as [_ [_ [e [Hrep _]]]].
    pose proof (dag_represents_name V.t (extraction_certificate entries) c e Hrep) as Hname.
    apply in_map_iff in Hname as [[i [f k]] [Hic Hin]]. cbn [fst] in Hic. subst i.
    apply certificate_entry in Hin as [m Hentry].
    pose proof (proj2 (finalised_lookup_spec rs costs entries c m Hvalid)
      (ex_intro _ (f, k) Hentry)) as Hget.
    unfold dag_get_cost in Hcost. rewrite Hget in Hcost. subst n.
    rewrite (finalised_lookup_agrees costs entries (proj1 Hvalid) c). exact Hget.
  Qed.

  (** A uniform selected-cost width bounds every accepted selected certificate root. *)
  Lemma certificate_check_width : forall rs costs entries check_row c width,
    finalised_valid rs costs entries ->
    (forall i n ch, In (i, (n, ch)) entries -> N.size_nat n <= width) ->
    match dag_check check_row C.fn_cost C.val_cost (extraction_certificate entries) c with
    | Some n => N.size_nat n
    | None => 0
    end <= width.
  Proof.
    intros rs costs entries check_row c width Hvalid Hwidth.
    destruct (dag_check check_row C.fn_cost C.val_cost (extraction_certificate entries) c)
      as [n|] eqn:Hcheck; [|lia].
    pose proof (certificate_check_lookup rs costs entries check_row c n Hvalid Hcheck)
      as Hlookup.
    destruct (extraction_cost_lookup_sound V.t entries c n Hlookup) as [ch Hin].
    exact (Hwidth c n ch Hin).
  Qed.
End SearchFinals.

(** Ghost row enumeration uses declared slot depths and exact stored-row lookup. *)
Module ConstructorRows (V : VALUE) (I : INDEX V) (D : DATABASE V I).
  Module Paths := IndexPaths V I.
  Module Cells := CellKey V.

  (** Ghost row equality compares function names, complete keys and output identifiers. *)
  Definition cell_eq_dec (x y : cell V.t) : {x = y} + {x <> y}.
  Proof.
    destruct (Cells.eqb x y) eqn:Hcheck.
    - left. destruct (Cells.eqb_spec x y); [assumption |discriminate].
    - right. destruct (Cells.eqb_spec x y); [discriminate |assumption].
  Defined.

  Definition row_eq_dec (x y : positive * list (cell V.t) * positive) :
      {x = y} + {x <> y}.
  Proof.
    destruct x as [[f k] i], y as [[g l] j].
    destruct (Pos.eq_dec f g) as [-> |Hname]; [|right; congruence].
    destruct (list_eq_dec cell_eq_dec k l) as [-> |Hkey]; [|right; congruence].
    destruct (Pos.eq_dec i j) as [-> |Houtput]; [left; reflexivity |right; congruence].
  Defined.

  (** A candidate tuple contributes a constructor row only after exact stored-row lookup. *)
  Definition tuple_row (db : D.t) (f : positive) (u : list (cell V.t))
      : list (positive * list (cell V.t) * positive) :=
    match rev u with
    | Id i :: tail =>
      let k := rev tail in
      match D.old db f k with
      | Some (Some (Id j)) => if Pos.eqb i j then [(f, k, i)] else []
      | _ => []
      end
    | _ => []
    end.

  (** The ghost collector knows every slot's depth from its specification metadata. *)
  Definition slot_rows (db : D.t) (slot : nat)
      : list (positive * list (cell V.t) * positive) :=
    match nth_error (D.slots db) slot with
    | Some (f, perm) =>
      let ix := D.index (N.of_nat slot) false db in
      flat_map (tuple_row db f)
        (index_paths (I.child ix) (I.children ix) (length perm) (I.root ix))
    | None => []
    end.

  Definition all_rows (db : D.t) : list (positive * list (cell V.t) * positive) :=
    flat_map (slot_rows db) (seq 0 (length (D.slots db))).

  (** Specification enumeration retains each exact constructor row once. *)
  Definition rows (db : D.t) : list (positive * list (cell V.t) * positive) :=
    nodup row_eq_dec (all_rows db).

  Definition maximum_arity (rs : list (positive * list (cell V.t) * positive)) : nat :=
    fold_right (fun entry n => Nat.max (length (snd (fst entry))) n) 0 rs.

  (** Every retained candidate is an exact public constructor row. *)
  Lemma tuple_row_sound : forall db f u g k i, D.wf db ->
    In (g, k, i) (tuple_row db f u) -> Model.row (D.view db) g k (Some (Id i)).
  Proof.
    intros db f u g k i Hwf Hin. unfold tuple_row in Hin.
    destruct (rev u) as [|[j|v] tail] eqn:Hrev; try contradiction.
    destruct (D.old db f (rev tail)) as [[[outid|outval]|]|] eqn:Hstored;
      try contradiction.
    destruct (Pos.eqb j outid) eqn:Hout; [|contradiction].
    apply Pos.eqb_eq in Hout. subst outid.
    destruct Hin as [Heq |Hbad]; [|contradiction]. inversion Heq; subst.
    apply (proj1 (D.old_row _ _ _ _ Hwf)). exact Hstored.
  Qed.

  (** A complete constructor tuple passes the exact-row filter. *)
  Lemma tuple_row_complete : forall db f k i, D.wf db ->
    Model.row (D.view db) f k (Some (Id i)) ->
    tuple_row db f (k ++ [Id i]) = [(f, k, i)].
  Proof.
    intros db f k i Hwf Hrow.
    pose proof (proj2 (D.old_row db f k (Some (Id i)) Hwf) Hrow) as Hstored.
    unfold tuple_row. rewrite rev_app_distr. cbn [rev app].
    rewrite rev_involutive, Hstored, Pos.eqb_refl. reflexivity.
  Qed.

  (** Filtering makes the whole slot enumeration sound even for partial or empty slots. *)
  Lemma rows_sound : forall db f k i, D.wf db ->
    In (f, k, i) (rows db) -> Model.row (D.view db) f k (Some (Id i)).
  Proof.
    intros db f k i Hwf Hin. unfold rows in Hin. apply nodup_In in Hin.
    unfold all_rows in Hin. apply in_flat_map in Hin as [slot [_ Hin]].
    unfold slot_rows in Hin.
    destruct (nth_error (D.slots db) slot) as [[g perm]|] eqn:Hslot; [|contradiction].
    apply in_flat_map in Hin as [u [_ Hin]].
    eapply tuple_row_sound; eassumption.
  Qed.

  (** Any row with an unpermuted full slot appears in the finite enumeration. *)
  Lemma rows_complete : forall db f k i, D.wf db ->
    Model.row (D.view db) f k (Some (Id i)) ->
    (exists slot perm, D.slot_of db slot = Some (f, perm) /\
      D.permute perm (k ++ [Id i]) = k ++ [Id i]) ->
    In (f, k, i) (rows db).
  Proof.
    intros db f k i Hwf Hrow [slot [perm [Hslot Hfull]]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    pose proof (D.index_all_complete db slot f perm k (Some (Id i)) Hwf Hslot Hrow)
      as Hmember.
    cbn [option_list] in Hmember. rewrite Hfull in Hmember.
    pose proof (Paths.index_paths_root _ _ _ Hindex Hmember) as Hpath.
    unfold rows. apply nodup_In. unfold all_rows. apply in_flat_map.
    exists (N.to_nat slot). split.
    - apply in_seq. split; [lia |]. unfold D.slot_of in Hslot.
      apply nth_error_Some. intro Hnone. rewrite Hnone in Hslot. discriminate.
    - unfold slot_rows. unfold D.slot_of in Hslot. rewrite Hslot, N2Nat.id.
      apply in_flat_map. exists (k ++ [Id i]). split; [exact Hpath |].
      rewrite (tuple_row_complete db f k i Hwf Hrow). now left.
  Qed.

  (** Exact-row enumeration has no duplicate triples. *)
  Lemma rows_nodup : forall db, NoDup (rows db).
  Proof.
    intro db. apply NoDup_nodup.
  Qed.

  (** Each enumerated row key is bounded by the recorded maximum. *)
  Lemma maximum_arity_member : forall rs f k i,
    In (f, k, i) rs -> length k <= maximum_arity rs.
  Proof.
    induction rs as [|entry rs IH]; intros f k i Hin; [contradiction |].
    cbn [maximum_arity fold_right]. destruct Hin as [-> |Hin].
    - cbn [fst snd]. apply Nat.le_max_l.
    - eapply Nat.le_trans; [eapply IH; exact Hin |apply Nat.le_max_r].
  Qed.

  (** The maximum is zero or is attained by one of the finite rows. *)
  Lemma maximum_arity_attained : forall rs,
    maximum_arity rs = 0 \/ exists f k i, In (f, k, i) rs /\ length k = maximum_arity rs.
  Proof.
    induction rs as [|[[f k] i] rs IH]; [now left |].
    cbn [maximum_arity fold_right fst snd] in *.
    destruct (Nat.le_ge_cases (length k) (maximum_arity rs)) as [Hle |Hge].
    - change (Nat.max (length k) (maximum_arity rs) = 0 \/
        exists g l j, In (g, l, j) ((f, k, i) :: rs) /\
          length l = Nat.max (length k) (maximum_arity rs)).
      rewrite Nat.max_r by exact Hle. destruct IH as [Hzero |[g [l [j [Hin Heq]]]]].
      + now left.
      + right. exists g, l, j. split; [now right |exact Heq].
    - change (Nat.max (length k) (maximum_arity rs) = 0 \/
        exists g l j, In (g, l, j) ((f, k, i) :: rs) /\
          length l = Nat.max (length k) (maximum_arity rs)).
      rewrite Nat.max_l by exact Hge. right. exists f, k, i. split; [now left |reflexivity].
  Qed.
End ConstructorRows.

(** Executable enumeration agrees with the finite constructor-row specification. *)
Module EnumeratedRows (V : VALUE) (I : INDEX V) (D : DATABASE V I).
  Module Paths := IndexPaths V I.
  Module Rows := ConstructorRows V I D.

  (** The inventory's slot clause fixes every tuple's arity, output and order. *)
  Definition entry_ok (db : D.t) (f : positive) (slot : N) (arity : nat) : Prop :=
    exists perm, D.slot_of db slot = Some (f, perm) /\
      forall k o, row (D.view db) f k o ->
        length k = arity /\ (exists i, o = Some (Id i)) /\
        D.permute perm (k ++ option_list o) = k ++ option_list o.

  Definition entry_rows (db : D.t) (entry : positive * (N * nat)) :=
    inventory_entry_rows (fun slot => D.index slot false db) I.child I.children I.root entry.

  Definition enumerated_rows (cs : list (positive * (N * nat))) (db : D.t) :=
    inventory_rows (fun slot => D.index slot false db) I.child I.children I.root cs.

  (** Every indexed member is a full tuple of the named constructor. *)
  Lemma entry_member_sound : forall db f slot arity u,
    D.wf db -> entry_ok db f slot arity -> I.mem (D.index slot false db) u ->
    exists k i, row (D.view db) f k (Some (Id i)) /\
      length k = arity /\ u = k ++ [Id i].
  Proof.
    intros db f slot arity u Hwf [perm [Hslot Hrows]] Hmember.
    destruct (D.index_all db slot false u Hwf Hmember)
      as [g [positions [k [o [Hslot' [Hrow Htuple]]]]]].
    rewrite Hslot in Hslot'. injection Hslot' as <- <-.
    destruct (Hrows k o Hrow) as [Hlength [[i Houtput] Hfull]]. subst o.
    cbn [option_list] in Hfull, Htuple. rewrite Hfull in Htuple.
    exists k, i. repeat split; assumption.
  Qed.

  (** The full inventory index contains every row of its constructor. *)
  Lemma entry_member_complete : forall db f slot arity k i,
    D.wf db -> entry_ok db f slot arity -> row (D.view db) f k (Some (Id i)) ->
    I.mem (D.index slot false db) (k ++ [Id i]).
  Proof.
    intros db f slot arity k i Hwf [perm [Hslot Hrows]] Hrow.
    pose proof (D.index_all_complete db slot f perm k (Some (Id i)) Hwf Hslot Hrow)
      as Hmember.
    destruct (Hrows k (Some (Id i)) Hrow) as [_ [_ Hfull]].
    cbn [option_list] in Hfull, Hmember. now rewrite Hfull in Hmember.
  Qed.

  (** A nonempty live prefix extends to a tuple of exactly the inventory depth. *)
  Lemma entry_node_extension : forall db f slot arity node pre,
    D.wf db -> entry_ok db f slot arity ->
    I.node (D.index slot false db) node pre -> pre <> [] ->
    exists suffix, I.mem (D.index slot false db) (pre ++ suffix) /\
      length pre + length suffix = S arity.
  Proof.
    intros db f slot arity node pre Hwf Hentry Hnode Hnonempty.
    destruct Hentry as [perm [Hslot Hrows]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    destruct (I.node_live (length perm) _ node pre Hindex Hnode Hnonempty)
      as [suffix Hmember].
    assert (Hentry : entry_ok db f slot arity) by (exists perm; auto).
    destruct (entry_member_sound db f slot arity _ Hwf Hentry Hmember)
      as [k [i [_ [Hlength Htuple]]]].
    exists suffix. split; [exact Hmember |].
    apply (f_equal (@length (cell V.t))) in Htuple.
    rewrite !length_app in Htuple. cbn [length] in Htuple. lia.
  Qed.

  (** Every child of a live prefix contributes a completed path at the remaining depth. *)
  Lemma entry_child_paths_live : forall db f slot arity node pre c next remaining,
    D.wf db -> entry_ok db f slot arity ->
    I.node (D.index slot false db) node pre -> length pre + S remaining = S arity ->
    I.child (D.index slot false db) node c = Some next ->
    exists suffix, In suffix
      (index_paths (I.child (D.index slot false db)) (I.children (D.index slot false db))
        remaining next).
  Proof.
    intros db f slot arity node pre c next remaining Hwf Hentry Hnode Hdepth Hchild.
    destruct Hentry as [perm [Hslot Hrows]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    assert (Hnext : I.node (D.index slot false db) next (pre ++ [c])).
    { apply (proj1 (proj1 (I.child_spec (length perm) _ node pre c Hindex Hnode) next)).
      exact Hchild. }
    assert (Hentry : entry_ok db f slot arity) by (exists perm; auto).
    assert (Hnonempty : pre ++ [c] <> []).
    { intro Hempty. apply app_eq_nil in Hempty as [_ Hbad]. discriminate. }
    destruct (entry_node_extension db f slot arity next (pre ++ [c])
      Hwf Hentry Hnext Hnonempty) as [suffix [Hmember Hlength]].
    exists suffix. eapply Paths.index_paths_complete with (pre := pre ++ [c]).
    - exact Hindex.
    - exact Hnext.
    - exact Hmember.
    - rewrite length_app in Hlength. cbn [length] in Hlength. lia.
  Qed.

  (** A full-depth root path is itself a complete constructor tuple. *)
  Lemma entry_paths_sound : forall db f slot arity u,
    D.wf db -> entry_ok db f slot arity ->
    In u (index_paths (I.child (D.index slot false db))
      (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))) ->
    exists k i, row (D.view db) f k (Some (Id i)) /\
      length k = arity /\ u = k ++ [Id i].
  Proof.
    intros db f slot arity u Hwf Hentry Hpath.
    destruct Hentry as [perm [Hslot Hrows]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    pose proof (index_paths_length V.t _ _ _ _ u Hpath) as Hlength.
    destruct (Paths.index_paths_nodes (S arity) (length perm) _ _ [] u Hindex
      (I.node_root _ _ Hindex) Hpath) as [node Hnode].
    cbn [app] in Hnode.
    assert (Hentry : entry_ok db f slot arity) by (exists perm; auto).
    assert (Hnonempty : u <> []) by (intro Heq; subst u; discriminate).
    destruct (entry_node_extension db f slot arity node u Hwf Hentry Hnode Hnonempty)
      as [suffix [Hmember Htotal]].
    assert (Hsuffix : suffix = []) by (apply length_zero_iff_nil; lia).
    subst suffix. rewrite app_nil_r in Hmember.
    exact (entry_member_sound db f slot arity u Hwf Hentry Hmember).
  Qed.

  (** Every constructor row is found with the inventory's supplied arity as fuel. *)
  Lemma entry_paths_complete : forall db f slot arity k i,
    D.wf db -> entry_ok db f slot arity -> row (D.view db) f k (Some (Id i)) ->
    In (k ++ [Id i]) (index_paths (I.child (D.index slot false db))
      (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))).
  Proof.
    intros db f slot arity k i Hwf Hentry Hrow.
    pose proof (entry_member_complete db f slot arity k i Hwf Hentry Hrow) as Hmember.
    destruct Hentry as [perm [Hslot Hrows]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    destruct (Hrows k (Some (Id i)) Hrow) as [Hlength _].
    eapply Paths.index_paths_complete with (pre := []) (a := length perm).
    - exact Hindex.
    - apply I.node_root with (length perm). exact Hindex.
    - exact Hmember.
    - rewrite length_app. cbn [length]. lia.
  Qed.

  (** Decoding an entry cannot change its constructor name. *)
  Lemma entry_rows_name : forall db f slot arity g k i,
    In (g, k, i) (entry_rows db (f, (slot, arity))) -> g = f.
  Proof.
    intros db f slot arity g k i Hin. unfold entry_rows, inventory_entry_rows in Hin.
    apply in_flat_map in Hin as [u [_ Hdecode]].
    symmetry. exact (proj1 (extraction_decode_sound V.t f u g k i Hdecode)).
  Qed.

  (** Every row emitted for an entry occurs in the database. *)
  Lemma entry_rows_sound : forall db f slot arity g k i,
    D.wf db -> entry_ok db f slot arity ->
    In (g, k, i) (entry_rows db (f, (slot, arity))) ->
    row (D.view db) g k (Some (Id i)).
  Proof.
    intros db f slot arity g k i Hwf Hentry Hin.
    unfold entry_rows, inventory_entry_rows in Hin.
    apply in_flat_map in Hin as [u [Hpath Hdecode]].
    destruct (entry_paths_sound db f slot arity u Hwf Hentry Hpath)
      as [key [outid [Hrow [_ Htuple]]]].
    subst u. rewrite extraction_decode_complete in Hdecode.
    destruct Hdecode as [Heq |Hbad]; [|contradiction]. now injection Heq as <- <- <-.
  Qed.

  (** Every database constructor row is emitted by its inventory entry. *)
  Lemma entry_rows_complete : forall db f slot arity k i,
    D.wf db -> entry_ok db f slot arity -> row (D.view db) f k (Some (Id i)) ->
    In (f, k, i) (entry_rows db (f, (slot, arity))).
  Proof.
    intros db f slot arity k i Hwf Hentry Hrow.
    unfold entry_rows, inventory_entry_rows. apply in_flat_map.
    exists (k ++ [Id i]). split.
    - exact (entry_paths_complete db f slot arity k i Hwf Hentry Hrow).
    - rewrite extraction_decode_complete. now left.
  Qed.

  (** Duplicate-free paths decode to duplicate-free constructor rows. *)
  Lemma entry_rows_nodup : forall db f slot arity,
    D.wf db -> entry_ok db f slot arity -> NoDup (entry_rows db (f, (slot, arity))).
  Proof.
    intros db f slot arity Hwf [perm [Hslot Hrows]].
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    unfold entry_rows, inventory_entry_rows.
    eapply extraction_flat_map_nodup with (key := fun u => u).
    - rewrite map_id. eapply Paths.index_paths_nodup with (pre := []).
      + exact Hindex.
      + apply I.node_root with (length perm). exact Hindex.
    - intros u _. apply extraction_decode_nodup.
    - intros left right [[g k] i] Hleft Hright.
      destruct (extraction_decode_sound V.t f left g k i Hleft) as [_ Hleft'].
      destruct (extraction_decode_sound V.t f right g k i Hright) as [_ Hright']. congruence.
  Qed.

  (** Full inventory enumeration contains only exact constructor rows. *)
  Lemma enumerated_rows_sound : forall cs db f k i,
    D.wf db ->
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    In (f, k, i) (enumerated_rows cs db) -> row (D.view db) f k (Some (Id i)).
  Proof.
    intros cs db f k i Hwf Hentries Hin. unfold enumerated_rows, inventory_rows in Hin.
    apply in_flat_map in Hin as [[g [slot arity]] [Hentry Hin]].
    eapply entry_rows_sound; [exact Hwf |apply Hentries; exact Hentry |exact Hin].
  Qed.

  (** Coverage of constructor names makes inventory enumeration complete. *)
  Lemma enumerated_rows_complete : forall cs db f k i,
    D.wf db ->
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    (forall g key outid, row (D.view db) g key (Some (Id outid)) -> In g (map fst cs)) ->
    row (D.view db) f k (Some (Id i)) -> In (f, k, i) (enumerated_rows cs db).
  Proof.
    intros cs db f k i Hwf Hentries Hcovers Hrow.
    pose proof (Hcovers f k i Hrow) as Hname.
    apply in_map_iff in Hname as [[g [slot arity]] [Hname Hentry]].
    cbn [fst] in Hname. subst g.
    unfold enumerated_rows, inventory_rows. apply in_flat_map.
    exists (f, (slot, arity)). split; [exact Hentry |].
    apply entry_rows_complete; [exact Hwf |apply Hentries; exact Hentry |exact Hrow].
  Qed.

  (** Distinct constructor names make the complete inventory row list duplicate free. *)
  Lemma enumerated_rows_nodup : forall cs db,
    D.wf db -> NoDup (map fst cs) ->
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    NoDup (enumerated_rows cs db).
  Proof.
    intros cs db Hwf Hnames Hentries.
    change (NoDup (flat_map (entry_rows db) cs)).
    eapply extraction_flat_map_nodup with (key := fst).
    - exact Hnames.
    - intros [f [slot arity]] Hin. apply entry_rows_nodup; [exact Hwf |now apply Hentries].
    - intros [f [slot arity]] [g [other width]] [[name key] outid] Hleft Hright.
      cbn [fst]. pose proof (entry_rows_name db f slot arity name key outid Hleft).
      pose proof (entry_rows_name db g other width name key outid Hright). congruence.
  Qed.

  (** Every covered constructor row has a slot for the ghost enumeration. *)
  Lemma inventory_full_slot : forall cs db f k i,
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    (forall g key outid, row (D.view db) g key (Some (Id outid)) -> In g (map fst cs)) ->
    row (D.view db) f k (Some (Id i)) ->
    exists slot perm, D.slot_of db slot = Some (f, perm) /\
      D.permute perm (k ++ [Id i]) = k ++ [Id i].
  Proof.
    intros cs db f k i Hentries Hcovers Hrow.
    pose proof (Hcovers f k i Hrow) as Hname.
    apply in_map_iff in Hname as [[g [slot arity]] [Hname Hentry]].
    cbn [fst] in Hname. subst g.
    destruct (Hentries f slot arity Hentry) as [perm [Hslot Hrows]].
    exists slot, perm. split; [exact Hslot |].
    exact (proj2 (proj2 (Hrows k (Some (Id i)) Hrow))).
  Qed.

  (** Executable and ghost enumerations differ only in their order. *)
  Lemma enumerated_rows_permutation : forall cs db,
    D.wf db -> NoDup (map fst cs) ->
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    (forall g key outid, row (D.view db) g key (Some (Id outid)) -> In g (map fst cs)) ->
    Permutation (enumerated_rows cs db) (Rows.rows db).
  Proof.
    intros cs db Hwf Hnames Hentries Hcovers. apply NoDup_Permutation.
    - now apply enumerated_rows_nodup.
    - apply Rows.rows_nodup.
    - intros [[f k] i]. split.
      + intro Hin. pose proof (enumerated_rows_sound cs db f k i Hwf Hentries Hin) as Hrow.
        apply Rows.rows_complete; [exact Hwf |exact Hrow |].
        eapply inventory_full_slot; eassumption.
      + intro Hin. apply enumerated_rows_complete; [exact Hwf |exact Hentries |exact Hcovers |].
        now apply Rows.rows_sound.
  Qed.

  (** The stored executable row count equals the specification row count. *)
  Lemma enumerated_rows_length : forall cs db,
    D.wf db -> NoDup (map fst cs) ->
    (forall g slot arity, In (g, (slot, arity)) cs -> entry_ok db g slot arity) ->
    (forall g key outid, row (D.view db) g key (Some (Id outid)) -> In g (map fst cs)) ->
    length (enumerated_rows cs db) = length (Rows.rows db).
  Proof.
    intros cs db Hwf Hnames Hentries Hcovers.
    apply Permutation_length. now apply enumerated_rows_permutation.
  Qed.
End EnumeratedRows.

(** Flattening a list pays for each callback and each emitted element. *)
Lemma extraction_flat_map_clock : forall A B (f : A -> list B) T_f a b xs,
  (forall x, In x xs -> (T_f x <= a * N.of_nat (length (f x)) + b)%N) ->
  (List.T_flat_map f T_f xs <=
    (a + 1) * N.of_nat (length (flat_map f xs)) +
    (b + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f T_f a b xs. induction xs as [|x xs IH]; intro Hcallback.
  - time_unfold @List.T_flat_map. time_cbn. cbn [flat_map length]. nia.
  - pose proof (Hcallback x ltac:(now left)) as Hhead.
    specialize (IH ltac:(intros y Hy; apply Hcallback; now right)).
    pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happ.
    time_unfold @List.T_flat_map. time_simpl. time_cbn.
    cbn [flat_map length]. rewrite length_app, !Nat2N.inj_add. cbn [N.of_nat]. nia.
Qed.

(** Nonempty branches account for every visited child in the flattened output. *)
Lemma extraction_flat_map_live : forall A B (f : A -> list B) xs,
  (forall x, In x xs -> f x <> []) -> length xs <= length (flat_map f xs).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intro Hlive; [cbn; lia |].
  specialize (IH ltac:(intros y Hy; apply Hlive; now right)).
  pose proof (Hlive x ltac:(now left)) as Hhead.
  assert (Hlength : 1 <= length (f x)).
  { destruct (f x); [contradiction |cbn; lia]. }
  cbn [flat_map length]. rewrite length_app. lia.
Qed.

(** Productive index walks charge depth only to complete output paths. *)
Lemma T_index_paths_productive : forall V child T_child children T_children
    (valid : nat -> positive -> Prop) b,
  (1 <= b)%N ->
  (forall rest node c, valid (S rest) node -> In c (children node) ->
    (T_child node c <= b)%N) ->
  (forall rest node, valid (S rest) node ->
    (T_children node <= b * N.of_nat (length (children node) + 1))%N) ->
  (forall rest node c, valid (S rest) node -> In c (children node) ->
    exists next, child node c = Some next /\ valid rest next /\
      @index_paths V child children rest next <> []) ->
  forall fuel node, valid fuel node ->
    (T_index_paths child T_child children T_children fuel node <=
      32 * b * N.of_nat (fuel * length (index_paths child children fuel node)) +
      4 * b)%N.
Proof.
  intros V child T_child children T_children valid b Hb Hchild Hchildren Hlive fuel.
  induction fuel as [|rest IH]; intros node Hvalid.
  - time_unfold @T_index_paths. time_cbn. nia.
  - set (branch := fun c => match child node c with
      | Some next => map (cons c) (index_paths child children rest next)
      | None => [] end).
    set (clock := fun c => (1 + (T_child node c + match child node c with
      | Some next => T_index_paths child T_child children T_children rest next +
        ListDef.T_map (cons c) (fun _ => 1%N) (index_paths child children rest next)
      | None => 0 end))%N).
    assert (Hcallback : forall c, In c (children node) ->
      (clock c <= (32 * b * N.of_nat rest + 2) * N.of_nat (length (branch c)) +
        7 * b)%N).
    { intros c Hin. destruct (Hlive rest node c Hvalid Hin)
        as [next [Hnext [Hnextvalid Hnonempty]]].
      pose proof (Hchild rest node c Hvalid Hin) as Hprobe.
      pose proof (IH next Hnextvalid) as Hwalk.
      pose proof (ListDef.T_map_le (cons c) (fun _ => 1%N) 1%N
        (index_paths child children rest next) ltac:(intro; reflexivity)) as Hmap.
      unfold clock, branch. rewrite Hnext, length_map.
      rewrite Nat2N.inj_mul in Hwalk. nia. }
    pose proof (extraction_flat_map_clock _ _ branch clock
      (32 * b * N.of_nat rest + 2)%N (7 * b)%N (children node) Hcallback) as Hflat.
    assert (Hcount : length (children node) <= length (flat_map branch (children node))).
    { apply extraction_flat_map_live. intros c Hin.
      destruct (Hlive rest node c Hvalid Hin) as [next [Hnext [_ Hnonempty]]].
      unfold branch. rewrite Hnext. intro Hnil.
      apply Hnonempty. now apply map_eq_nil in Hnil. }
    pose proof (Hchildren rest node Hvalid) as Hlist.
    change (1 + (T_children node + List.T_flat_map branch clock (children node)) <=
      32 * b * N.of_nat (S rest * length (flat_map branch (children node))) + 4 * b)%N.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. rewrite Nat2N.inj_succ. nia.
Qed.

(** Splitting an output identifier reads its tuple at most twice. *)
Lemma T_extraction_decode_le : forall V f (u : list (cell V)),
  (T_extraction_decode f u <= 4 * N.of_nat (length u + 1))%N.
Proof.
  intros V f u. pose proof (List.T_rev_append_le u []) as Hfirst.
  assert (Hlength : length (rev_append u []) = length u).
  { rewrite <- rev_alt, length_rev. reflexivity. }
  time_unfold @T_extraction_decode. time_simpl. time_cbn.
  destruct (rev_append u []) as [|[i|v] tail] eqn:Hreverse; try nia.
  pose proof (List.T_rev_append_le tail []) as Hsecond.
  cbn [length] in Hlength. rewrite !Nat2N.inj_add in *. nia.
Qed.

(** One-element images preserve the number of source paths. *)
Lemma extraction_flat_map_singletons : forall A B (f : A -> list B) xs,
  (forall x, In x xs -> length (f x) = 1) -> length (flat_map f xs) = length xs.
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intro Hsingle; [reflexivity |].
  cbn [flat_map length]. rewrite length_app, Hsingle by now left.
  rewrite IH; [reflexivity |]. intros y Hy. apply Hsingle. now right.
Qed.

(** A slot's logarithmic lookup budget fits its binary syntax. *)
Lemma inventory_slot_log_width : forall n,
  N.to_nat (N.log2 n) + 1 <= N.size_nat n + 1.
Proof.
  assert (Hsize : forall p, Pos.to_nat (Pos.size p) = Pos.size_nat p).
  { induction p; cbn [Pos.size Pos.size_nat]; rewrite ?Pos2Nat.inj_succ, ?IHp;
      reflexivity. }
  intros [|[p|p|]]; cbn [N.log2 N.to_nat N.size_nat Pos.size_nat]; rewrite ?Hsize; lia.
Qed.

(** Scaling by positive navigation budgets covers each component's syntax allowance. *)
Lemma enumeration_scale : forall b m u, (1 <= b)%N -> (1 <= u)%N ->
  (m <= b * m * u)%N.
Proof.
  intros b m u Hb Hu. eapply N.le_trans; [|apply dag_budget_scale; exact Hu].
  replace m with (1 * m)%N at 1 by ring. now apply N.mul_le_mono_r.
Qed.

(** Slot lookup, root access, traversal and decoding fit one entry allowance. *)
Lemma enumeration_entry_budget : forall i d s q u index root paths decode,
  (1 <= u)%N -> (index <= d * (s + 1))%N -> (root <= i)%N ->
  (paths <= 128 * (i + 1) * (q + 1) * u)%N -> (decode <= 16 * (q + 1))%N ->
  (2 + index + root + paths + decode <= 256 * (i + d + 1) * (s + q + 1) * u)%N.
Proof.
  intros i d s q u index root paths decode Hu Hindex Hroot Hpaths Hdecode.
  set (b := (i + d + 1)%N). set (m := (s + q + 1)%N).
  set (budget := (b * m * u)%N).
  assert (Hb : (1 <= b)%N) by (unfold b; lia).
  assert (Hm : (1 <= m)%N) by (unfold m; lia).
  assert (Hmass : (m <= budget)%N) by (unfold budget; apply enumeration_scale; assumption).
  assert (Hslot : (s + 1 <= m)%N) by (unfold m; lia).
  assert (Hrows : (q + 1 <= m)%N) by (unfold m; lia).
  assert (Hfunction : (i + 1 <= b)%N) by (unfold b; lia).
  assert (Hdatabase : (d <= b)%N) by (unfold b; lia).
  assert (Hlookup : (index <= budget)%N).
  { eapply N.le_trans; [exact Hindex |]. eapply N.le_trans.
    - apply N.mul_le_mono; [exact Hdatabase |exact Hslot].
    - unfold budget. apply dag_budget_scale. exact Hu. }
  assert (Hroot' : (root <= budget)%N).
  { eapply N.le_trans; [exact Hroot |]. eapply N.le_trans with (m := b); [unfold b; lia |].
    eapply N.le_trans with (m := (b * m)%N); [apply dag_budget_scale; exact Hm |].
    unfold budget. apply dag_budget_scale. exact Hu. }
  assert (Hwalk : (paths <= 128 * budget)%N).
  { eapply N.le_trans; [exact Hpaths |].
    replace (128 * (i + 1) * (q + 1) * u)%N with
      (128 * ((i + 1) * (q + 1) * u))%N by ring.
    apply N.mul_le_mono_l. unfold budget. apply N.mul_le_mono_r, N.mul_le_mono;
      assumption. }
  assert (Hsplit : (decode <= 16 * budget)%N).
  { eapply N.le_trans; [exact Hdecode |]. apply N.mul_le_mono_l. lia. }
  replace (256 * (i + d + 1) * (s + q + 1) * u)%N with (256 * budget)%N
    by (unfold budget, b, m; ring).
  clear - Hlookup Hroot' Hwalk Hsplit Hmass Hm. lia.
Qed.

(** Flattening one entry spends a fixed fraction of its allowance before the tail. *)
Lemma enumeration_flat_budget : forall b u h m head tail append,
  (1 <= b)%N -> (1 <= u)%N -> (1 <= h)%N ->
  (head <= 256 * b * h * u)%N -> (tail <= 512 * b * m * u)%N -> (append <= h)%N ->
  (1 + head + tail + append <= 512 * b * (h + m) * u)%N.
Proof.
  intros b u h m head tail append Hb Hu Hh Hhead Htail Happ.
  pose proof (enumeration_scale b h u Hb Hu) as Hscale.
  replace (512 * b * (h + m) * u)%N with
    (512 * (b * h * u) + 512 * (b * m * u))%N by ring.
  replace (256 * b * h * u)%N with (256 * (b * h * u))%N in Hhead by ring.
  replace (512 * b * m * u)%N with (512 * (b * m * u))%N in Htail by ring.
  clear - Hscale Hhead Htail Happ Hh. lia.
Qed.

(** Enumeration clocks depend on live tuple paths and public index width laws. *)
Module EnumeratedRowsT (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I).
  Module Entries := EnumeratedRows V I D.
  Module Rows := Entries.Rows.

  (** Incrementing the fresh node counter adds at most one binary digit. *)
  Lemma index_counter_succ_width : forall p,
    Pos.size_nat (Pos.succ p) <= Pos.size_nat p + 1.
  Proof.
    induction p; cbn [Pos.succ Pos.size_nat]; lia.
  Qed.

  (** A listed index child occurs in a stored tuple and fits its recorded width. *)
  Lemma index_child_width : forall depth ix node pre c,
    I.wf depth ix -> I.node ix node pre -> In c (I.children ix node) ->
    cell_bits V.encode c <= I.max_cell_bits ix.
  Proof.
    intros depth ix node pre c Hwf Hnode Hin.
    destruct (proj1 (proj1 (I.children_spec depth ix node pre c Hwf Hnode)) Hin)
      as [next Hnext].
    assert (Hnextnode : I.node ix next (pre ++ [c])).
    { apply (proj1 (proj1 (I.child_spec depth ix node pre c Hwf Hnode) next)).
      exact Hnext. }
    destruct (I.node_live depth ix next (pre ++ [c]) Hwf Hnextnode
      ltac:(destruct pre; discriminate)) as [suffix Hmember].
    eapply I.max_cell_bits_mem; [exact Hwf |exact Hmember |].
    apply in_or_app. left. apply in_or_app. right. now left.
  Qed.

  (** Empty and one-cell index probes fit the database's common spending unit. *)
  Lemma stored_index_widths : forall db slot depth node pre,
    D.wf db -> I.wf depth (D.index slot false db) ->
    I.node (D.index slot false db) node pre ->
    I.width (D.index slot false db) [] + 1 <= 4 * (D.unit db + 1) /\
    forall c, In c (I.children (D.index slot false db) node) ->
      I.width (D.index slot false db) [c] + 1 <= 4 * (D.unit db + 1).
  Proof.
    intros db slot depth node pre Hwf Hindex Hnode.
    destruct (D.wmark_index db slot false Hwf) as [Hnext Hcells].
    pose proof (dag_cost_size_mono _ _ Hnext) as Hcounter.
    change (Pos.size_nat (I.next (D.index slot false db)) <=
      N.size_nat (D.wmark db)) in Hcounter.
    assert (Hunit : N.size_nat (D.wmark db) <= D.unit db) by (unfold D.unit; nia).
    pose proof (index_counter_succ_width (I.next (D.index slot false db))) as Hsucc.
    split.
    - pose proof (I.width_le (D.index slot false db) []) as Hwidth.
      change (I.width (D.index slot false db) [] <=
        Pos.size_nat (I.next (D.index slot false db) + 1) + 0 +
          I.max_cell_bits (D.index slot false db)) in Hwidth.
      rewrite Pos.add_1_r in Hwidth. lia.
    - intros c Hin. pose proof (I.width_le (D.index slot false db) [c]) as Hwidth.
      pose proof (index_child_width depth _ node pre c Hindex Hnode Hin) as Hcell.
      change (I.width (D.index slot false db) [c] <=
        Pos.size_nat (I.next (D.index slot false db) + 1) +
          Nat.max (cell_bits V.encode c) 0 + I.max_cell_bits (D.index slot false db))
        in Hwidth.
      rewrite Pos.add_1_r, Nat.max_0_r in Hwidth. lia.
  Qed.

  (** Complete inventory paths fund every navigation call and every copied prefix cell. *)
  Lemma entry_paths_clock : forall db f slot arity,
    D.wf db -> Entries.entry_ok db f slot arity ->
    (T_index_paths (I.child (D.index slot false db)) (I.T_child (D.index slot false db))
      (I.children (D.index slot false db)) (I.T_children (D.index slot false db))
      (S arity) (I.root (D.index slot false db)) <=
      128 * (I.c_ix + 1) * N.of_nat (S arity *
        length (index_paths (I.child (D.index slot false db))
          (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))) + 1) *
        N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db f slot arity Hwf Hentry.
    destruct Hentry as [perm [Hslot Hrows]].
    assert (Hentry : Entries.entry_ok db f slot arity) by (exists perm; auto).
    pose proof (D.index_wf db slot false f perm Hwf Hslot) as Hindex.
    set (ix := D.index slot false db) in *.
    set (b := (4 * (I.c_ix + 1) * N.of_nat (D.unit db + 1))%N).
    assert (Hclock : (T_index_paths (I.child ix) (I.T_child ix)
      (I.children ix) (I.T_children ix) (S arity) (I.root ix) <=
      32 * b * N.of_nat (S arity *
        length (index_paths (I.child ix) (I.children ix) (S arity) (I.root ix))) +
      4 * b)%N).
    { eapply T_index_paths_productive with
        (valid := fun remaining node => exists pre, I.node ix node pre /\
          length pre + remaining = S arity).
      - unfold b. nia.
      - intros remaining node c [pre [Hnode Hdepth]] Hin.
        pose proof (proj2 (stored_index_widths db slot (length perm) node pre
          Hwf Hindex Hnode) c Hin) as Hwidth.
        pose proof (I.T_child_le ix node c) as Htime. fold ix in Hwidth.
        unfold b. rewrite !Nat2N.inj_add in *. nia.
      - intros remaining node [pre [Hnode Hdepth]].
        pose proof (proj1 (stored_index_widths db slot (length perm) node pre
          Hwf Hindex Hnode)) as Hwidth.
        pose proof (I.T_children_le (length perm) ix node Hindex) as Htime.
        rewrite (I.degree_spec (length perm) ix node pre Hindex Hnode) in Htime.
        fold ix in Hwidth. unfold b. rewrite !Nat2N.inj_add in *. nia.
      - intros remaining node c [pre [Hnode Hdepth]] Hin.
        destruct (proj1 (proj1 (I.children_spec (length perm) ix node pre c Hindex Hnode)) Hin)
          as [next Hnext].
        exists next. split; [exact Hnext |]. split.
        + exists (pre ++ [c]). split.
          * apply (proj1 (proj1 (I.child_spec (length perm) ix node pre c
              Hindex Hnode) next)). exact Hnext.
          * rewrite length_app. cbn [length]. lia.
        + destruct (Entries.entry_child_paths_live db f slot arity node pre c next remaining
            Hwf Hentry Hnode Hdepth Hnext) as [suffix Hinpath].
          fold ix in Hinpath. intro Hempty. rewrite Hempty in Hinpath. contradiction.
      - exists []. split; [apply I.node_root with (length perm); exact Hindex |reflexivity]. }
    unfold b in Hclock. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Every full-depth inventory path decodes to exactly one constructor row. *)
  Lemma entry_rows_paths_length : forall db f slot arity,
    D.wf db -> Entries.entry_ok db f slot arity ->
    length (Entries.entry_rows db (f, (slot, arity))) =
      length (index_paths (I.child (D.index slot false db))
        (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))).
  Proof.
    intros db f slot arity Hwf Hentry. unfold Entries.entry_rows, inventory_entry_rows.
    apply extraction_flat_map_singletons. intros u Hin.
    destruct (Entries.entry_paths_sound db f slot arity u Hwf Hentry Hin)
      as [k [i [_ [_ ->]]]]. rewrite extraction_decode_complete. reflexivity.
  Qed.

  (** Splitting all paths costs their total tuple length plus a constant empty walk. *)
  Lemma entry_decode_clock : forall db f slot arity,
    D.wf db -> Entries.entry_ok db f slot arity ->
    (List.T_flat_map (extraction_decode f) (T_extraction_decode f)
      (index_paths (I.child (D.index slot false db))
        (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))) <=
      16 * N.of_nat (S arity * length (Entries.entry_rows db (f, (slot, arity))) + 1))%N.
  Proof.
    intros db f slot arity Hwf Hentry.
    pose proof (entry_rows_paths_length db f slot arity Hwf Hentry) as Hlength.
    set (paths := index_paths (I.child (D.index slot false db))
      (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db))) in *.
    assert (Hcallback : forall u, In u paths ->
      (T_extraction_decode f u <= 0 * N.of_nat (length (extraction_decode f u)) +
        4 * N.of_nat (S arity + 1))%N).
    { intros u Hin. pose proof (T_extraction_decode_le V.t f u) as Htime.
      pose proof (index_paths_length V.t _ _ _ _ u Hin) as Hdepth. rewrite Hdepth in Htime.
      exact Htime. }
    pose proof (extraction_flat_map_clock _ _ (extraction_decode f) (T_extraction_decode f)
      0%N (4 * N.of_nat (S arity + 1))%N paths Hcallback) as Hflat.
    change (length (Entries.entry_rows db (f, (slot, arity))) = length paths) in Hlength.
    change (List.T_flat_map (extraction_decode f) (T_extraction_decode f) paths <=
      16 * N.of_nat (S arity * length (flat_map (extraction_decode f) paths) + 1))%N.
    change (length (flat_map (extraction_decode f) paths) = length paths) in Hlength.
    rewrite <- Hlength in Hflat. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *.
    rewrite Nat2N.inj_succ in *. nia.
  Qed.

  (** An inventory entry pays for slot syntax and the tuples that it actually emits. *)
  Lemma entry_rows_clock : forall db f slot arity,
    D.wf db -> Entries.entry_ok db f slot arity ->
    (T_inventory_entry_rows (fun s => D.index s false db)
      (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root (f, (slot, arity)) <=
      256 * (I.c_ix + D.c_db + 1) *
        N.of_nat (N.size_nat slot + S arity *
          length (Entries.entry_rows db (f, (slot, arity))) + 1) *
        N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db f slot arity Hwf Hentry.
    pose proof (entry_paths_clock db f slot arity Hwf Hentry) as Hpaths.
    pose proof (entry_decode_clock db f slot arity Hwf Hentry) as Hdecode.
    pose proof (entry_rows_paths_length db f slot arity Hwf Hentry) as Hlength.
    pose proof (D.T_index_le slot false db) as Hindex.
    pose proof (inventory_slot_log_width slot) as Hslot.
    pose proof (I.T_root_le (D.index slot false db)) as Hroot.
    rewrite <- Hlength in Hpaths.
    set (count := length (Entries.entry_rows db (f, (slot, arity)))) in *.
    set (paths := T_index_paths (I.child (D.index slot false db))
      (I.T_child (D.index slot false db)) (I.children (D.index slot false db))
      (I.T_children (D.index slot false db)) (S arity) (I.root (D.index slot false db))) in *.
    set (decode := List.T_flat_map (extraction_decode f) (T_extraction_decode f)
      (index_paths (I.child (D.index slot false db))
        (I.children (D.index slot false db)) (S arity) (I.root (D.index slot false db)))) in *.
    change (1 + ((1 + D.T_index slot false db) +
      (I.T_root (D.index slot false db) + paths + decode)) <=
      256 * (I.c_ix + D.c_db + 1) * N.of_nat (N.size_nat slot + S arity * count + 1) *
        N.of_nat (D.unit db + 1))%N.
    assert (Hindex' : (D.T_index slot false db <=
      D.c_db * (N.of_nat (N.size_nat slot) + 1))%N).
    { eapply N.le_trans; [exact Hindex |]. apply N.mul_le_mono_l.
      rewrite Nat2N.inj_add. cbn [N.of_nat]. lia. }
    rewrite (Nat2N.inj_add (S arity * count) 1) in Hpaths, Hdecode.
    pose proof (enumeration_entry_budget I.c_ix D.c_db (N.of_nat (N.size_nat slot))
      (N.of_nat (S arity * count))
      (N.of_nat (D.unit db + 1)) (D.T_index slot false db)
      (I.T_root (D.index slot false db)) paths decode
      ltac:(lia) Hindex' Hroot Hpaths Hdecode) as Hbudget.
    rewrite (Nat2N.inj_add (N.size_nat slot + S arity * count) 1),
      (Nat2N.inj_add (N.size_nat slot) (S arity * count)).
    eapply N.le_trans; [|exact Hbudget]. lia.
  Qed.

  (** Empty slots contribute no arity charge, and nonempty slots use a recorded row arity. *)
  Lemma entry_arity_mass : forall db f slot arity,
    D.wf db -> Entries.entry_ok db f slot arity ->
    S arity * length (Entries.entry_rows db (f, (slot, arity))) <=
      (Rows.maximum_arity (Rows.rows db) + 1) *
        length (Entries.entry_rows db (f, (slot, arity))).
  Proof.
    intros db f slot arity Hwf Hentry.
    destruct (Entries.entry_rows db (f, (slot, arity))) as [|[[g k] i] rest] eqn:Hrows;
      [cbn; lia |].
    assert (Hin : In (g, k, i) (Entries.entry_rows db (f, (slot, arity)))).
    { rewrite Hrows. now left. }
    pose proof (Entries.entry_rows_sound db f slot arity g k i Hwf Hentry Hin) as Hrow.
    pose proof (Entries.entry_rows_name db f slot arity g k i Hin) as Hname. subst g.
    destruct Hentry as [perm [Hslot Hshape]].
    destruct (Hshape k (Some (Id i)) Hrow) as [Harity [_ Hfull]].
    assert (Hmember : In (f, k, i) (Rows.rows db)).
    { apply Rows.rows_complete; [exact Hwf |exact Hrow |]. exists slot, perm. auto. }
    pose proof (Rows.maximum_arity_member (Rows.rows db) f k i Hmember) as Hbound.
    cbn [length]. nia.
  Qed.

  (** Concatenating entry enumerations pays their aggregate row count and inventory bits. *)
  Lemma inventory_flat_clock : forall db cs, D.wf db ->
    (forall f slot arity, In (f, (slot, arity)) cs -> Entries.entry_ok db f slot arity) ->
    (List.T_flat_map
      (inventory_entry_rows (fun s => D.index s false db) I.child I.children I.root)
      (T_inventory_entry_rows (fun s => D.index s false db)
        (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
        I.root I.T_root) cs <=
      512 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (Rows.maximum_arity (Rows.rows db) + 1) *
          length (Entries.enumerated_rows cs db) + 1) * N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db cs Hwf.
    set (emit := inventory_entry_rows (fun s => D.index s false db)
      I.child I.children I.root).
    set (clock := T_inventory_entry_rows (fun s => D.index s false db)
      (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root).
    set (a := Rows.maximum_arity (Rows.rows db)).
    change ((forall f slot arity, In (f, (slot, arity)) cs ->
      Entries.entry_ok db f slot arity) ->
      (List.T_flat_map emit clock cs <= 512 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (a + 1) * length (flat_map emit cs) + 1) *
        N.of_nat (D.unit db + 1))%N).
    induction cs as [|[f [slot arity]] cs IH]; intro Hentries.
    - change (1 <= 512 * (I.c_ix + D.c_db + 1) *
        N.of_nat (0 + (a + 1) * 0 + 1) * N.of_nat (D.unit db + 1))%N.
      rewrite Nat.mul_0_r. cbn [N.of_nat]. nia.
    - pose proof (Hentries f slot arity ltac:(now left)) as Hentry.
      pose proof (entry_rows_clock db f slot arity Hwf Hentry) as Hhead.
      pose proof (entry_arity_mass db f slot arity Hwf Hentry) as Hmass.
      specialize (IH ltac:(intros g s n Hin; apply Hentries; now right)).
      set (headrows := emit (f, (slot, arity))). set (tailrows := flat_map emit cs).
      change (clock (f, (slot, arity)) <= 256 * (I.c_ix + D.c_db + 1) *
        N.of_nat (N.size_nat slot + S arity * length headrows + 1) *
        N.of_nat (D.unit db + 1))%N in Hhead.
      change (S arity * length headrows <= (a + 1) * length headrows) in Hmass.
      pose proof (Datatypes.T_app_le headrows tailrows) as Happ.
      set (h := N.of_nat (Pos.size_nat f + N.size_nat slot + 1 +
        (a + 1) * length headrows)).
      set (m := N.of_nat (inventory_bits cs + (a + 1) * length tailrows + 1)).
      assert (Hhead' : (clock (f, (slot, arity)) <=
        256 * (I.c_ix + D.c_db + 1) * h * N.of_nat (D.unit db + 1))%N).
      { eapply N.le_trans; [exact Hhead |]. apply N.mul_le_mono_r, N.mul_le_mono_l.
        unfold h. clear - Hmass. lia. }
      assert (Happ' : (Datatypes.T_app headrows tailrows <= h)%N).
      { eapply N.le_trans; [exact Happ |]. unfold h.
        replace (N.of_nat (length headrows) + 1)%N with
          (N.of_nat (length headrows + 1)) by (rewrite Nat2N.inj_add; reflexivity).
        clear - Hmass. nia. }
      pose proof (enumeration_flat_budget (I.c_ix + D.c_db + 1)%N
        (N.of_nat (D.unit db + 1)) h m _ _ _ ltac:(lia) ltac:(lia)
        ltac:(unfold h; lia) Hhead' IH Happ') as Hbudget.
      change (1 + (clock (f, (slot, arity)) + List.T_flat_map emit clock cs +
        Datatypes.T_app headrows tailrows) <= 512 * (I.c_ix + D.c_db + 1) *
        N.of_nat (Pos.size_nat f + N.size_nat slot + 1 + inventory_bits cs +
          (a + 1) * length (headrows ++ tailrows) + 1) * N.of_nat (D.unit db + 1))%N.
      rewrite length_app.
      assert (Hsize : (h + m)%N = N.of_nat (Pos.size_nat f + N.size_nat slot + 1 +
        inventory_bits cs + (a + 1) * (length headrows + length tailrows) + 1)).
      { unfold h, m. rewrite <- Nat2N.inj_add. f_equal. ring. }
      rewrite Hsize in Hbudget. eapply N.le_trans; [|exact Hbudget]. lia.
  Qed.

  (** Executable inventory enumeration has an additive syntax and live-row budget. *)
  Lemma inventory_rows_clock : forall db cs, D.wf db ->
    (forall f slot arity, In (f, (slot, arity)) cs -> Entries.entry_ok db f slot arity) ->
    (T_inventory_rows (fun s => D.index s false db)
      (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root cs <=
      1024 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (Rows.maximum_arity (Rows.rows db) + 1) *
          length (Entries.enumerated_rows cs db) + 1) * N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db cs Hwf Hentries. pose proof (inventory_flat_clock db cs Hwf Hentries) as Hflat.
    set (clock := List.T_flat_map
      (inventory_entry_rows (fun s => D.index s false db) I.child I.children I.root)
      (T_inventory_entry_rows (fun s => D.index s false db)
        (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
        I.root I.T_root) cs) in *.
    set (mass := N.of_nat (inventory_bits cs + (Rows.maximum_arity (Rows.rows db) + 1) *
      length (Entries.enumerated_rows cs db) + 1)) in *.
    set (b := (I.c_ix + D.c_db + 1)%N) in *.
    set (u := N.of_nat (D.unit db + 1)) in *.
    change (1 + clock <= 1024 * b * mass * u)%N.
    assert (Hmass : (1 <= mass)%N) by (unfold mass; lia).
    pose proof (enumeration_scale b mass u ltac:(unfold b; lia) ltac:(unfold u; lia)) as Hscale.
    replace (512 * b * mass * u)%N with (512 * (b * mass * u))%N in Hflat by ring.
    replace (1024 * b * mass * u)%N with (1024 * (b * mass * u))%N by ring.
    clear - Hflat Hmass Hscale. lia.
  Qed.

  (** Semantic row arities and an executable count bound suffice for the public clock budget. *)
  Lemma inventory_rows_clock_bounded : forall db cs arity count,
    D.wf db ->
    (forall f slot n, In (f, (slot, n)) cs -> Entries.entry_ok db f slot n) ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> length k <= arity) ->
    length (Entries.enumerated_rows cs db) <= count ->
    (T_inventory_rows (fun s => D.index s false db)
      (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root cs <=
      1024 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (arity + 1) * count + 1) *
        N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db cs arity count Hwf Hentries Harity Hcount.
    pose proof (inventory_rows_clock db cs Hwf Hentries) as Hclock.
    assert (Hmaximum : Rows.maximum_arity (Rows.rows db) <= arity).
    { destruct (Rows.maximum_arity_attained (Rows.rows db))
        as [Hzero |[f [k [i [Hin Heq]]]]]; [lia |].
      rewrite <- Heq. apply Harity with f i. now apply Rows.rows_sound. }
    assert (Hmass : (Rows.maximum_arity (Rows.rows db) + 1) *
      length (Entries.enumerated_rows cs db) <= (arity + 1) * count).
    { apply Nat.mul_le_mono; lia. }
    eapply N.le_trans; [exact Hclock |]. apply N.mul_le_mono_r, N.mul_le_mono_l.
    clear - Hmass. lia.
  Qed.

  (** A complete duplicate-free inventory replaces its executable count by the ghost count. *)
  Lemma inventory_rows_clock_exact : forall db cs,
    D.wf db -> NoDup (map fst cs) ->
    (forall f slot arity, In (f, (slot, arity)) cs -> Entries.entry_ok db f slot arity) ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> In f (map fst cs)) ->
    (T_inventory_rows (fun s => D.index s false db)
      (fun s => (1 + D.T_index s false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root cs <=
      1024 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (Rows.maximum_arity (Rows.rows db) + 1) *
          length (Rows.rows db) + 1) * N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db cs Hwf Hnames Hentries Hcovers.
    pose proof (inventory_rows_clock db cs Hwf Hentries) as Hclock.
    rewrite (Entries.enumerated_rows_length cs db Hwf Hnames Hentries Hcovers) in Hclock.
    exact Hclock.
  Qed.
End EnumeratedRowsT.

(** Canonical database rows and exact finite-row witnesses have the same constructor trees. *)
Module SearchDatabase (V : VALUE) (I : INDEX V) (D : DATABASE V I).

  (** Every stored key cell is already its own canonical representative. *)
  Lemma search_canonical_key : forall db f k o,
    D.canonical db -> row (D.view db) f k o -> map (D.canon db) k = k.
  Proof.
    intros db f k o Hcanonical Hrow.
    rewrite <- (map_id k) at 2. apply map_ext_in.
    intros [i|v] Hin; [|reflexivity]. cbn [D.canon].
    f_equal. apply (Hcanonical f k o Hrow i). apply in_or_app. now left.
  Qed.

  (** A represented database tree appears in every complete exact constructor-row list. *)
  Lemma database_search_represents : forall db rs,
    D.wf db -> D.canonical db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> In (f, k, i) rs) ->
    forall c e, represents (D.view db) c e -> search_represents rs (D.canon db c) e.
  Proof.
    intros db rs Hwf Hcanonical Hrows c e Hrep.
    induction Hrep as [v|f k i j args Hrow Hsame Hargs IHargs].
    - constructor.
    - assert (Hj : D.repr db j = j).
      { apply (Hcanonical f k (Some (Id j)) Hrow j).
        apply in_or_app. right. now left. }
      pose proof (proj1 (D.same_repr db i j Hwf) Hsame) as Hij.
      rewrite Hj in Hij. cbn [D.canon]. rewrite Hij.
      eapply search_rep_app with (k := k); [exact (Hrows f k j Hrow)|].
      assert (Hchildren : Forall2 (search_represents rs) (map (D.canon db) k) args).
      { clear Hrow Hsame Hj Hij.
        induction IHargs as [|c e ks es Hr Hhead Htail Hall IH]; cbn [map].
        - constructor.
        - constructor; assumption. }
      now rewrite (search_canonical_key db f k (Some (Id j)) Hcanonical Hrow) in Hchildren.
  Qed.

  (** A finite tree over exact stored rows is represented by the database. *)
  Lemma search_database_represents : forall db rs,
    D.wf db ->
    (forall f k i, In (f, k, i) rs -> row (D.view db) f k (Some (Id i))) ->
    forall c e, search_represents rs c e -> represents (D.view db) c e.
  Proof.
    intros db rs Hwf Hrows c e Hrep.
    induction Hrep as [v|f k i args Hrow Hargs IHargs].
    - constructor.
    - eapply rep_app with (k := k) (j := i).
      + exact (Hrows f k i Hrow).
      + apply (proj2 (D.same_repr db i i Hwf)). reflexivity.
      + clear Hrow.
        induction IHargs as [|c e ks es Hr Hhead Htail Hall IH].
        * constructor.
        * constructor; assumption.
  Qed.

End SearchDatabase.
(** The operations-only search resumes each row at its first unknown child. *)
Module SearchCode (V : VALUE_OPS) (C : COST_OPS V) (Q : PQ_OPS).

  (** A scan returns its first missing child or all child costs in their original order. *)
  Fixpoint search_scan (costs : ptrie N) (acc : list N) (todo : list (cell V.t))
      : (positive * (list (cell V.t) * list N)) + list N :=
    match todo with
    | [] => inr (rev_append acc [])
    | Val v :: rest => search_scan costs (C.val_cost v :: acc) rest
    | Id i :: rest =>
      match trie_get i costs with
      | Some n => search_scan costs (n :: acc) rest
      | None => inl (i, (todo, acc))
      end
    end.

  (** Parking adds one frame to the class on which its next scan depends. *)
  Definition search_park {DB} (i : positive) (frame : extraction_frame V.t)
      (s : extraction_state V.t DB Q.t) : extraction_state V.t DB Q.t :=
    let waiting := match trie_get i (search_waiters s) with
      | Some frames => frames
      | None => []
      end in
    search_restate s (search_final_costs s) (search_candidates s)
      (PTrieCode.set i (frame :: waiting) (search_waiters s))
      (search_queue s) (search_finalised s).

  (** The candidate row changes only when its class receives a strictly smaller ready cost. *)
  Definition search_offer {DB} (i : positive) (n : N) (row : extraction_row V.t)
      (s : extraction_state V.t DB Q.t) : extraction_state V.t DB Q.t :=
    let better := match trie_get i (search_candidates s) with
      | Some (old, _) => N.ltb n old
      | None => true
      end in
    if better then
      search_restate s (search_final_costs s)
        (PTrieCode.set i (n, row) (search_candidates s)) (search_waiters s)
        (Q.push n i (search_queue s)) (search_finalised s)
    else s.

  (** A live row is parked once or offered after all its children become final. *)
  Definition search_resume {DB} (frame : extraction_frame V.t)
      (s : extraction_state V.t DB Q.t) : extraction_state V.t DB Q.t :=
    let '(f, key, i) := frame_row frame in
    match trie_get i (search_final_costs s) with
    | Some _ => s
    | None =>
      match search_scan (search_final_costs s) (frame_costs frame) (frame_rest frame) with
      | inl (child, (rest, costs)) =>
        search_park child (ExtractionFrame (f, key, i) rest costs) s
      | inr costs => search_offer i (C.fn_cost f costs) (f, key) s
      end
    end.

  (** Resuming a detached waiting list consumes it in one forward pass. *)
  Fixpoint search_resume_list {DB} (frames : list (extraction_frame V.t))
      (s : extraction_state V.t DB Q.t) : extraction_state V.t DB Q.t :=
    match frames with
    | [] => s
    | frame :: rest => search_resume_list rest (search_resume frame s)
    end.

  (** Initialization stores its finite source before registering the rows. *)
  Definition search_start {DB} (db : DB) (rows : list (search_row V.t))
      : extraction_state V.t DB Q.t :=
    ExtractionState db rows (length rows) Empty Empty Empty Q.empty [].

  (** Every input row is initially scanned, parked or offered, with no finalized class. *)
  Definition search_initial {DB} (db : DB) (rows : list (search_row V.t))
      : extraction_state V.t DB Q.t :=
    search_resume_list (map search_new_frame rows) (search_start db rows).

  (** Finalizing a class detaches the rows waiting on that class before resuming them. *)
  Definition search_finish {DB} (i : positive) (n : N) (row : extraction_row V.t)
      (queue : Q.t) (s : extraction_state V.t DB Q.t) : extraction_state V.t DB Q.t :=
    let waiting := match trie_get i (search_waiters s) with
      | Some frames => frames
      | None => []
      end in
    let next := search_restate s
      (PTrieCode.set i n (search_final_costs s))
      (PTrieCode.remove i (search_candidates s))
      (PTrieCode.remove i (search_waiters s)) queue
      ((i, (n, row)) :: search_finalised s) in
    search_resume_list waiting next.

  (** Cached emptiness stops without a heap pop; impossible malformed states remain unchanged. *)
  Definition search_step {DB} (s : extraction_state V.t DB Q.t)
      : extraction_state V.t DB Q.t + extraction_best V.t :=
    match Q.size (search_queue s) with
    | 0%N => inr (search_finalised s)
    | Npos _ =>
      match Q.pop (search_queue s) with
      | None => inl s
      | Some (n, i, queue) =>
        match trie_get i (search_candidates s), trie_get i (search_final_costs s) with
        | Some (_, row), None => inl (search_finish i n row queue s)
        | _, _ => inl s
        end
      end
    end.

  (** One more step than the stored row count suffices to return the completed table. *)
  Definition best_rows {DB} (db : DB) (rows : list (search_row V.t)) : extraction_best V.t :=
    let initial := search_initial db rows in
    match loop_fuel search_step (S (search_row_count initial)) initial with
    | inl unfinished => search_finalised unfinished
    | inr finished => finished
    end.

End SearchCode.

(** Search bookkeeping relates class maps to the finite row source. *)
Module SearchFacts (V : VALUE) (C : COST V) (Q : PQ).
  Include SearchCode V C Q.
  Module Semantics := SearchSemantics V C.

  (** Registering rows changes neither the source nor the finalized table. *)
  Definition search_stable {DB} (s t : extraction_state V.t DB Q.t) : Prop :=
    search_database t = search_database s /\
    search_rows t = search_rows s /\
    search_row_count t = search_row_count s /\
    search_final_costs t = search_final_costs s /\
    search_finalised t = search_finalised s.

  Lemma search_stable_refl : forall DB (s : extraction_state V.t DB Q.t),
    search_stable s s.
  Proof.
    intros DB s. repeat split; reflexivity.
  Qed.

  Lemma search_stable_trans : forall DB (s t u : extraction_state V.t DB Q.t),
    search_stable s t -> search_stable t u -> search_stable s u.
  Proof.
    intros DB s t u [Hdb [Hrows [Hcount [Hcost Hfinal]]]]
      [Hdb' [Hrows' [Hcount' [Hcost' Hfinal']]]].
    unfold search_stable. repeat split; congruence.
  Qed.

  Lemma search_park_stable : forall DB i frame (s : extraction_state V.t DB Q.t),
    search_stable s (search_park i frame s).
  Proof.
    intros DB i frame s. unfold search_park, search_stable, search_restate.
    repeat split; reflexivity.
  Qed.

  Lemma search_offer_stable : forall DB i n row (s : extraction_state V.t DB Q.t),
    search_stable s (search_offer i n row s).
  Proof.
    intros DB i n row s. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|];
      [destruct (N.ltb n old)|]; unfold search_stable, search_restate;
      repeat split; reflexivity.
  Qed.

  Lemma search_resume_stable : forall DB frame (s : extraction_state V.t DB Q.t),
    search_stable s (search_resume frame s).
  Proof.
    intros DB [row rest costs] s. destruct row as [[f key] i]. unfold search_resume.
    cbn [frame_row frame_costs frame_rest].
    destruct (trie_get i (search_final_costs s)); [apply search_stable_refl|].
    destruct (search_scan (search_final_costs s) costs rest)
      as [[child [suffix values]]|values].
    - apply search_park_stable.
    - apply search_offer_stable.
  Qed.

  Lemma search_resume_list_stable : forall DB frames (s : extraction_state V.t DB Q.t),
    search_stable s (search_resume_list frames s).
  Proof.
    intros DB frames. induction frames as [|frame rest IH]; intro s.
    - apply search_stable_refl.
    - cbn [search_resume_list]. eapply search_stable_trans.
      + apply search_resume_stable.
      + apply IH.
  Qed.

  (** Initialization records its source and has no finalized class or cost. *)
  Lemma search_initial_fields : forall DB (db : DB) rows,
    search_database (search_initial db rows) = db /\
    search_rows (search_initial db rows) = rows /\
    search_row_count (search_initial db rows) = length rows /\
    search_final_costs (search_initial db rows) = Empty /\
    search_finalised (search_initial db rows) = [].
  Proof.
    intros DB db rows. unfold search_initial.
    exact (search_resume_list_stable DB (map search_new_frame rows) (search_start db rows)).
  Qed.

  (** Finishing records one chosen row and leaves the source fields unchanged. *)
  Lemma search_finish_fields : forall DB i n row queue (s : extraction_state V.t DB Q.t),
    search_database (search_finish i n row queue s) = search_database s /\
    search_rows (search_finish i n row queue s) = search_rows s /\
    search_row_count (search_finish i n row queue s) = search_row_count s /\
    search_final_costs (search_finish i n row queue s) =
      PTrieCode.set i n (search_final_costs s) /\
    search_finalised (search_finish i n row queue s) =
      (i, (n, row)) :: search_finalised s.
  Proof.
    intros DB i n row queue s. unfold search_finish.
    exact (search_resume_list_stable DB
      (match trie_get i (search_waiters s) with Some frames => frames | None => [] end)
      (search_restate s (PTrieCode.set i n (search_final_costs s))
        (PTrieCode.remove i (search_candidates s))
        (PTrieCode.remove i (search_waiters s)) queue
        ((i, (n, row)) :: search_finalised s))).
  Qed.

  (** Queue priorities and cached size agree with the live candidate trie. *)
  Definition search_queue_agrees (candidates : ptrie (N * extraction_row V.t))
      (queue : Q.t) : Prop :=
    Q.wf queue /\
    (forall i, Q.prio queue i = option_map fst (trie_get i candidates)) /\
    Q.size queue = N.of_nat (length (PTrieCode.elements candidates)).

  Lemma search_queue_empty : search_queue_agrees Empty Q.empty.
  Proof.
    split; [apply Q.wf_empty|]. split.
    - intro i. rewrite Q.prio_empty, PTrie.get_empty. reflexivity.
    - apply Q.size_empty.
  Qed.

  (** Decreasing or creating a candidate preserves the queue correspondence. *)
  Lemma search_queue_set : forall candidates queue i n row,
    search_queue_agrees candidates queue ->
    (match trie_get i candidates with Some (old, _) => (n <= old)%N | None => True end) ->
    search_queue_agrees (PTrieCode.set i (n, row) candidates) (Q.push n i queue).
  Proof.
    intros candidates queue i n row [Hwf [Hprio Hsize]] Hbetter.
    split; [now apply Q.wf_push|]. split.
    - intro j. destruct (Pos.eq_dec j i) as [->|Hneq].
      + rewrite Q.prio_push, PTrie.get_set_same, Hprio.
        destruct (trie_get i candidates) as [[old choice]|]; cbn in *.
        * now rewrite N.min_l.
        * reflexivity.
      + rewrite Q.prio_push_other by congruence.
        rewrite PTrie.get_set_other by exact Hneq. apply Hprio.
    - rewrite Q.size_push by exact Hwf. rewrite Hprio, Heap.live_length_set.
      unfold PTrieCode.get.
      destruct (trie_get i candidates) as [[old choice]|]; cbn [option_map fst].
      + exact Hsize.
      + rewrite Nat2N.inj_succ. now rewrite Hsize.
  Qed.

  (** Popping removes the same live candidate and returns its recorded priority. *)
  Lemma search_queue_remove : forall candidates queue i n queue',
    search_queue_agrees candidates queue -> Q.pop queue = Some (n, i, queue') ->
    exists row, trie_get i candidates = Some (n, row) /\
      search_queue_agrees (PTrieCode.remove i candidates) queue'.
  Proof.
    intros candidates queue i n queue' [Hwf [Hprio Hsize]] Hpop.
    destruct (Q.pop_min queue n i queue' Hwf Hpop)
      as [Hget [Hminimum [Hremoved Hothers]]].
    rewrite Hprio in Hget.
    destruct (trie_get i candidates) as [[old row]|] eqn:Hcandidate; [|discriminate].
    cbn [option_map fst] in Hget. injection Hget as <-.
    exists row. split; [reflexivity|]. split.
    - eapply Q.wf_pop; eassumption.
    - split.
      + intro j. destruct (Pos.eq_dec j i) as [->|Hneq].
        * rewrite PTrie.get_remove_same, Hremoved. reflexivity.
        * rewrite Hothers by exact Hneq.
          rewrite PTrie.get_remove_other by exact Hneq. apply Hprio.
      + pose proof (Q.size_pop queue old i queue' Hwf Hpop) as Hpopsize.
        pose proof (Heap.live_length_remove _ i (old, row) candidates Hcandidate) as Hlength.
        rewrite Hlength, Nat2N.inj_succ in Hsize. lia.
  Qed.

  (** A positive cached size has a real pop result in every consistent search queue. *)
  Lemma search_queue_positive : forall candidates queue,
    search_queue_agrees candidates queue -> Q.size queue <> 0%N ->
    exists n i queue', Q.pop queue = Some (n, i, queue').
  Proof.
    intros candidates queue [Hwf [Hprio Hsize]] Hnonzero.
    destruct (Q.pop queue) as [[[n i] queue']|] eqn:Hpop.
    - exists n, i, queue'. reflexivity.
    - pose proof (proj1 (Q.pop_none queue Hwf) Hpop) as Hemptyprio.
      assert (Hempty : candidates = Empty).
      { apply PTrie.ext. intro i. rewrite PTrie.get_empty.
        specialize (Hprio i). rewrite Hemptyprio in Hprio.
        destruct (trie_get i candidates) as [[n row]|] eqn:Hcandidate;
          [discriminate|exact Hcandidate]. }
      subst candidates. cbn in Hsize. contradiction.
  Qed.

  (** Zero cached size has no live priority. *)
  Lemma search_queue_zero : forall candidates queue,
    search_queue_agrees candidates queue -> Q.size queue = 0%N ->
    forall i, Q.prio queue i = None.
  Proof.
    intros candidates queue [Hwf [Hprio Hsize]] Hzero i.
    destruct (Q.pop queue) as [[[n j] queue']|] eqn:Hpop.
    - pose proof (Q.size_pop queue n j queue' Hwf Hpop). lia.
    - exact (proj1 (Q.pop_none queue Hwf) Hpop i).
  Qed.

  Lemma search_park_queue : forall DB i frame (s : extraction_state V.t DB Q.t),
    search_queue_agrees (search_candidates s) (search_queue s) ->
    search_queue_agrees (search_candidates (search_park i frame s))
      (search_queue (search_park i frame s)).
  Proof.
    intros DB i frame s Hqueue. exact Hqueue.
  Qed.

  Lemma search_offer_queue : forall DB i n row (s : extraction_state V.t DB Q.t),
    search_queue_agrees (search_candidates s) (search_queue s) ->
    search_queue_agrees (search_candidates (search_offer i n row s))
      (search_queue (search_offer i n row s)).
  Proof.
    intros DB i n row s Hqueue. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|] eqn:Hget.
    - destruct (N.ltb n old) eqn:Hbetter; [|exact Hqueue].
      apply search_queue_set; [exact Hqueue|]. rewrite Hget.
      apply N.ltb_lt in Hbetter. lia.
    - apply search_queue_set; [exact Hqueue|]. now rewrite Hget.
  Qed.

  Lemma search_resume_queue : forall DB frame (s : extraction_state V.t DB Q.t),
    search_queue_agrees (search_candidates s) (search_queue s) ->
    search_queue_agrees (search_candidates (search_resume frame s))
      (search_queue (search_resume frame s)).
  Proof.
    intros DB [row rest costs] s Hqueue. destruct row as [[f key] i].
    unfold search_resume. cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)); [exact Hqueue|].
    destruct (search_scan (search_final_costs s) costs rest)
      as [[child [suffix values]]|values].
    - now apply search_park_queue.
    - now apply search_offer_queue.
  Qed.

  Lemma search_resume_list_queue : forall DB frames (s : extraction_state V.t DB Q.t),
    search_queue_agrees (search_candidates s) (search_queue s) ->
    search_queue_agrees (search_candidates (search_resume_list frames s))
      (search_queue (search_resume_list frames s)).
  Proof.
    intros DB frames. induction frames as [|frame rest IH]; intros s Hqueue.
    - exact Hqueue.
    - cbn [search_resume_list]. apply IH. now apply search_resume_queue.
  Qed.

  Lemma search_initial_queue : forall DB (db : DB) rows,
    search_queue_agrees (search_candidates (search_initial db rows))
      (search_queue (search_initial db rows)).
  Proof.
    intros DB db rows. unfold search_initial. apply search_resume_list_queue.
    apply search_queue_empty.
  Qed.

  (** A completed scan has found every identifier and reports the complete child-cost list. *)
  Lemma search_scan_ready : forall todo costs acc values,
    search_scan costs acc todo = inr values ->
    (forall i, In (Id i) todo -> exists n, trie_get i costs = Some n) /\
    values = rev acc ++ dag_cost_cells C.val_cost costs todo.
  Proof.
    induction todo as [|[i|v] rest IH]; intros costs acc values Hscan.
    - cbn [search_scan] in Hscan. injection Hscan as <-. split.
      + intros i Hin. contradiction.
      + cbn [dag_cost_cells]. now rewrite rev_append_rev.
    - cbn [search_scan] in Hscan.
      destruct (trie_get i costs) as [n|] eqn:Hget; [|discriminate].
      destruct (IH costs (n :: acc) values Hscan) as [Hknown Hvalues]. split.
      + intros j [Heq|Hin].
        * injection Heq as <-. exists n. exact Hget.
        * now apply Hknown.
      + rewrite Hvalues. cbn [rev dag_cost_cells]. unfold dag_get_cost. rewrite Hget.
        now rewrite <- app_assoc.
    - cbn [search_scan] in Hscan.
      destruct (IH costs (C.val_cost v :: acc) values Hscan) as [Hknown Hvalues]. split.
      + intros i [Heq|Hin]; [discriminate|now apply Hknown].
      + rewrite Hvalues. cbn [rev dag_cost_cells]. now rewrite <- app_assoc.
  Qed.

  (** A suspended scan splits off a known prefix and retains its first unknown identifier. *)
  Lemma search_scan_wait : forall todo costs acc child rest values,
    search_scan costs acc todo = inl (child, (rest, values)) ->
    exists pre tail, todo = pre ++ Id child :: tail /\ rest = Id child :: tail /\
      (forall i, In (Id i) pre -> exists n, trie_get i costs = Some n) /\
      trie_get child costs = None /\
      values = rev (dag_cost_cells C.val_cost costs pre) ++ acc.
  Proof.
    induction todo as [|[i|v] todo IH]; intros costs acc child rest values Hscan.
    - discriminate.
    - cbn [search_scan] in Hscan.
      destruct (trie_get i costs) as [n|] eqn:Hget.
      + destruct (IH costs (n :: acc) child rest values Hscan)
          as [pre [tail [Htodo [Hrest [Hknown [Hmissing Hvalues]]]]]].
        exists (Id i :: pre), tail. split; [now cbn [app]; rewrite Htodo|].
        split; [exact Hrest|]. split.
        * intros j [Heq|Hin].
          -- injection Heq as <-. exists n. exact Hget.
          -- now apply Hknown.
        * split; [exact Hmissing|]. rewrite Hvalues.
          cbn [dag_cost_cells]. unfold dag_get_cost. rewrite Hget. cbn [rev].
          now rewrite <- app_assoc.
      + injection Hscan as <- <- <-. exists [], todo. split; [reflexivity|].
        split; [reflexivity|]. split; [intros j Hin; contradiction|].
        split; [exact Hget|reflexivity].
    - cbn [search_scan] in Hscan.
      destruct (IH costs (C.val_cost v :: acc) child rest values Hscan)
        as [pre [tail [Htodo [Hrest [Hknown [Hmissing Hvalues]]]]]].
      exists (Val v :: pre), tail. split; [now cbn [app]; rewrite Htodo|].
      split; [exact Hrest|]. split.
      + intros i [Heq|Hin]; [discriminate|now apply Hknown].
      + split; [exact Hmissing|]. rewrite Hvalues.
        cbn [dag_cost_cells rev]. now rewrite <- app_assoc.
  Qed.

  (** Extending a final-cost map preserves every previous binding. *)
  Definition search_costs_extend (old new : ptrie N) : Prop :=
    forall i n, trie_get i old = Some n -> trie_get i new = Some n.

  Lemma search_costs_extend_set : forall costs i n,
    trie_get i costs = None -> search_costs_extend costs (PTrieCode.set i n costs).
  Proof.
    intros costs i n Hmissing j m Hget. destruct (Pos.eq_dec j i) as [->|Hneq].
    - congruence.
    - now rewrite PTrie.get_set_other.
  Qed.

  (** Evaluated known keys retain their costs when more classes become final. *)
  Lemma search_cells_extend : forall key old new,
    search_costs_extend old new ->
    (forall i, In (Id i) key -> exists n, trie_get i old = Some n) ->
    dag_cost_cells C.val_cost new key = dag_cost_cells C.val_cost old key.
  Proof.
    induction key as [|[i|v] rest IH]; intros old new Hextend Hknown.
    - reflexivity.
    - destruct (Hknown i (or_introl eq_refl)) as [n Hget].
      pose proof (Hextend i n Hget) as Hnew.
      cbn [dag_cost_cells]. unfold dag_get_cost. rewrite Hget, Hnew. f_equal.
      apply IH; [exact Hextend|]. intros j Hin. apply Hknown. now right.
    - cbn [dag_cost_cells]. f_equal. apply IH; [exact Hextend|].
      intros i Hin. apply Hknown. now right.
  Qed.

  (** A frame's cached costs describe exactly a consumed prefix of its original row. *)
  Definition search_frame_valid (rs : list (search_row V.t)) (costs : ptrie N)
      (frame : extraction_frame V.t) : Prop :=
    In (frame_row frame) rs /\
    exists pre, snd (fst (frame_row frame)) = pre ++ frame_rest frame /\
      Semantics.search_known costs pre /\
      frame_costs frame = rev (dag_cost_cells C.val_cost costs pre).

  Lemma search_frame_new : forall rs costs row, In row rs ->
    search_frame_valid rs costs (search_new_frame row).
  Proof.
    intros rs costs [[f k] i] Hin. split; [exact Hin|].
    exists []. split; [reflexivity|]. split; [|reflexivity].
    intros j Hmember. contradiction.
  Qed.

  Lemma search_known_extend : forall key old new,
    search_costs_extend old new -> Semantics.search_known old key ->
    Semantics.search_known new key.
  Proof.
    intros key old new Hextend Hknown i Hin.
    destruct (Hknown i Hin) as [n Hget]. exists n. now apply Hextend.
  Qed.

  Lemma search_frame_extend : forall rs old new frame,
    search_costs_extend old new -> search_frame_valid rs old frame ->
    search_frame_valid rs new frame.
  Proof.
    intros rs old new frame Hextend [Hrow [pre [Hkey [Hknown Hcosts]]]].
    split; [exact Hrow|]. exists pre. split; [exact Hkey|]. split.
    - eapply search_known_extend; eassumption.
    - rewrite Hcosts. f_equal. symmetry. eapply search_cells_extend; eassumption.
  Qed.

  (** The evaluator distributes over a key split. *)
  Lemma search_cells_app : forall costs left right,
    dag_cost_cells C.val_cost costs (left ++ right) =
      dag_cost_cells C.val_cost costs left ++ dag_cost_cells C.val_cost costs right.
  Proof.
    intros costs left. induction left as [|[i|v] left IH]; intro right;
      cbn [app dag_cost_cells]; now rewrite ?IH.
  Qed.

  Lemma search_known_app : forall costs left right,
    Semantics.search_known costs left -> Semantics.search_known costs right ->
    Semantics.search_known costs (left ++ right).
  Proof.
    intros costs left right Hleft Hright i Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin]; [now apply Hleft|now apply Hright].
  Qed.

  (** A completed valid frame yields exactly the evaluated costs of its full row key. *)
  Lemma search_frame_ready : forall rs costs frame values,
    search_frame_valid rs costs frame ->
    search_scan costs (frame_costs frame) (frame_rest frame) = inr values ->
    Semantics.search_known costs (snd (fst (frame_row frame))) /\
    values = dag_cost_cells C.val_cost costs (snd (fst (frame_row frame))).
  Proof.
    intros rs costs frame values [Hrow [pre [Hkey [Hknown Hcosts]]]] Hscan.
    destruct (search_scan_ready _ _ _ _ Hscan) as [Hrest Hvalues].
    rewrite Hkey. split.
    - now apply search_known_app.
    - rewrite Hvalues, Hcosts, rev_involutive, search_cells_app. reflexivity.
  Qed.

  (** A suspended valid frame remains valid at the precise missing child it reports. *)
  Lemma search_frame_wait : forall rs costs frame child rest values,
    search_frame_valid rs costs frame ->
    search_scan costs (frame_costs frame) (frame_rest frame) =
      inl (child, (rest, values)) ->
    search_frame_valid rs costs (ExtractionFrame (frame_row frame) rest values) /\
    trie_get child costs = None /\ exists tail, rest = Id child :: tail.
  Proof.
    intros rs costs frame child rest values [Hrow [pre [Hkey [Hknown Hcosts]]]] Hscan.
    destruct (search_scan_wait _ _ _ _ _ _ Hscan)
      as [more [tail [Hrest [Hsuffix [Hmore [Hmissing Hvalues]]]]]].
    split.
    - split; [exact Hrow|]. exists (pre ++ more). split.
      + cbn [frame_row frame_rest]. rewrite Hkey, Hrest, Hsuffix. now rewrite app_assoc.
      + split; [now apply search_known_app|]. cbn [frame_costs].
        rewrite Hvalues, Hcosts, search_cells_app, rev_app_distr. reflexivity.
    - split; [exact Hmissing|]. now exists tail.
  Qed.

  (** Every parked frame waits at its first still absent identifier. *)
  Definition search_waiters_valid (rs : list (search_row V.t)) (costs : ptrie N)
      (waiters : ptrie (list (extraction_frame V.t))) : Prop :=
    forall i frames frame, trie_get i waiters = Some frames -> In frame frames ->
      search_frame_valid rs costs frame /\ trie_get i costs = None /\
      exists rest, frame_rest frame = Id i :: rest.

  (** Every live candidate is a ready original row for an unfinalized class. *)
  Definition search_candidates_valid (rs : list (search_row V.t)) (costs : ptrie N)
      (candidates : ptrie (N * extraction_row V.t)) : Prop :=
    forall i n f k, trie_get i candidates = Some (n, (f, k)) ->
      trie_get i costs = None /\ In (f, k, i) rs /\
      Semantics.search_known costs k /\ n = C.fn_cost f (dag_cost_cells C.val_cost costs k).

  (** A processed row has a final output or a ready candidate no dearer than that row. *)
  Definition search_row_covered (costs : ptrie N)
      (candidates : ptrie (N * extraction_row V.t)) (row : search_row V.t) : Prop :=
    (exists n, trie_get (snd row) costs = Some n) \/
    (Semantics.search_known costs (snd (fst row)) /\
      exists n choice, trie_get (snd row) candidates = Some (n, choice) /\
        (n <= C.fn_cost (fst (fst row))
          (dag_cost_cells C.val_cost costs (snd (fst row))))%N).

  (** An unfinished row remains in a waiting list or in the detached active list. *)
  Definition search_row_pending (waiters : ptrie (list (extraction_frame V.t)))
      (active : list (extraction_frame V.t)) (row : search_row V.t) : Prop :=
    (exists i frames frame, trie_get i waiters = Some frames /\
      In frame frames /\ frame_row frame = row) \/
    exists frame, In frame active /\ frame_row frame = row.

  Definition search_tracking (rs : list (search_row V.t)) (costs : ptrie N)
      (candidates : ptrie (N * extraction_row V.t))
      (waiters : ptrie (list (extraction_frame V.t)))
      (active : list (extraction_frame V.t)) : Prop :=
    forall row, In row rs -> search_row_covered costs candidates row \/
      search_row_pending waiters active row.

  (** Search bookkeeping accounts for every source row without counting rows in executable maps. *)
  Definition search_invariant {DB} (rs : list (search_row V.t))
      (s : extraction_state V.t DB Q.t) : Prop :=
    search_candidates_valid rs (search_final_costs s) (search_candidates s) /\
    search_waiters_valid rs (search_final_costs s) (search_waiters s) /\
    search_queue_agrees (search_candidates s) (search_queue s) /\
    search_tracking rs (search_final_costs s) (search_candidates s) (search_waiters s) [].

  (** A ready row cannot still be parked at an absent identifier. *)
  Lemma search_ready_not_waiting : forall rs costs waiters row,
    search_waiters_valid rs costs waiters ->
    Semantics.search_known costs (snd (fst row)) ->
    ~ search_row_pending waiters [] row.
  Proof.
    intros rs costs waiters row Hwaiters Hknown [Hwaiting|Hactive].
    - destruct Hwaiting as [i [frames [frame [Hget [Hin Hrow]]]]].
      destruct (Hwaiters i frames frame Hget Hin)
        as [[Hsource [pre [Hkey [Hprefix Hcosts]]]] [Hmissing [rest Hrest]]].
      rewrite Hrow, Hrest in Hkey.
      destruct (Hknown i ltac:(rewrite Hkey; apply in_or_app; right; now left)) as [n Hn].
      congruence.
    - destruct Hactive as [frame [Hin _]]. contradiction.
  Qed.

  (** Accounted ready rows provide precisely the frontier condition used by Knuth's argument. *)
  Lemma search_invariant_covered : forall DB rs (s : extraction_state V.t DB Q.t),
    search_invariant rs s ->
    Semantics.search_covered rs (search_final_costs s) (Q.prio (search_queue s)).
  Proof.
    intros DB rs s [Hcandidates [Hwaiters [[Hwf [Hprio Hsize]] Htracking]]]
      f k i Hrow Hknown Hmissing.
    destruct (Htracking (f, k, i) Hrow) as [Hcovered|Hpending].
    - destruct Hcovered as [[n Hget]|[_ [n [choice [Hget Hle]]]]].
      + cbn [snd] in Hget. congruence.
      + cbn [fst snd] in Hget, Hle. exists n. split; [|exact Hle].
        rewrite Hprio, Hget. reflexivity.
    - exfalso. exact (search_ready_not_waiting rs (search_final_costs s)
        (search_waiters s) (f, k, i) Hwaiters Hknown Hpending).
  Qed.

  (** A continuing invariant state performs a real pop and finalizes its recorded candidate. *)
  Lemma search_step_cases : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_invariant rs s -> search_step s = inl next ->
    exists i n f k queue,
      Q.pop (search_queue s) = Some (n, i, queue) /\
      trie_get i (search_candidates s) = Some (n, (f, k)) /\
      next = search_finish i n (f, k) queue s.
  Proof.
    intros DB rs s next [Hcandidates [Hwaiters [Hqueue Htracking]]] Hstep.
    destruct (Q.size (search_queue s)) as [|size] eqn:Hsize.
    - unfold search_step in Hstep. rewrite Hsize in Hstep. discriminate.
    - destruct (search_queue_positive _ _ Hqueue ltac:(rewrite Hsize; discriminate))
        as [n [i [queue Hpop]]].
      destruct (search_queue_remove _ _ _ _ _ Hqueue Hpop)
        as [[f k] [Hcandidate Hremaining]].
      destruct (Hcandidates i n f k Hcandidate) as [Hmissing Hrow].
      unfold search_step in Hstep. rewrite Hsize, Hpop, Hcandidate, Hmissing in Hstep.
      injection Hstep as <-. exists i, n, f, k, queue. auto.
  Qed.

  (** The newly finalized row is an original ready row with the least live priority. *)
  Lemma search_step_choice : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_invariant rs s -> search_step s = inl next ->
    exists i n f k,
      trie_get i (search_final_costs s) = None /\ In (f, k, i) rs /\
      Semantics.search_known (search_final_costs s) k /\
      n = C.fn_cost f (dag_cost_cells C.val_cost (search_final_costs s) k) /\
      Q.prio (search_queue s) i = Some n /\
      (forall j m, Q.prio (search_queue s) j = Some m -> (n <= m)%N) /\
      search_final_costs next = PTrieCode.set i n (search_final_costs s) /\
      search_finalised next = (i, (n, (f, k))) :: search_finalised s.
  Proof.
    intros DB rs s next Hinv Hstep.
    destruct (search_step_cases DB rs s next Hinv Hstep)
      as [i [n [f [k [queue [Hpop [Hcandidate ->]]]]]]].
    destruct Hinv as [Hcandidates [Hwaiters [[Hwf [Hprio Hsize]] Htracking]]].
    destruct (Hcandidates i n f k Hcandidate) as [Hmissing [Hrow [Hknown Hcost]]].
    destruct (Q.pop_min (search_queue s) n i queue Hwf Hpop)
      as [Hpriority [Hminimum Hrest]].
    destruct (search_finish_fields DB i n (f, k) queue s)
      as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
    exists i, n, f, k. repeat split; assumption.
  Qed.

  (** Every continuing step retains the immutable source fields. *)
  Lemma search_step_source : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_invariant rs s -> search_step s = inl next ->
    search_database next = search_database s /\
    search_rows next = search_rows s /\ search_row_count next = search_row_count s.
  Proof.
    intros DB rs s next Hinv Hstep.
    destruct (search_step_cases DB rs s next Hinv Hstep)
      as [i [n [f [k [queue [Hpop [Hcandidate ->]]]]]]].
    destruct (search_finish_fields DB i n (f, k) queue s) as [Hdb [Hrows [Hcount Hrest]]].
    repeat split; assumption.
  Qed.

  (** Stopping exposes the finalized table and a zero cached queue size. *)
  Lemma search_step_stopped : forall DB (s : extraction_state V.t DB Q.t) out,
    search_step s = inr out -> out = search_finalised s /\ Q.size (search_queue s) = 0%N.
  Proof.
    intros DB s out Hstep. unfold search_step in Hstep.
    destruct (Q.size (search_queue s)) as [|size] eqn:Hsize.
    - injection Hstep as <-. now split.
    - destruct (Q.pop (search_queue s)) as [[[n i] queue]|]; [|discriminate].
      destruct (trie_get i (search_candidates s)) as [[value row]|];
        destruct (trie_get i (search_final_costs s)); discriminate.
  Qed.

  (** Setting a ready original row preserves validity of every live candidate. *)
  Lemma search_candidates_set : forall rs costs candidates i n f k,
    search_candidates_valid rs costs candidates -> trie_get i costs = None ->
    In (f, k, i) rs -> Semantics.search_known costs k ->
    n = C.fn_cost f (dag_cost_cells C.val_cost costs k) ->
    search_candidates_valid rs costs (PTrieCode.set i (n, (f, k)) candidates).
  Proof.
    intros rs costs candidates i n f k Hvalid Hmissing Hrow Hknown Hcost j m g key Hget.
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget. injection Hget as <- <- <-.
      repeat split; assumption.
    - rewrite PTrie.get_set_other in Hget by exact Hneq. exact (Hvalid j m g key Hget).
  Qed.

  (** Parking a valid frame preserves validity of all old and new waiting entries. *)
  Lemma search_waiters_set : forall rs costs waiters i frame,
    search_waiters_valid rs costs waiters -> search_frame_valid rs costs frame ->
    trie_get i costs = None -> (exists rest, frame_rest frame = Id i :: rest) ->
    search_waiters_valid rs costs
      (PTrieCode.set i (frame :: match trie_get i waiters with
        | Some frames => frames | None => [] end) waiters).
  Proof.
    intros rs costs waiters i frame Hvalid Hframe Hmissing Hhead j frames entry Hget Hin.
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_set_same in Hget. injection Hget as <-.
      destruct Hin as [<-|Hin].
      + split; [exact Hframe|]. split; assumption.
      + destruct (trie_get i waiters) as [old|] eqn:Hold; [|contradiction].
        exact (Hvalid i old entry Hold Hin).
    - rewrite PTrie.get_set_other in Hget by exact Hneq.
      exact (Hvalid j frames entry Hget Hin).
  Qed.

  (** Offering a ready row preserves candidate and waiting-list validity. *)
  Lemma search_offer_valid : forall DB rs i n f k (s : extraction_state V.t DB Q.t),
    search_candidates_valid rs (search_final_costs s) (search_candidates s) ->
    search_waiters_valid rs (search_final_costs s) (search_waiters s) ->
    trie_get i (search_final_costs s) = None -> In (f, k, i) rs ->
    Semantics.search_known (search_final_costs s) k ->
    n = C.fn_cost f (dag_cost_cells C.val_cost (search_final_costs s) k) ->
    search_candidates_valid rs (search_final_costs (search_offer i n (f, k) s))
      (search_candidates (search_offer i n (f, k) s)) /\
    search_waiters_valid rs (search_final_costs (search_offer i n (f, k) s))
      (search_waiters (search_offer i n (f, k) s)).
  Proof.
    intros DB rs i n f k s Hcandidates Hwaiters Hmissing Hrow Hknown Hcost.
    unfold search_offer. destruct (trie_get i (search_candidates s)) as [[old choice]|].
    - destruct (N.ltb n old); split; try assumption.
      now apply search_candidates_set.
    - split; [now apply search_candidates_set|exact Hwaiters].
  Qed.

  (** A resumed valid row retains both class-map invariants. *)
  Lemma search_resume_valid : forall DB rs frame (s : extraction_state V.t DB Q.t),
    search_candidates_valid rs (search_final_costs s) (search_candidates s) ->
    search_waiters_valid rs (search_final_costs s) (search_waiters s) ->
    search_frame_valid rs (search_final_costs s) frame ->
    search_candidates_valid rs (search_final_costs (search_resume frame s))
      (search_candidates (search_resume frame s)) /\
    search_waiters_valid rs (search_final_costs (search_resume frame s))
      (search_waiters (search_resume frame s)).
  Proof.
    intros DB rs [[[f k] i] todo acc] s Hcandidates Hwaiters Hframe.
    unfold search_resume. cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)) as [old|] eqn:Hmissing; [now split|].
    destruct (search_scan (search_final_costs s) acc todo)
      as [[child [rest values]]|values] eqn:Hscan.
    - destruct (search_frame_wait rs (search_final_costs s)
        (ExtractionFrame (f, k, i) todo acc) child rest values Hframe Hscan)
        as [Hnew [Hchild Hhead]].
      split; [exact Hcandidates|]. apply search_waiters_set; assumption.
    - destruct (search_frame_ready rs (search_final_costs s)
        (ExtractionFrame (f, k, i) todo acc) values Hframe Hscan) as [Hknown Hvalues].
      cbn [frame_row fst snd] in Hknown, Hvalues.
      apply search_offer_valid; try assumption.
      + exact (proj1 Hframe).
      + now rewrite Hvalues.
  Qed.

  (** A new offer can only decrease a previously recorded candidate cost. *)
  Lemma search_offer_decreases : forall DB i n row (s : extraction_state V.t DB Q.t) j m old,
    trie_get j (search_candidates s) = Some (m, old) ->
    exists p choice, trie_get j (search_candidates (search_offer i n row s)) =
      Some (p, choice) /\ (p <= m)%N.
  Proof.
    intros DB i n row s j m old Hget. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[prior choice]|] eqn:Hi.
    - destruct (N.ltb n prior) eqn:Hbetter.
      + cbn [search_restate search_candidates]. destruct (Pos.eq_dec j i) as [->|Hneq].
        * rewrite Hi in Hget. injection Hget as <- <-. exists n, row. split.
          -- apply PTrie.get_set_same.
          -- apply N.ltb_lt in Hbetter. lia.
        * exists m, old. split; [now rewrite PTrie.get_set_other|apply N.le_refl].
      + exists m, old. split; [exact Hget|apply N.le_refl].
    - cbn [search_restate search_candidates].
      destruct (Pos.eq_dec j i) as [->|Hneq]; [congruence|].
      exists m, old. split; [now rewrite PTrie.get_set_other|apply N.le_refl].
  Qed.

  (** Every offer leaves a candidate whose cost is at most the supplied ready cost. *)
  Lemma search_offer_supplied : forall DB i n row (s : extraction_state V.t DB Q.t),
    exists p choice, trie_get i (search_candidates (search_offer i n row s)) =
      Some (p, choice) /\ (p <= n)%N.
  Proof.
    intros DB i n row s. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[prior choice]|] eqn:Hi.
    - destruct (N.ltb n prior) eqn:Hbetter.
      + exists n, row. split; [apply PTrie.get_set_same|apply N.le_refl].
      + exists prior, choice. split; [exact Hi|]. now apply N.ltb_ge in Hbetter.
    - exists n, row. split; [apply PTrie.get_set_same|apply N.le_refl].
  Qed.

  (** Offering a new row preserves coverage already supplied by other ready rows. *)
  Lemma search_offer_covered : forall DB i n choice (s : extraction_state V.t DB Q.t) row,
    search_row_covered (search_final_costs s) (search_candidates s) row ->
    search_row_covered (search_final_costs (search_offer i n choice s))
      (search_candidates (search_offer i n choice s)) row.
  Proof.
    intros DB i n choice s row Hcovered.
    destruct (search_offer_stable DB i n choice s) as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
    rewrite Hcosts. destruct Hcovered as [Hfinal|[Hknown [p [old [Hget Hbound]]]]].
    - now left.
    - right. split; [exact Hknown|].
      destruct (search_offer_decreases DB i n choice s (snd row) p old Hget)
        as [m [new [Hnew Hle]]].
      exists m, new. split; [exact Hnew|]. eapply N.le_trans; eassumption.
  Qed.

  Lemma search_offer_waiters : forall DB i n choice (s : extraction_state V.t DB Q.t),
    search_waiters (search_offer i n choice s) = search_waiters s.
  Proof.
    intros DB i n choice s. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old row]|];
      [destruct (N.ltb n old)|]; reflexivity.
  Qed.

  (** The row just offered is covered by the resulting candidate map. *)
  Lemma search_offer_covers : forall DB i n f k (s : extraction_state V.t DB Q.t),
    Semantics.search_known (search_final_costs s) k ->
    n = C.fn_cost f (dag_cost_cells C.val_cost (search_final_costs s) k) ->
    search_row_covered (search_final_costs (search_offer i n (f, k) s))
      (search_candidates (search_offer i n (f, k) s)) (f, k, i).
  Proof.
    intros DB i n f k s Hknown Hcost.
    destruct (search_offer_stable DB i n (f, k) s) as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
    rewrite Hcosts. right. split; [exact Hknown|].
    destruct (search_offer_supplied DB i n (f, k) s) as [p [choice [Hget Hle]]].
    exists p, choice. split; [exact Hget|]. cbn [fst snd]. now rewrite <- Hcost.
  Qed.

  (** A pending source in a nonempty active list is its head or remains pending in the tail. *)
  Lemma search_pending_cons : forall waiters frame active row,
    search_row_pending waiters (frame :: active) row ->
    frame_row frame = row \/ search_row_pending waiters active row.
  Proof.
    intros waiters frame active row [Hwaiting|[entry [Hin Hrow]]].
    - right. now left.
    - destruct Hin as [<-|Hin].
      + now left.
      + right. right. exists entry. now split.
  Qed.

  (** Inserting a waiting frame preserves all older pending row sources. *)
  Lemma search_pending_set : forall waiters i frame active row,
    search_row_pending waiters active row ->
    search_row_pending (PTrieCode.set i (frame :: match trie_get i waiters with
      | Some frames => frames | None => [] end) waiters) active row.
  Proof.
    intros waiters i frame active row [Hwaiting|Hactive]; [left|now right].
    destruct Hwaiting as [j [frames [entry [Hget [Hin Hrow]]]]].
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - exists i, (frame :: frames), entry. split.
      + rewrite PTrie.get_set_same, Hget. reflexivity.
      + split; [now right|exact Hrow].
    - exists j, frames, entry. split.
      + now rewrite PTrie.get_set_other.
      + now split.
  Qed.

  (** A newly parked frame accounts for its own source row. *)
  Lemma search_pending_inserted : forall waiters i frame active,
    search_row_pending (PTrieCode.set i (frame :: match trie_get i waiters with
      | Some frames => frames | None => [] end) waiters) active (frame_row frame).
  Proof.
    intros waiters i frame active. left.
    exists i, (frame :: match trie_get i waiters with Some frames => frames | None => [] end),
      frame.
    split; [apply PTrie.get_set_same|]. split; [now left|reflexivity].
  Qed.

  (** Consuming one active frame keeps all sources accounted for when old coverage persists. *)
  Lemma search_tracking_consume : forall rs costs candidates waiters frame active
      new_costs new_candidates new_waiters,
    search_tracking rs costs candidates waiters (frame :: active) ->
    (forall row, search_row_covered costs candidates row ->
      search_row_covered new_costs new_candidates row) ->
    (forall row, search_row_pending waiters active row ->
      search_row_pending new_waiters active row) ->
    (search_row_covered new_costs new_candidates (frame_row frame) \/
      search_row_pending new_waiters active (frame_row frame)) ->
    search_tracking rs new_costs new_candidates new_waiters active.
  Proof.
    intros rs costs candidates waiters frame active new_costs new_candidates new_waiters
      Htracking Hcovered Hpending Hframe row Hin.
    destruct (Htracking row Hin) as [Hcover|Hwait].
    - left. now apply Hcovered.
    - destruct (search_pending_cons waiters frame active row Hwait) as [<-|Htail].
      + exact Hframe.
      + right. now apply Hpending.
  Qed.

  (** Resuming the head of an active list preserves the source accounting of its tail. *)
  Lemma search_resume_tracking : forall DB rs frame active (s : extraction_state V.t DB Q.t),
    search_frame_valid rs (search_final_costs s) frame ->
    search_tracking rs (search_final_costs s) (search_candidates s) (search_waiters s)
      (frame :: active) ->
    search_tracking rs (search_final_costs (search_resume frame s))
      (search_candidates (search_resume frame s)) (search_waiters (search_resume frame s)) active.
  Proof.
    intros DB rs [[[f k] i] todo acc] active s Hframe Htracking.
    unfold search_resume. cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)) as [n|] eqn:Hmissing.
    - eapply search_tracking_consume; [exact Htracking| | |].
      + intros row Hcovered. exact Hcovered.
      + intros row Hpending. exact Hpending.
      + left. left. exists n. exact Hmissing.
    - destruct (search_scan (search_final_costs s) acc todo)
        as [[child [rest values]]|values] eqn:Hscan.
      + eapply search_tracking_consume; [exact Htracking| | |].
        * intros row Hcovered. exact Hcovered.
        * intros row Hpending. now apply search_pending_set.
        * right. exact (search_pending_inserted (search_waiters s) child
            (ExtractionFrame (f, k, i) rest values) active).
      + destruct (search_frame_ready rs (search_final_costs s)
          (ExtractionFrame (f, k, i) todo acc) values Hframe Hscan) as [Hknown Hvalues].
        cbn [frame_row fst snd] in Hknown, Hvalues.
        eapply search_tracking_consume; [exact Htracking| | |].
        * intros row Hcovered. now apply search_offer_covered.
        * intros row Hpending. now rewrite search_offer_waiters.
        * left. apply search_offer_covers; [exact Hknown|]. now rewrite Hvalues.
  Qed.

  (** Registering a whole active list restores the state invariant once the list is empty. *)
  Lemma search_resume_list_registered : forall DB rs frames (s : extraction_state V.t DB Q.t),
    search_candidates_valid rs (search_final_costs s) (search_candidates s) ->
    search_waiters_valid rs (search_final_costs s) (search_waiters s) ->
    search_queue_agrees (search_candidates s) (search_queue s) ->
    Forall (search_frame_valid rs (search_final_costs s)) frames ->
    search_tracking rs (search_final_costs s) (search_candidates s) (search_waiters s) frames ->
    search_invariant rs (search_resume_list frames s).
  Proof.
    intros DB rs frames. induction frames as [|frame frames IH];
      intros s Hcandidates Hwaiters Hqueue Hframes Htracking.
    - split; [exact Hcandidates|]. split; [exact Hwaiters|]. now split.
    - inversion Hframes as [|entry rest Hframe Hrest]; subst entry rest.
      destruct (search_resume_valid DB rs frame s Hcandidates Hwaiters Hframe)
        as [Hcandidates' Hwaiters'].
      cbn [search_resume_list]. apply IH; try assumption.
      + now apply search_resume_queue.
      + destruct (search_resume_stable DB frame s)
          as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
        now rewrite Hcosts.
      + now apply search_resume_tracking.
  Qed.

  (** Every source row starts as an unconsumed active frame. *)
  Lemma search_initial_invariant : forall DB (db : DB) rs,
    search_invariant rs (search_initial db rs).
  Proof.
    intros DB db rs. unfold search_initial. apply search_resume_list_registered.
    - intros i n f k Hget. rewrite PTrie.get_empty in Hget. discriminate.
    - intros i frames frame Hget Hin. rewrite PTrie.get_empty in Hget. discriminate.
    - apply search_queue_empty.
    - apply Forall_forall. intros frame Hin. apply in_map_iff in Hin.
      destruct Hin as [row [<- Hrow]]. now apply search_frame_new.
    - intros row Hin. right. right. exists (search_new_frame row).
      split; [now apply in_map|reflexivity].
  Qed.

  (** Finalizing a fresh class preserves all other candidate rows and their costs. *)
  Lemma search_candidates_remove : forall rs costs candidates i n,
    search_candidates_valid rs costs candidates -> trie_get i costs = None ->
    search_candidates_valid rs (PTrieCode.set i n costs) (PTrieCode.remove i candidates).
  Proof.
    intros rs costs candidates i n Hvalid Hmissing j m f k Hget.
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_remove_same in Hget. discriminate.
    - rewrite PTrie.get_remove_other in Hget by exact Hneq.
      destruct (Hvalid j m f k Hget) as [Habsent [Hrow [Hknown Hcost]]].
      pose proof (search_costs_extend_set costs i n Hmissing) as Hextend.
      split; [now rewrite PTrie.get_set_other|]. split; [exact Hrow|]. split.
      + eapply search_known_extend; eassumption.
      + rewrite (search_cells_extend k costs (PTrieCode.set i n costs) Hextend Hknown).
        exact Hcost.
  Qed.

  (** Undetached frames still wait at absent classes after one fresh finalization. *)
  Lemma search_waiters_remove : forall rs costs waiters i n,
    search_waiters_valid rs costs waiters -> trie_get i costs = None ->
    search_waiters_valid rs (PTrieCode.set i n costs) (PTrieCode.remove i waiters).
  Proof.
    intros rs costs waiters i n Hvalid Hmissing j frames frame Hget Hin.
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - rewrite PTrie.get_remove_same in Hget. discriminate.
    - rewrite PTrie.get_remove_other in Hget by exact Hneq.
      destruct (Hvalid j frames frame Hget Hin) as [Hframe [Habsent Hhead]].
      split.
      + eapply search_frame_extend; [now apply search_costs_extend_set|exact Hframe].
      + split; [now rewrite PTrie.get_set_other|exact Hhead].
  Qed.

  (** The detached waiting list contains valid frames in the extended final-cost map. *)
  Lemma search_detached_valid : forall rs costs waiters i n,
    search_waiters_valid rs costs waiters -> trie_get i costs = None ->
    Forall (search_frame_valid rs (PTrieCode.set i n costs))
      (match trie_get i waiters with Some frames => frames | None => [] end).
  Proof.
    intros rs costs waiters i n Hvalid Hmissing.
    destruct (trie_get i waiters) as [frames|] eqn:Hget; [|constructor].
    apply Forall_forall. intros frame Hin.
    destruct (Hvalid i frames frame Hget Hin) as [Hframe Hrest].
    eapply search_frame_extend; [now apply search_costs_extend_set|exact Hframe].
  Qed.

  (** Old coverage survives finalization because ready child costs are already fixed. *)
  Lemma search_covered_finish : forall costs candidates i n row,
    trie_get i costs = None -> search_row_covered costs candidates row ->
    search_row_covered (PTrieCode.set i n costs) (PTrieCode.remove i candidates) row.
  Proof.
    intros costs candidates i n row Hmissing Hcovered.
    destruct (Pos.eq_dec (snd row) i) as [Heq|Hneq].
    - left. exists n. rewrite Heq. apply PTrie.get_set_same.
    - pose proof (search_costs_extend_set costs i n Hmissing) as Hextend.
      destruct Hcovered as [[m Hget]|[Hknown [m [choice [Hget Hbound]]]]].
      + left. exists m. now apply Hextend.
      + right. split.
        * eapply search_known_extend; eassumption.
        * exists m, choice. split; [now rewrite PTrie.get_remove_other|].
          rewrite (search_cells_extend (snd (fst row)) costs (PTrieCode.set i n costs)
            Hextend Hknown). exact Hbound.
  Qed.

  (** Detaching one waiting list moves its sources to the active list and keeps all others. *)
  Lemma search_pending_detach : forall waiters i row,
    search_row_pending waiters [] row ->
    search_row_pending (PTrieCode.remove i waiters)
      (match trie_get i waiters with Some frames => frames | None => [] end) row.
  Proof.
    intros waiters i row [Hwaiting|[frame [Hin Hrow]]]; [|contradiction].
    destruct Hwaiting as [j [frames [frame [Hget [Hin Hrow]]]]].
    destruct (Pos.eq_dec j i) as [->|Hneq].
    - right. rewrite Hget. exists frame. now split.
    - left. exists j, frames, frame. split; [now rewrite PTrie.get_remove_other|].
      now split.
  Qed.

  (** The finalization update accounts for every source before resuming the detached list. *)
  Lemma search_tracking_finish : forall rs costs candidates waiters i n,
    trie_get i costs = None -> search_tracking rs costs candidates waiters [] ->
    search_tracking rs (PTrieCode.set i n costs) (PTrieCode.remove i candidates)
      (PTrieCode.remove i waiters)
      (match trie_get i waiters with Some frames => frames | None => [] end).
  Proof.
    intros rs costs candidates waiters i n Hmissing Htracking row Hin.
    destruct (Htracking row Hin) as [Hcovered|Hpending].
    - left. now apply search_covered_finish.
    - right. now apply search_pending_detach.
  Qed.

  (** Finalizing a live heap candidate and resuming its waiting list preserves bookkeeping. *)
  Lemma search_finish_invariant : forall DB rs (s : extraction_state V.t DB Q.t)
      i n f k queue,
    search_invariant rs s -> Q.pop (search_queue s) = Some (n, i, queue) ->
    trie_get i (search_candidates s) = Some (n, (f, k)) ->
    search_invariant rs (search_finish i n (f, k) queue s).
  Proof.
    intros DB rs s i n f k queue [Hcandidates [Hwaiters [Hqueue Htracking]]]
      Hpop Hcandidate.
    destruct (Hcandidates i n f k Hcandidate) as [Hmissing Hrow].
    destruct (search_queue_remove _ _ _ _ _ Hqueue Hpop)
      as [choice [Hchoice Hnextqueue]].
    unfold search_finish. apply search_resume_list_registered.
    - now apply search_candidates_remove.
    - now apply search_waiters_remove.
    - exact Hnextqueue.
    - now apply search_detached_valid.
    - now apply search_tracking_finish.
  Qed.

  (** Every continuing search step preserves the invariant on the same finite source. *)
  Lemma search_step_invariant : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_invariant rs s -> search_step s = inl next -> search_invariant rs next.
  Proof.
    intros DB rs s next Hinv Hstep.
    destruct (search_step_cases DB rs s next Hinv Hstep)
      as [i [n [f [k [queue [Hpop [Hcandidate ->]]]]]]].
    eapply search_finish_invariant; eassumption.
  Qed.

End SearchFacts.

(** A ghost sum charges each finite-map value independently of its lookup key. *)
Definition search_entries_weight {A} (weight : A -> nat) (entries : list (positive * A)) :=
  fold_right (fun entry total => weight (snd entry) + total) 0 entries.

Definition search_trie_weight {A} (weight : A -> nat) (m : ptrie A) :=
  search_entries_weight weight (PTrieCode.elements m).

Lemma search_entries_weight_app : forall A weight (left right : list (positive * A)),
  search_entries_weight weight (left ++ right) =
    search_entries_weight weight left + search_entries_weight weight right.
Proof.
  intros A weight left right. unfold search_entries_weight.
  induction left as [|[i a] left IH].
  - reflexivity.
  - cbn [fold_right app snd]. rewrite IH. lia.
Qed.

Lemma search_entries_weight_lift : forall A weight (bit : positive -> positive)
    (entries : list (positive * A)),
  search_entries_weight weight (map (fun entry => (bit (fst entry), snd entry)) entries) =
    search_entries_weight weight entries.
Proof.
  intros A weight bit entries. unfold search_entries_weight.
  induction entries as [|[i a] entries IH].
  - reflexivity.
  - cbn [fold_right map fst snd]. now rewrite IH.
Qed.

(** A trie node carries exactly the sum of its two subtries and optional root value. *)
Lemma search_trie_weight_node : forall A weight (left right : ptrie A) value,
  search_trie_weight weight (PTrieCode.node left value right) =
    search_trie_weight weight left +
    (match value with Some a => weight a | None => 0 end) +
    search_trie_weight weight right.
Proof.
  intros A weight left right value. unfold search_trie_weight.
  rewrite PTrie.elements_node, !search_entries_weight_app, !search_entries_weight_lift.
  destruct value; cbn [search_entries_weight fold_right snd]; lia.
Qed.

(** Replacing a binding exchanges exactly the old and new value charges. *)
Lemma search_trie_weight_replace : forall A weight p value (m : ptrie A),
  search_trie_weight weight (PTrieCode.replace p value m) +
    (match PTrieCode.get p m with Some a => weight a | None => 0 end) =
  search_trie_weight weight m + (match value with Some a => weight a | None => 0 end).
Proof.
  intros A weight p. induction p; intros value m.
  all: assert (Hweight : search_trie_weight weight m =
    search_trie_weight weight (PTrieCode.left m) +
    (match PTrieCode.value m with Some a => weight a | None => 0 end) +
    search_trie_weight weight (PTrieCode.right m)).
  all: try (rewrite <- (PTrieT.F1_node A m) at 1; apply search_trie_weight_node).
  all: cbn [PTrieCode.replace];
    rewrite search_trie_weight_node, Hweight, PTrie.get_equation.
  - specialize (IHp value (PTrieCode.right m)). lia.
  - specialize (IHp value (PTrieCode.left m)). lia.
  - lia.
Qed.

Lemma search_trie_weight_remove : forall A weight p (m : ptrie A),
  search_trie_weight weight (PTrieCode.remove p m) +
    (match trie_get p m with Some a => weight a | None => 0 end) =
  search_trie_weight weight m.
Proof.
  intros A weight p m. pose proof (search_trie_weight_replace A weight p None m) as Hweight.
  unfold PTrieCode.remove. cbn beta iota zeta in Hweight.
  unfold PTrieCode.get in Hweight. lia.
Qed.

Module SearchResources (V : VALUE) (C : COST V) (Q : PQ).
  Module Facts := SearchFacts V C Q.
  Import Facts.

  (** Each parked occurrence and each pending heap entry owns one source-row token. *)
  Definition search_waiter_count (waiters : ptrie (list (extraction_frame V.t))) :=
    search_trie_weight (@length (extraction_frame V.t)) waiters.

  Definition search_load {DB} (s : extraction_state V.t DB Q.t) :=
    search_waiter_count (search_waiters s) + Q.pending (search_queue s).

  Lemma search_park_load : forall DB i frame (s : extraction_state V.t DB Q.t),
    search_load (search_park i frame s) = S (search_load s).
  Proof.
    intros DB i frame s. unfold search_load, search_park, search_waiter_count.
    cbn [search_restate search_waiters search_queue].
    pose proof (search_trie_weight_replace _ (@length (extraction_frame V.t)) i
      (Some (frame :: match trie_get i (search_waiters s) with
        | Some frames => frames | None => [] end)) (search_waiters s)) as Hweight.
    unfold PTrieCode.set. unfold PTrieCode.get in Hweight.
    destruct (trie_get i (search_waiters s)); cbn [length] in Hweight; lia.
  Qed.

  (** A candidate offer creates at most one pending heap entry and no parked frame. *)
  Lemma search_offer_load : forall DB i n row (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> search_load (search_offer i n row s) <= S (search_load s).
  Proof.
    intros DB i n row s Hwf. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|];
      [destruct (N.ltb n old)|]; unfold search_load;
      cbn [search_restate search_waiters search_queue];
      try pose proof (Q.pending_push n i (search_queue s) Hwf); lia.
  Qed.

  Lemma search_offer_wf : forall DB i n row (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.wf (search_queue (search_offer i n row s)).
  Proof.
    intros DB i n row s Hwf. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|];
      [destruct (N.ltb n old)|]; cbn [search_restate search_queue];
      try apply Q.wf_push; exact Hwf.
  Qed.

  Lemma search_resume_wf : forall DB frame (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.wf (search_queue (search_resume frame s)).
  Proof.
    intros DB [[[f k] i] todo acc] s Hwf. unfold search_resume.
    cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)); [exact Hwf|].
    destruct (search_scan (search_final_costs s) acc todo) as [[child [rest costs]]|costs].
    - exact Hwf.
    - now apply search_offer_wf.
  Qed.

  (** Registering one active frame consumes at most its one source-row token. *)
  Lemma search_resume_load : forall DB frame (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> search_load (search_resume frame s) <= S (search_load s).
  Proof.
    intros DB [[[f k] i] todo acc] s Hwf. unfold search_resume.
    cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)); [lia|].
    destruct (search_scan (search_final_costs s) acc todo) as [[child [rest costs]]|costs].
    - rewrite search_park_load. lia.
    - now apply search_offer_load.
  Qed.

  (** Registering a list preserves the total of active and stored source-row tokens. *)
  Lemma search_resume_list_load : forall DB frames (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) ->
    search_load (search_resume_list frames s) <= length frames + search_load s.
  Proof.
    intros DB frames. induction frames as [|frame frames IH]; intros s Hwf.
    - cbn [search_resume_list length]. lia.
    - pose proof (search_resume_load DB frame s Hwf) as Hhead.
      pose proof (search_resume_wf DB frame s Hwf) as Hnext.
      specialize (IH (search_resume frame s) Hnext).
      cbn [search_resume_list length]. lia.
  Qed.

  Lemma search_initial_load : forall DB (db : DB) rs,
    search_load (search_initial db rs) <= length rs.
  Proof.
    intros DB db rs. unfold search_initial.
    pose proof (search_resume_list_load DB (map search_new_frame rs)
      (search_start db rs) Q.wf_empty) as Hload.
    rewrite length_map in Hload.
    assert (Hstart : search_load (search_start db rs) = 0).
    { unfold search_load, search_waiter_count, search_trie_weight, search_entries_weight,
        search_start.
      cbn [search_waiters search_queue PTrieCode.elements PTrieCode.fold PTrieCode.fold_path
        rev_append fold_right].
      now rewrite Q.pending_empty. }
    rewrite Hstart in Hload. lia.
  Qed.

  (** A successful pop releases one token before the detached frames are registered again. *)
  Lemma search_finish_load : forall DB i n row queue (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.pop (search_queue s) = Some (n, i, queue) ->
    search_load (search_finish i n row queue s) < search_load s.
  Proof.
    intros DB i n row queue s Hwf Hpop.
    pose proof (Q.wf_pop (search_queue s) n i queue Hwf Hpop) as Hnext.
    pose proof (Q.pending_pop (search_queue s) n i queue Hwf Hpop) as Hpending.
    pose proof (search_trie_weight_remove _ (@length (extraction_frame V.t)) i
      (search_waiters s)) as Hweight.
    unfold search_finish.
    pose proof (search_resume_list_load DB
      (match trie_get i (search_waiters s) with Some frames => frames | None => [] end)
      (search_restate s (PTrieCode.set i n (search_final_costs s))
        (PTrieCode.remove i (search_candidates s)) (PTrieCode.remove i (search_waiters s))
        queue ((i, (n, row)) :: search_finalised s)) Hnext) as Hload.
    unfold search_load, search_waiter_count in Hload |- *.
    cbn [search_restate search_waiters search_queue] in Hload.
    destruct (trie_get i (search_waiters s)); cbn [length] in Hload, Hweight; lia.
  Qed.

  Lemma search_step_load : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_invariant rs s -> search_step s = inl next -> search_load next < search_load s.
  Proof.
    intros DB rs s next Hinv Hstep.
    destruct (search_step_cases DB rs s next Hinv Hstep)
      as [i [n [f [k [queue [Hpop [Hcandidate ->]]]]]]].
    destruct Hinv as [Hcandidates [Hwaiters [[Hwf Hqueue] Htracking]]].
    now apply search_finish_load.
  Qed.
  (** Every ready original row fits one fixed heap entry-width envelope. *)
  Definition search_rows_width (rs : list (search_row V.t)) (costs : ptrie N) (w : nat) :=
    forall f k i, In (f, k, i) rs -> Semantics.search_known costs k ->
      Pos.size_nat i + N.size_nat (C.fn_cost f (dag_cost_cells C.val_cost costs k)) <= w.

  Lemma search_offer_fits : forall DB w i n row (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    Pos.size_nat i + N.size_nat n <= w ->
    Q.fits w (search_queue (search_offer i n row s)).
  Proof.
    intros DB w i n row s Hwf Hfits Hwidth. unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|];
      [destruct (N.ltb n old)|]; cbn [search_restate search_queue];
      try apply Q.fits_push; assumption.
  Qed.

  (** Resumption only enqueues the exact cost of a ready original row. *)
  Lemma search_resume_fits : forall DB rs w frame (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    search_frame_valid rs (search_final_costs s) frame ->
    search_rows_width rs (search_final_costs s) w ->
    Q.fits w (search_queue (search_resume frame s)).
  Proof.
    intros DB rs w [[[f k] i] todo acc] s Hwf Hfits Hframe Hwidth.
    unfold search_resume. cbn [frame_row frame_rest frame_costs].
    destruct (trie_get i (search_final_costs s)); [exact Hfits|].
    destruct (search_scan (search_final_costs s) acc todo)
      as [[child [rest values]]|values] eqn:Hscan.
    - exact Hfits.
    - apply search_offer_fits; try assumption.
      destruct (search_frame_ready rs (search_final_costs s)
        (ExtractionFrame (f, k, i) todo acc) values Hframe Hscan) as [Hknown Hvalues].
      cbn [frame_row fst snd] in Hknown, Hvalues.
      rewrite Hvalues. apply Hwidth; [exact (proj1 Hframe)|exact Hknown].
  Qed.

  Lemma search_resume_list_fits : forall DB rs w frames (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    Forall (search_frame_valid rs (search_final_costs s)) frames ->
    search_rows_width rs (search_final_costs s) w ->
    Q.fits w (search_queue (search_resume_list frames s)).
  Proof.
    intros DB rs w frames. induction frames as [|frame frames IH];
      intros s Hwf Hfits Hframes Hwidth.
    - exact Hfits.
    - inversion Hframes as [|entry rest Hframe Hrest]; subst entry rest.
      destruct (search_resume_stable DB frame s)
        as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
      cbn [search_resume_list]. apply IH.
      + now apply search_resume_wf.
      + eapply search_resume_fits; eassumption.
      + now rewrite Hcosts.
      + now rewrite Hcosts.
  Qed.

  Lemma search_initial_fits : forall DB (db : DB) rs w,
    search_rows_width rs Empty w -> Q.fits w (search_queue (search_initial db rs)).
  Proof.
    intros DB db rs w Hwidth. unfold search_initial.
    eapply (search_resume_list_fits DB rs w).
    - exact Q.wf_empty.
    - apply Q.fits_empty.
    - apply Forall_forall. intros frame Hin. apply in_map_iff in Hin.
      destruct Hin as [row [<- Hrow]]. now apply search_frame_new.
    - exact Hwidth.
  Qed.

  (** Finalization preserves queued widths when every newly ready source row fits. *)
  Lemma search_finish_fits : forall DB rs w i n f k queue
      (s : extraction_state V.t DB Q.t),
    search_invariant rs s -> Q.fits w (search_queue s) ->
    Q.pop (search_queue s) = Some (n, i, queue) ->
    trie_get i (search_candidates s) = Some (n, (f, k)) ->
    search_rows_width rs (PTrieCode.set i n (search_final_costs s)) w ->
    Q.fits w (search_queue (search_finish i n (f, k) queue s)).
  Proof.
    intros DB rs w i n f k queue s [Hcandidates [Hwaiters [[Hwf Hqueue] Htracking]]]
      Hfits Hpop Hcandidate Hwidth.
    destruct (Hcandidates i n f k Hcandidate) as [Hmissing Hrest].
    unfold search_finish. eapply (search_resume_list_fits DB rs w).
    - eapply Q.wf_pop; eassumption.
    - eapply Q.fits_pop; eassumption.
    - now apply search_detached_valid.
    - exact Hwidth.
  Qed.


  (** The load bound follows the same continuing-step closure as the search invariant. *)
  Lemma search_load_preserved : forall DB rs (s last : extraction_state V.t DB Q.t),
    clos_refl_trans (extraction_state V.t DB Q.t)
      (fun before after => search_step before = inl after) s last ->
    search_invariant rs s ->
    search_invariant rs last /\ search_load last <= search_load s.
  Proof.
    intros DB rs s last Hreach.
    induction Hreach as [before after Hstep|s|before middle after Hfirst IHfirst Hlast IHlast];
      intro Hinv.
    - split.
      + eapply search_step_invariant; eassumption.
      + pose proof (search_step_load DB rs before after Hinv Hstep). lia.
    - split; [exact Hinv|lia].
    - destruct (IHfirst Hinv) as [Hmiddle Hfirst_load].
      destruct (IHlast Hmiddle) as [Hlast_inv Hlast_load]. split; [exact Hlast_inv|lia].
  Qed.

  (** Every reachable state keeps the pending heap count within the finite source count. *)
  Lemma search_reachable_pending : forall DB (db : DB) rs (s : extraction_state V.t DB Q.t),
    clos_refl_trans (extraction_state V.t DB Q.t)
      (fun before after => search_step before = inl after) (search_initial db rs) s ->
    Q.pending (search_queue s) <= length rs.
  Proof.
    intros DB db rs s Hreach.
    destruct (search_load_preserved DB rs _ _ Hreach (search_initial_invariant DB db rs))
      as [Hinv Hload].
    pose proof (search_initial_load DB db rs) as Hinitial.
    assert (Hcap : search_load s <= length rs) by lia.
    unfold search_load in Hcap. lia.
  Qed.
End SearchResources.

(** Local search clocks and resource credits use only the public timed dependencies. *)
Module SearchResourceT (V : VALUE_T) (C : COST_T V) (Q : PQ_T).
  Include SearchCode V C Q.
  TimeFun search_scan.
  TimeFun search_park.
  TimeFun search_offer.
  TimeFun search_resume.
  TimeFun search_resume_list.
  TimeFun search_start.
  TimeFun search_initial.
  TimeFun search_finish.
  TimeFun search_step.
  TimeFun best_rows.
  Module Facts := SearchFacts V C Q.
  Module Resources := SearchResources V C Q.

  (** A scan budget covers one cell observation and the recursive-call step. *)
  Definition search_cell_bound (costs : ptrie N) (budget : N) (todo : list (cell V.t)) :=
    forall item, In item todo ->
      (match item with
       | Id i => 1 + T_trie_get i costs
       | Val v => 1 + C.T_val_cost v
       end <= budget)%N.

  Lemma search_cell_bound_tail : forall costs budget item todo,
    search_cell_bound costs budget (item :: todo) -> search_cell_bound costs budget todo.
  Proof.
    intros costs budget item todo Hbound other Hin. apply Hbound. now right.
  Qed.

  (** A suspended scan charges only consumed cells and one unsuccessful lookup. *)
  Lemma T_search_scan_wait : forall todo costs acc child rest values budget,
    search_cell_bound costs budget todo ->
    search_scan costs acc todo = inl (child, (rest, values)) ->
    (T_search_scan costs acc todo + budget * N.of_nat (length rest) <=
      budget * N.of_nat (length todo + 1))%N.
  Proof.
    induction todo as [|[i|v] todo IH]; intros costs acc child rest values budget Hbound Hscan.
    - discriminate.
    - pose proof (Hbound (Id i) (or_introl eq_refl)) as Hhead.
      pose proof (search_cell_bound_tail _ _ _ _ Hbound) as Htail.
      cbn [search_scan] in Hscan.
      destruct (trie_get i costs) as [n|] eqn:Hget.
      + specialize (IH costs (n :: acc) child rest values budget Htail Hscan).
        time_unfold @T_search_scan. time_simpl. time_cbn. rewrite Hget.
        cbn [length] in *. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
      + injection Hscan as <- <- <-.
        time_unfold @T_search_scan. time_simpl. time_cbn. rewrite Hget.
        cbn [length] in *. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
    - pose proof (Hbound (Val v) (or_introl eq_refl)) as Hhead.
      pose proof (search_cell_bound_tail _ _ _ _ Hbound) as Htail.
      cbn [search_scan] in Hscan.
      specialize (IH costs (C.val_cost v :: acc) child rest values budget Htail Hscan).
      time_unfold @T_search_scan. time_simpl. time_cbn.
      cbn [length] in *. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** A completed scan reverses its accumulated full key exactly once. *)
  Lemma T_search_scan_ready : forall todo costs acc values budget,
    search_cell_bound costs budget todo -> search_scan costs acc todo = inr values ->
    (T_search_scan costs acc todo <= budget * N.of_nat (length todo) +
      N.of_nat (length acc + length todo) + 2)%N.
  Proof.
    induction todo as [|[i|v] todo IH]; intros costs acc values budget Hbound Hscan.
    - pose proof (Argent.Std.List.T_rev_append_le acc ([] : list N)) as Hreverse.
      time_unfold @T_search_scan. time_simpl. time_cbn.
      cbn [length]. rewrite Nat.add_0_r. nia.
    - pose proof (Hbound (Id i) (or_introl eq_refl)) as Hhead.
      pose proof (search_cell_bound_tail _ _ _ _ Hbound) as Htail.
      cbn [search_scan] in Hscan.
      destruct (trie_get i costs) as [n|] eqn:Hget; [|discriminate].
      specialize (IH costs (n :: acc) values budget Htail Hscan).
      time_unfold @T_search_scan. time_simpl. time_cbn. rewrite Hget.
      cbn [length] in *. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
    - pose proof (Hbound (Val v) (or_introl eq_refl)) as Hhead.
      pose proof (search_cell_bound_tail _ _ _ _ Hbound) as Htail.
      cbn [search_scan] in Hscan.
      specialize (IH costs (C.val_cost v :: acc) values budget Htail Hscan).
      time_unfold @T_search_scan. time_simpl. time_cbn.
      cbn [length] in *. rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** A detached frame consumes its newly final head before it can be parked again. *)
  Lemma search_scan_progress : forall costs acc i todo n child rest values,
    trie_get i costs = Some n ->
    search_scan costs acc (Id i :: todo) = inl (child, (rest, values)) ->
    length rest < length (Id i :: todo).
  Proof.
    intros costs acc i todo n child rest values Hget Hscan.
    cbn [search_scan] in Hscan. rewrite Hget in Hscan.
    destruct (Facts.search_scan_wait _ _ _ _ _ _ Hscan)
      as [pre [tail [Htodo [Hrest Hfacts]]]].
    rewrite Htodo, Hrest. cbn [length]. rewrite length_app. cbn [length]. lia.
  Qed.


  (** Source cell widths give a uniform price for each scan observation. *)
  Lemma search_cell_bound_width : forall costs w todo,
    (forall i, In (Id i) todo -> Pos.size_nat i <= w) ->
    (forall v, In (Val v) todo -> V.bits v <= w) ->
    search_cell_bound costs ((C.c_cost + 3) * N.of_nat (w + 1))%N todo.
  Proof.
    intros costs w todo Hids Hvalues [i|v] Hin.
    - specialize (Hids i Hin). PTrieT.trie_get_le.
      rewrite Nat2N.inj_add. nia.
    - specialize (Hvalues v Hin). pose proof (C.T_val_cost_le v) as Hcost.
      rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** A constructor cost bounds the bit width of each argument because it dominates that cost. *)
  Lemma T_search_fn_cost_le : forall f values w,
    N.size_nat (C.fn_cost f values) <= w ->
    (C.T_fn_cost f values <= C.c_cost * N.of_nat (length values + 1) *
      N.of_nat (w + 1))%N.
  Proof.
    intros f values w Hwidth.
    pose proof (dag_cost_width_le values (C.fn_cost f values)
      (C.fn_cost_super f values)) as Hchildren.
    eapply N.le_trans; [apply C.T_fn_cost_le|]. apply N.mul_le_mono_l. lia.
  Qed.

  Lemma search_frame_length : forall rs costs frame,
    Facts.search_frame_valid rs costs frame ->
    length (frame_costs frame) + length (frame_rest frame) =
      length (snd (fst (frame_row frame))).
  Proof.
    intros rs costs frame [Hrow [pre [Hkey [Hknown Hcosts]]]].
    rewrite Hcosts, Hkey, length_rev, length_app, dag_cost_cells_map, length_map.
    reflexivity.
  Qed.

  (** Parking touches one class-keyed binding and copies the fixed state fields. *)
  Lemma T_search_park_le : forall DB i frame (s : extraction_state V.t DB Q.t) w,
    Pos.size_nat i <= w ->
    (T_search_park i frame s <=
      64 * (PTrieT.c_trie + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros DB i frame s w Hwidth.
    pose proof (PTrieT.T_set_le _ i
      (frame :: match trie_get i (search_waiters s) with
        | Some frames => frames | None => [] end) (search_waiters s)) as Hset.
    change (PTrieCode.T_set i
      (frame :: match trie_get i (search_waiters s) with
        | Some frames => frames | None => [] end) (search_waiters s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    time_unfold @T_search_park. time_simpl. time_cbn.
    time_unfold @T_search_restate. time_simpl. time_cbn.
    PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma T_search_ltb_le : forall n old,
    (N.T_ltb n old <= N.of_nat (N.size_nat n) + 3)%N.
  Proof.
    intros n old. pose proof (N.T_compare_le n old) as Hcompare.
    time_unfold N.T_ltb. time_simpl. time_cbn. lia.
  Qed.

  (** A candidate offer pays at most one amortized heap insertion. *)
  Lemma T_search_offer_amort : forall DB P w i n row (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    Q.pending (search_queue s) < P -> Pos.size_nat i + N.size_nat n <= w ->
    (T_search_offer i n row s + Q.phi P w (search_queue (search_offer i n row s)) <=
      64 * (PTrieT.c_trie + 1) * N.of_nat (w + 1) +
      Q.c_pq * N.of_nat (Q.unit_pq P w) + Q.phi P w (search_queue s))%N.
  Proof.
    intros DB P w i n row s Hwf Hfits Hpending Hwidth.
    pose proof (Q.T_push_amort P w n i (search_queue s) Hwf Hfits Hpending Hwidth)
      as Hpush.
    pose proof (PTrieT.T_set_le _ i (n, row) (search_candidates s)) as Hset.
    change (PTrieCode.T_set i (n, row) (search_candidates s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    unfold search_offer.
    destruct (trie_get i (search_candidates s)) as [[old choice]|] eqn:Hget.
    - pose proof (T_search_ltb_le n old) as Hcompare.
      destruct (N.ltb n old) eqn:Hbetter.
      + time_unfold @T_search_offer. time_simpl. time_cbn. rewrite Hget, Hbetter.
        time_unfold @T_search_restate. time_simpl. time_cbn.
        cbn [search_restate search_queue]. PTrieT.trie_get_le.
        rewrite !Nat2N.inj_add in *. nia.
      + time_unfold @T_search_offer. time_simpl. time_cbn. rewrite Hget, Hbetter.
        PTrieT.trie_get_le. rewrite !Nat2N.inj_add in *. nia.
    - time_unfold @T_search_offer. time_simpl. time_cbn. rewrite Hget.
      time_unfold @T_search_restate. time_simpl. time_cbn.
      cbn [search_restate search_queue]. PTrieT.trie_get_le.
      rewrite !Nat2N.inj_add in *. nia.
  Qed.
  (** Residual cells pay repeated wakeups; the original key pays completion once. *)
  Definition search_frame_work (frame : extraction_frame V.t) :=
    length (frame_rest frame) + length (snd (fst (frame_row frame))) + 1.

  Definition search_frames_work (frames : list (extraction_frame V.t)) :=
    fold_right (fun frame total => search_frame_work frame + total) 0 frames.

  Definition search_waiting_work (waiters : ptrie (list (extraction_frame V.t))) :=
    search_trie_weight search_frames_work waiters.

  Definition search_cell_unit (w : nat) : N :=
    (128 * (PTrieT.c_trie + C.c_cost + 1) * N.of_nat (w + 1))%N.

  Definition search_work_unit (w : nat) : N := (4 * search_cell_unit w)%N.

  Definition search_push_unit (P w : nat) : N :=
    (Q.c_pq * N.of_nat (Q.unit_pq P w))%N.

  Definition search_frame_credit (P w : nat) (frame : extraction_frame V.t) : N :=
    (search_work_unit w * N.of_nat (search_frame_work frame) + search_push_unit P w)%N.

  Definition search_frames_credit (P w : nat) (frames : list (extraction_frame V.t)) : N :=
    (search_work_unit w * N.of_nat (search_frames_work frames) +
      search_push_unit P w * N.of_nat (length frames))%N.

  (** Search credit combines suspended-row work with the queue's public stale-entry credit. *)
  Definition search_potential {DB} (P w : nat) (s : extraction_state V.t DB Q.t) : N :=
    (search_work_unit w * N.of_nat (search_waiting_work (search_waiters s)) +
      search_push_unit P w * N.of_nat (Resources.search_waiter_count (search_waiters s)) +
      Q.phi P w (search_queue s))%N.

  Definition search_detached {DB} (i : positive) (s : extraction_state V.t DB Q.t) :=
    match trie_get i (search_waiters s) with Some frames => frames | None => [] end.

  Lemma search_frames_work_cons : forall frame frames,
    search_frames_work (frame :: frames) = search_frame_work frame + search_frames_work frames.
  Proof.
    reflexivity.
  Qed.

  Lemma search_frames_work_nil : search_frames_work [] = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma search_frames_credit_cons : forall P w frame frames,
    search_frames_credit P w (frame :: frames) =
      (search_frame_credit P w frame + search_frames_credit P w frames)%N.
  Proof.
    intros P w frame frames. unfold search_frames_credit, search_frame_credit.
    rewrite search_frames_work_cons. cbn [length].
    rewrite Nat2N.inj_add, Nat2N.inj_succ. nia.
  Qed.

  Lemma search_frames_credit_nil : forall P w, search_frames_credit P w [] = 0%N.
  Proof.
    intros P w. unfold search_frames_credit. rewrite search_frames_work_nil.
    cbn [length]. nia.
  Qed.

  Lemma search_park_work : forall DB i frame (s : extraction_state V.t DB Q.t),
    search_waiting_work (search_waiters (search_park i frame s)) =
      search_waiting_work (search_waiters s) + search_frame_work frame.
  Proof.
    intros DB i frame s. unfold search_waiting_work, search_park.
    cbn [search_restate search_waiters].
    pose proof (search_trie_weight_replace _ search_frames_work i
      (Some (frame :: match trie_get i (search_waiters s) with
        | Some frames => frames | None => [] end)) (search_waiters s)) as Hcharge.
    unfold PTrieCode.get in Hcharge. unfold PTrieCode.set.
    destruct (trie_get i (search_waiters s)); cbn beta iota zeta in Hcharge;
      rewrite search_frames_work_cons in Hcharge;
      rewrite ?search_frames_work_nil in Hcharge; lia.
  Qed.

  Lemma search_park_count : forall DB i frame (s : extraction_state V.t DB Q.t),
    Resources.search_waiter_count (search_waiters (search_park i frame s)) =
      S (Resources.search_waiter_count (search_waiters s)).
  Proof.
    intros DB i frame s.
    pose proof (Resources.search_park_load DB i frame s) as Hload.
    unfold Resources.search_load in Hload.
    change (Resources.search_waiter_count (search_waiters (search_park i frame s)) +
      Q.pending (search_queue s) =
      S (Resources.search_waiter_count (search_waiters s) + Q.pending (search_queue s)))
      in Hload.
    lia.
  Qed.

  (** Parking transfers exactly the frame's work and insertion credit into the state. *)
  Lemma search_park_potential : forall DB P w i frame (s : extraction_state V.t DB Q.t),
    search_potential P w (search_park i frame s) =
      (search_potential P w s + search_frame_credit P w frame)%N.
  Proof.
    intros DB P w i frame s. unfold search_potential, search_frame_credit.
    rewrite search_park_work, search_park_count, Nat2N.inj_add, Nat2N.inj_succ.
    cbn [search_park search_restate search_queue]. nia.
  Qed.

  (** Removing a waiting list transfers its entire credit to that detached active list. *)
  Lemma search_detached_potential : forall DB P w i costs candidates queue finals
      (s : extraction_state V.t DB Q.t),
    (search_potential P w (search_restate s costs candidates
        (PTrieCode.remove i (search_waiters s)) queue finals) +
      search_frames_credit P w (search_detached i s) + Q.phi P w (search_queue s) =
      search_potential P w s + Q.phi P w queue)%N.
  Proof.
    intros DB P w i costs candidates queue finals s.
    pose proof (search_trie_weight_remove _ search_frames_work i (search_waiters s))
      as Hwork.
    pose proof (search_trie_weight_remove _ (@length (extraction_frame V.t)) i
      (search_waiters s)) as Hcount.
    unfold search_potential, search_frames_credit, search_detached,
      search_waiting_work, Resources.search_waiter_count.
    cbn [search_restate search_waiters search_queue].
    destruct (trie_get i (search_waiters s)); cbn beta iota zeta in Hwork, Hcount |- *.
    - apply (f_equal N.of_nat) in Hwork. apply (f_equal N.of_nat) in Hcount.
      rewrite Nat2N.inj_add in Hwork, Hcount. rewrite <- Hwork, <- Hcount. nia.
    - rewrite search_frames_work_nil.
      cbn [length] in Hcount |- *.
      rewrite Nat.add_0_r in Hwork, Hcount. rewrite Hwork, Hcount. nia.
  Qed.

  Lemma search_start_potential : forall DB (db : DB) rs P w,
    search_potential P w (search_start db rs) = 0%N.
  Proof.
    intros DB db rs P w.
    unfold search_potential, search_waiting_work, Resources.search_waiter_count,
      search_trie_weight, search_entries_weight, search_start.
    cbn [search_waiters search_queue PTrieCode.elements PTrieCode.fold PTrieCode.fold_path
      rev_append fold_right].
    rewrite Q.phi_empty. nia.
  Qed.


  (** Source identifiers and literals fit the same physical-width envelope as heap entries. *)
  Definition search_syntax_width (rs : list (search_row V.t)) (w : nat) :=
    forall f k i, In (f, k, i) rs -> Pos.size_nat i <= w /\
      (forall j, In (Id j) k -> Pos.size_nat j <= w) /\
      (forall v, In (Val v) k -> V.bits v <= w).

  Lemma search_frame_suffix : forall rs costs frame item,
    Facts.search_frame_valid rs costs frame -> In item (frame_rest frame) ->
    In item (snd (fst (frame_row frame))).
  Proof.
    intros rs costs frame item [Hrow [pre [Hkey Hrest]]] Hin.
    rewrite Hkey. apply in_or_app. now right.
  Qed.

  Lemma search_cell_bound_mono : forall costs budget larger todo,
    search_cell_bound costs budget todo -> (budget <= larger)%N ->
    search_cell_bound costs larger todo.
  Proof.
    intros costs budget larger todo Hbound Hle item Hin.
    eapply N.le_trans; [exact (Hbound item Hin)|exact Hle].
  Qed.

  (** A valid frame inherits both the output lookup bound and all residual scan bounds. *)
  Lemma search_frame_syntax : forall rs costs frame w,
    Facts.search_frame_valid rs costs frame -> search_syntax_width rs w ->
    Pos.size_nat (snd (frame_row frame)) <= w /\
      search_cell_bound costs (search_cell_unit w) (frame_rest frame).
  Proof.
    intros rs costs [[[f k] i] todo acc] w Hframe Hsyntax.
    destruct (Hsyntax f k i (proj1 Hframe)) as [Houtput [Hids Hvalues]].
    split; [exact Houtput|].
    eapply search_cell_bound_mono; [apply search_cell_bound_width|].
    - intros j Hin. apply Hids.
      exact (search_frame_suffix rs costs _ (Id j) Hframe Hin).
    - intros v Hin. apply Hvalues.
      exact (search_frame_suffix rs costs _ (Val v) Hframe Hin).
    - unfold search_cell_unit. rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma search_frame_head_width : forall rs costs frame w i tail,
    Facts.search_frame_valid rs costs frame -> search_syntax_width rs w ->
    frame_rest frame = Id i :: tail -> Pos.size_nat i <= w.
  Proof.
    intros rs costs [[[f k] output] todo acc] w i tail Hframe Hsyntax Hhead.
    destruct (Hsyntax f k output (proj1 Hframe)) as [Houtput [Hids Hvalues]].
    apply Hids. apply (search_frame_suffix rs costs _ (Id i) Hframe).
    rewrite Hhead. now left.
  Qed.

  Definition search_frame_awake (costs : ptrie N) (frame : extraction_frame V.t) :=
    exists i tail n, frame_rest frame = Id i :: tail /\ trie_get i costs = Some n.

  Lemma search_frame_awake_progress : forall costs frame child rest values,
    search_frame_awake costs frame ->
    search_scan costs (frame_costs frame) (frame_rest frame) = inl (child, (rest, values)) ->
    length rest < length (frame_rest frame).
  Proof.
    intros costs frame child rest values [i [tail [n [Hhead Hget]]]] Hscan.
    rewrite Hhead in Hscan |- *. eapply search_scan_progress; eassumption.
  Qed.

  (** An initial scan may retain its first missing cell, which costs one registration fee. *)
  Lemma search_wait_charge_fresh : forall unit work fixed before after : N,
    (work + unit * after <= unit * (before + 1))%N -> (fixed <= unit)%N ->
    (after <= before)%N ->
    (work + fixed + (4 * unit) * after <= (4 * unit) * before + 4 * unit)%N.
  Proof.
    intros unit work fixed before after Hwork Hfixed Hlength.
    assert (Hscaled : (unit * after <= unit * before)%N)
      by (now apply N.mul_le_mono_l).
    nia.
  Qed.

  (** A wakeup that consumes a cell pays its scan and fixed overhead from residual credit. *)
  Lemma search_wait_charge_awake : forall unit work fixed before after : N,
    (work + unit * after <= unit * (before + 1))%N -> (fixed <= unit)%N ->
    (after + 1 <= before)%N ->
    (work + fixed + (4 * unit) * after <= (4 * unit) * before)%N.
  Proof.
    intros unit work fixed before after Hwork Hfixed Hlength.
    assert (Hscaled : (unit * (after + 1) <= unit * before)%N)
      by (now apply N.mul_le_mono_l).
    nia.
  Qed.

  Lemma search_frame_credit_unit : forall P w frame,
    (search_work_unit w <= search_frame_credit P w frame)%N.
  Proof.
    intros P w frame.
    assert (Hpositive : (1 <= N.of_nat (search_frame_work frame))%N)
      by (unfold search_frame_work; lia).
    assert (Hscaled : (search_work_unit w <=
      search_work_unit w * N.of_nat (search_frame_work frame))%N).
    { rewrite <- (N.mul_1_r (search_work_unit w)) at 1.
      now apply N.mul_le_mono_l. }
    unfold search_frame_credit. lia.
  Qed.

  (** Initial frame credit is linear in source count, key length and one push per source. *)
  Lemma search_initial_credit_bound : forall rs P w a,
    (forall row, In row rs -> length (snd (fst row)) <= a) ->
    (search_frames_credit P w (map search_new_frame rs) <=
      N.of_nat (length rs) *
        (search_work_unit w * N.of_nat (2 * a + 1) + search_push_unit P w))%N.
  Proof.
    induction rs as [|[[f k] i] rs IH]; intros P w a Hlength.
    - cbn [map length]. rewrite search_frames_credit_nil. nia.
    - specialize (IH P w a ltac:(intros row Hin; apply Hlength; now right)).
      pose proof (Hlength (f, k, i) (or_introl eq_refl)) as Hkey.
      assert (Hframe : (search_frame_credit P w (search_new_frame (f, k, i)) <=
        search_work_unit w * N.of_nat (2 * a + 1) + search_push_unit P w)%N).
      { unfold search_frame_credit, search_frame_work.
        cbn [search_new_frame frame_rest frame_row fst snd] in *.
        apply N.add_le_mono_r, N.mul_le_mono_l. lia. }
      cbn [map length]. rewrite search_frames_credit_cons, Nat2N.inj_succ. nia.
  Qed.
  Lemma search_resume_wait_state : forall DB f k i todo acc child rest values
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inl (child, (rest, values)) ->
    search_resume (ExtractionFrame (f, k, i) todo acc) s =
      search_park child (ExtractionFrame (f, k, i) rest values) s.
  Proof.
    intros DB f k i todo acc child rest values s Hget Hscan.
    unfold search_resume. cbn [frame_row frame_rest frame_costs]. now rewrite Hget, Hscan.
  Qed.

  Lemma search_resume_ready_state : forall DB f k i todo acc values
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inr values ->
    search_resume (ExtractionFrame (f, k, i) todo acc) s =
      search_offer i (C.fn_cost f values) (f, k) s.
  Proof.
    intros DB f k i todo acc values s Hget Hscan.
    unfold search_resume. cbn [frame_row frame_rest frame_costs]. now rewrite Hget, Hscan.
  Qed.

  Lemma T_search_resume_wait_eq : forall DB f k i todo acc child rest values
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inl (child, (rest, values)) ->
    T_search_resume (ExtractionFrame (f, k, i) todo acc) s =
      (6 + T_trie_get i (search_final_costs s) +
        T_search_scan (search_final_costs s) acc todo +
        T_search_park child (ExtractionFrame (f, k, i) rest values) s)%N.
  Proof.
    intros DB f k i todo acc child rest values s Hget Hscan.
    time_unfold @T_search_resume. time_simpl. time_cbn. rewrite Hget, Hscan. ring.
  Qed.

  Lemma T_search_resume_ready_eq : forall DB f k i todo acc values
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inr values ->
    T_search_resume (ExtractionFrame (f, k, i) todo acc) s =
      (6 + T_trie_get i (search_final_costs s) +
        T_search_scan (search_final_costs s) acc todo + C.T_fn_cost f values +
        T_search_offer i (C.fn_cost f values) (f, k) s)%N.
  Proof.
    intros DB f k i todo acc values s Hget Hscan.
    time_unfold @T_search_resume. time_simpl. time_cbn. rewrite Hget, Hscan. ring.
  Qed.

  (** A discarded frame pays the final-output check from its fixed completion reserve. *)
  Lemma T_search_resume_final_credit : forall DB P w f k i todo acc n
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = Some n -> Pos.size_nat i <= w ->
    (T_search_resume (ExtractionFrame (f, k, i) todo acc) s + 1 <=
      search_frame_credit P w (ExtractionFrame (f, k, i) todo acc))%N.
  Proof.
    intros DB P w f k i todo acc n s Hget Hwidth.
    eapply N.le_trans; [|apply search_frame_credit_unit].
    time_unfold @T_search_resume. time_simpl. time_cbn. rewrite Hget.
    PTrieT.trie_get_le. unfold search_work_unit, search_cell_unit.
    rewrite Nat2N.inj_add. nia.
  Qed.

  (** Scan-independent parking work fits one cell-price allowance. *)
  Lemma search_park_overhead : forall DB w i child frame (s : extraction_state V.t DB Q.t),
    Pos.size_nat i <= w -> Pos.size_nat child <= w ->
    (T_search_park child frame s + 7 + 2 * N.of_nat (Pos.size_nat i) <=
      search_cell_unit w)%N.
  Proof.
    intros DB w i child frame s Hi Hchild.
    pose proof (T_search_park_le DB child frame s w Hchild) as Hpark.
    unfold search_cell_unit. rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** A parked frame retains only its residual credit; fresh registration pays one extra fee. *)
  Lemma T_search_resume_wait_credit : forall DB P w fresh f k i todo acc child rest values
      (s : extraction_state V.t DB Q.t),
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inl (child, (rest, values)) ->
    search_cell_bound (search_final_costs s) (search_cell_unit w) todo ->
    Pos.size_nat i <= w -> Pos.size_nat child <= w ->
    (fresh = true \/ length rest < length todo) ->
    (T_search_resume (ExtractionFrame (f, k, i) todo acc) s + 1 +
      search_frame_credit P w (ExtractionFrame (f, k, i) rest values) <=
      search_frame_credit P w (ExtractionFrame (f, k, i) todo acc) +
      if fresh then search_work_unit w else 0)%N.
  Proof.
    intros DB P w fresh f k i todo acc child rest values s
      Hget Hscan Hbound Hi Hchild Hprogress.
    pose proof (T_search_scan_wait todo (search_final_costs s) acc child rest values
      (search_cell_unit w) Hbound Hscan) as Hwork.
    rewrite Nat2N.inj_add in Hwork.
    pose proof (search_park_overhead DB w i child
      (ExtractionFrame (f, k, i) rest values) s Hi Hchild) as Hfixed.
    rewrite (T_search_resume_wait_eq DB f k i todo acc child rest values s Hget Hscan).
    PTrieT.trie_get_le.
    unfold search_frame_credit, search_frame_work, search_work_unit.
    cbn [frame_rest frame_row fst snd]. rewrite !Nat2N.inj_add.
    destruct fresh.
    - destruct (Facts.search_scan_wait _ _ _ _ _ _ Hscan)
        as [pre [tail [Htodo [Hrest Hfacts]]]].
      assert (Hlength : (N.of_nat (length rest) <= N.of_nat (length todo))%N).
      { rewrite Htodo, Hrest, length_app. cbn [length]. lia. }
      pose proof (search_wait_charge_fresh _ _ _ _ _ Hwork Hfixed Hlength) as Hcharge.
      nia.
    - destruct Hprogress as [Hfalse|Hlength]; [discriminate|].
      assert (HlengthN : (N.of_nat (length rest) + 1 <= N.of_nat (length todo))%N) by lia.
      pose proof (search_wait_charge_awake _ _ _ _ _ Hwork Hfixed HlengthN) as Hcharge.
      nia.
  Qed.

  (** Completion pays its reverse, constructor call and map work without a logarithmic key factor. *)
  Lemma search_completion_charge : forall w key_length output_width,
    output_width <= w ->
    (N.of_nat key_length + 9 + 2 * N.of_nat output_width +
      C.c_cost * N.of_nat (key_length + 1) * N.of_nat (w + 1) +
      64 * (PTrieT.c_trie + 1) * N.of_nat (w + 1) <=
      search_cell_unit w * N.of_nat (key_length + 1))%N.
  Proof.
    intros w key_length output_width Hwidth. unfold search_cell_unit.
    rewrite !Nat2N.inj_add. nia.
  Qed.

  (** Completing a row consumes its one-time full-key and heap-insertion reserve. *)
  Lemma T_search_resume_ready_credit : forall DB P w f k i todo acc values
      (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    Q.pending (search_queue s) < P ->
    trie_get i (search_final_costs s) = None ->
    search_scan (search_final_costs s) acc todo = inr values ->
    search_cell_bound (search_final_costs s) (search_cell_unit w) todo ->
    length acc + length todo = length k ->
    Pos.size_nat i + N.size_nat (C.fn_cost f values) <= w ->
    (T_search_resume (ExtractionFrame (f, k, i) todo acc) s + 1 +
      Q.phi P w (search_queue (search_offer i (C.fn_cost f values) (f, k) s)) <=
      Q.phi P w (search_queue s) +
      search_frame_credit P w (ExtractionFrame (f, k, i) todo acc))%N.
  Proof.
    intros DB P w f k i todo acc values s Hwf Hfits Hpending
      Hget Hscan Hbound Hlength Hwidth.
    pose proof (T_search_scan_ready todo (search_final_costs s) acc values
      (search_cell_unit w) Hbound Hscan) as Hscan_time. rewrite Hlength in Hscan_time.
    assert (Hvalues_length : length values = length k).
    { destruct (Facts.search_scan_ready _ _ _ _ Hscan) as [Hknown Hvalues].
      rewrite Hvalues, length_app, length_rev, dag_cost_cells_map, length_map. exact Hlength. }
    pose proof (T_search_fn_cost_le f values w ltac:(lia)) as Hcost.
    rewrite Hvalues_length in Hcost.
    pose proof (T_search_offer_amort DB P w i (C.fn_cost f values) (f, k) s
      Hwf Hfits Hpending Hwidth) as Hoffer.
    fold (search_push_unit P w) in Hoffer.
    pose proof (search_completion_charge w (length k) (Pos.size_nat i) ltac:(lia)) as Hbody.
    rewrite (T_search_resume_ready_eq DB f k i todo acc values s Hget Hscan).
    PTrieT.trie_get_le.
    unfold search_frame_credit, search_frame_work, search_work_unit.
    cbn [frame_rest frame_row fst snd]. rewrite !Nat2N.inj_add in *. nia.
  Qed.


  (** One registration consumes one active frame's reserve and preserves the stored potential. *)
  Lemma T_search_resume_amort : forall DB rs P w fresh frame
      (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) -> Resources.search_load s < P ->
    Facts.search_frame_valid rs (search_final_costs s) frame ->
    search_syntax_width rs w -> Resources.search_rows_width rs (search_final_costs s) w ->
    (fresh = true \/ search_frame_awake (search_final_costs s) frame) ->
    (T_search_resume frame s + 1 + search_potential P w (search_resume frame s) <=
      search_potential P w s + search_frame_credit P w frame +
      if fresh then search_work_unit w else 0)%N.
  Proof.
    intros DB rs P w fresh [[[f k] i] todo acc] s
      Hwf Hfits Hload Hframe Hsyntax Hwidth Hfresh.
    destruct (search_frame_syntax rs (search_final_costs s) _ w Hframe Hsyntax)
      as [Houtput Hbound].
    destruct (trie_get i (search_final_costs s)) as [n|] eqn:Hget.
    - assert (Hsame : search_resume (ExtractionFrame (f, k, i) todo acc) s = s).
      { unfold search_resume. cbn [frame_row]. now rewrite Hget. }
      rewrite Hsame.
      pose proof (T_search_resume_final_credit DB P w f k i todo acc n s Hget Houtput)
        as Hcredit. lia.
    - destruct (search_scan (search_final_costs s) acc todo)
        as [[child [rest values]]|values] eqn:Hscan.
      + destruct (Facts.search_frame_wait rs (search_final_costs s) _ child rest values
          Hframe Hscan) as [Hparked [Hmissing [tail Hhead]]].
        pose proof (search_frame_head_width rs (search_final_costs s) _ w child tail
          Hparked Hsyntax Hhead) as Hchild.
        assert (Hprogress : fresh = true \/ length rest < length todo).
        { destruct Hfresh as [Htrue|Hawake]; [now left|right].
          exact (search_frame_awake_progress _ _ _ _ _ Hawake Hscan). }
        pose proof (T_search_resume_wait_credit DB P w fresh f k i todo acc child rest values
          s Hget Hscan Hbound Houtput Hchild Hprogress) as Hcredit.
        rewrite (search_resume_wait_state DB f k i todo acc child rest values s Hget Hscan),
          search_park_potential. lia.
      + destruct (Facts.search_frame_ready rs (search_final_costs s) _ values Hframe Hscan)
          as [Hknown Hvalues].
        cbn [frame_row fst snd] in Hknown, Hvalues.
        pose proof (Hwidth f k i (proj1 Hframe) Hknown) as Hentry.
        rewrite <- Hvalues in Hentry.
        assert (Hpending : Q.pending (search_queue s) < P)
          by (unfold Resources.search_load in Hload; lia).
        pose proof (search_frame_length rs (search_final_costs s) _ Hframe) as Hlength.
        pose proof (T_search_resume_ready_credit DB P w f k i todo acc values s
          Hwf Hfits Hpending Hget Hscan Hbound Hlength Hentry) as Hcredit.
        rewrite (search_resume_ready_state DB f k i todo acc values s Hget Hscan).
        unfold search_potential. rewrite Facts.search_offer_waiters. lia.
  Qed.

  (** Registering an active list telescopes its frame reserves and heap credit. *)
  Lemma T_search_resume_list_amort : forall DB rs P w fresh frames
      (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.fits w (search_queue s) ->
    length frames + Resources.search_load s <= P ->
    Forall (Facts.search_frame_valid rs (search_final_costs s)) frames ->
    search_syntax_width rs w -> Resources.search_rows_width rs (search_final_costs s) w ->
    (fresh = true \/ Forall (search_frame_awake (search_final_costs s)) frames) ->
    (T_search_resume_list frames s + search_potential P w (search_resume_list frames s) <=
      search_potential P w s + search_frames_credit P w frames +
      (if fresh then search_work_unit w else 0) * N.of_nat (length frames) + 1)%N.
  Proof.
    intros DB rs P w fresh frames. induction frames as [|frame frames IH];
      intros s Hwf Hfits Hcap Hframes Hsyntax Hwidth Hfresh.
    - time_unfold @T_search_resume_list. time_simpl. time_cbn.
      cbn [search_resume_list length]. rewrite search_frames_credit_nil. nia.
    - inversion Hframes as [|entry tail Hframe Hrest]; subst entry tail.
      assert (Hhead : fresh = true \/ search_frame_awake (search_final_costs s) frame).
      { destruct Hfresh as [Htrue|Hawake]; [now left|right].
        inversion Hawake; assumption. }
      assert (Htail : fresh = true \/
        Forall (search_frame_awake (search_final_costs s)) frames).
      { destruct Hfresh as [Htrue|Hawake]; [now left|right].
        inversion Hawake; assumption. }
      pose proof (T_search_resume_amort DB rs P w fresh frame s Hwf Hfits ltac:(cbn in Hcap; lia)
        Hframe Hsyntax Hwidth Hhead) as Hhead_time.
      pose proof (Resources.search_resume_load DB frame s Hwf) as Hload.
      change (Resources.search_load (search_resume frame s) <= S (Resources.search_load s))
        in Hload.
      destruct (Facts.search_resume_stable DB frame s)
        as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
      change (search_final_costs (search_resume frame s) = search_final_costs s) in Hcosts.
      assert (Hnext_frames : Forall
        (Facts.search_frame_valid rs (search_final_costs (search_resume frame s))) frames)
        by (now rewrite Hcosts).
      assert (Hnext_width : Resources.search_rows_width rs
        (search_final_costs (search_resume frame s)) w) by (now rewrite Hcosts).
      assert (Hnext_fresh : fresh = true \/
        Forall (search_frame_awake (search_final_costs (search_resume frame s))) frames)
        by (now rewrite Hcosts).
      specialize (IH (search_resume frame s) (Resources.search_resume_wf DB frame s Hwf)
        (Resources.search_resume_fits DB rs w frame s Hwf Hfits Hframe Hwidth)
        ltac:(cbn in Hcap; lia) Hnext_frames Hsyntax Hnext_width Hnext_fresh).
      time_unfold @T_search_resume_list. time_simpl. time_cbn.
      cbn [search_resume_list length].
      rewrite search_frames_credit_cons. rewrite ?Nat2N.inj_succ. nia.
  Qed.

  (** Initial state construction and frame mapping add only a linear driver overhead. *)
  Lemma T_search_initial_overhead : forall DB (db : DB) rs,
    (T_search_initial db rs <=
      T_search_resume_list (map search_new_frame rs) (search_start db rs) +
      8 * N.of_nat (length rs + 1))%N.
  Proof.
    intros DB db rs.
    assert (Hnew : forall row : search_row V.t, (T_search_new_frame row <= 3)%N).
    { intros [[f k] i]. time_unfold @T_search_new_frame. time_simpl. time_cbn. lia. }
    pose proof (Argent.Std.ListDef.T_map_le (@search_new_frame V.t)
      (fun row : search_row V.t => T_search_new_frame row) 3%N rs Hnew) as Hmap.
    pose proof (Argent.Std.Datatypes.T_length_le rs) as Hlength.
    time_unfold @T_search_initial. time_simpl. time_cbn.
    time_unfold @T_search_start. time_simpl. time_cbn.
    rewrite Nat2N.inj_add. nia.
  Qed.

  (** Initialization funds every parked frame and the queue from one reserve per source row. *)
  Lemma T_search_initial_amort : forall DB (db : DB) rs w,
    search_syntax_width rs w -> Resources.search_rows_width rs Empty w ->
    (T_search_initial db rs +
      search_potential (length rs) w (search_initial db rs) <=
      search_frames_credit (length rs) w (map search_new_frame rs) +
      search_work_unit w * N.of_nat (length rs) + 16 * N.of_nat (length rs + 1))%N.
  Proof.
    intros DB db rs w Hsyntax Hwidth.
    assert (Hstart : Resources.search_load (search_start db rs) = 0).
    { unfold Resources.search_load, Resources.search_waiter_count, search_trie_weight,
        search_entries_weight, search_start.
      cbn [search_waiters search_queue PTrieCode.elements PTrieCode.fold PTrieCode.fold_path
        rev_append fold_right]. now rewrite Q.pending_empty. }
    assert (Hframes : Forall (Facts.search_frame_valid rs Empty) (map search_new_frame rs)).
    { apply Forall_forall. intros frame Hin. apply in_map_iff in Hin.
      destruct Hin as [row [<- Hrow]]. now apply Facts.search_frame_new. }
    pose proof (T_search_resume_list_amort DB rs (length rs) w true
      (map search_new_frame rs) (search_start db rs) Q.wf_empty (Q.fits_empty w)
      ltac:(rewrite length_map, Hstart; lia) Hframes Hsyntax Hwidth (or_introl eq_refl))
      as Hregistered.
    rewrite length_map, search_start_potential in Hregistered.
    pose proof (T_search_initial_overhead DB db rs) as Hoverhead.
    unfold search_initial. cbn beta iota zeta in Hregistered.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.


  (** Every detached frame wakes at the class that the finalization has just installed. *)
  Lemma search_detached_awake : forall DB rs i n (s : extraction_state V.t DB Q.t),
    Facts.search_waiters_valid rs (search_final_costs s) (search_waiters s) ->
    Forall (search_frame_awake (PTrieCode.set i n (search_final_costs s)))
      (search_detached i s).
  Proof.
    intros DB rs i n s Hwaiting. unfold search_detached.
    destruct (trie_get i (search_waiters s)) as [frames|] eqn:Hget; [|constructor].
    apply Forall_forall. intros frame Hin.
    destruct (Hwaiting i frames frame Hget Hin) as [Hvalid [Hmissing [tail Hhead]]].
    exists i, tail, n. split; [exact Hhead|apply PTrie.get_set_same].
  Qed.

  (** The successful pop leaves room for all detached frames before their registration. *)
  Lemma search_detached_load : forall DB i n row queue (s : extraction_state V.t DB Q.t),
    Q.wf (search_queue s) -> Q.pop (search_queue s) = Some (n, i, queue) ->
    length (search_detached i s) + Resources.search_load
      (search_restate s (PTrieCode.set i n (search_final_costs s))
        (PTrieCode.remove i (search_candidates s)) (PTrieCode.remove i (search_waiters s))
        queue ((i, (n, row)) :: search_finalised s)) < Resources.search_load s.
  Proof.
    intros DB i n row queue s Hwf Hpop.
    pose proof (Q.pending_pop (search_queue s) n i queue Hwf Hpop) as Hpending.
    pose proof (search_trie_weight_remove _ (@length (extraction_frame V.t)) i
      (search_waiters s)) as Hcount.
    unfold search_detached, Resources.search_load, Resources.search_waiter_count.
    cbn [search_restate search_waiters search_queue].
    destruct (trie_get i (search_waiters s)); cbn [length] in Hcount |- *; lia.
  Qed.

  (** The fixed finalization update touches three trie bindings and one waiting-list pointer. *)
  Lemma T_search_finish_overhead : forall DB i n row queue
      (s : extraction_state V.t DB Q.t) w,
    Pos.size_nat i <= w ->
    (T_search_finish i n row queue s <=
      T_search_resume_list (search_detached i s)
        (search_restate s (PTrieCode.set i n (search_final_costs s))
          (PTrieCode.remove i (search_candidates s)) (PTrieCode.remove i (search_waiters s))
          queue ((i, (n, row)) :: search_finalised s)) +
      32 * (PTrieT.c_trie + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros DB i n row queue s w Hwidth.
    pose proof (PTrieT.T_set_le _ i n (search_final_costs s)) as Hset.
    pose proof (PTrieT.T_remove_le _ i (search_candidates s)) as Hcandidate.
    pose proof (PTrieT.T_remove_le _ i (search_waiters s)) as Hwaiting.
    change (PTrieCode.T_set i n (search_final_costs s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hset.
    change (PTrieCode.T_remove i (search_candidates s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hcandidate.
    change (PTrieCode.T_remove i (search_waiters s) <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat i + 1))%N in Hwaiting.
    time_unfold @T_search_finish. time_simpl. time_cbn.
    time_unfold @T_search_restate. time_simpl. time_cbn.
    unfold search_detached. PTrieT.trie_get_le.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** The waiting-list reserve pays every resumed row after a finalization. *)
  Lemma T_search_finish_amort : forall DB rs P w i n f k queue
      (s : extraction_state V.t DB Q.t),
    Facts.search_invariant rs s -> search_syntax_width rs w ->
    Q.fits w (search_queue s) -> Resources.search_load s <= P ->
    Q.pop (search_queue s) = Some (n, i, queue) ->
    trie_get i (search_candidates s) = Some (n, (f, k)) ->
    Resources.search_rows_width rs (PTrieCode.set i n (search_final_costs s)) w ->
    (T_search_finish i n (f, k) queue s +
      search_potential P w (search_finish i n (f, k) queue s) +
      Q.phi P w (search_queue s) <= search_potential P w s + Q.phi P w queue +
      32 * (PTrieT.c_trie + 1) * N.of_nat (w + 1) + 1)%N.
  Proof.
    intros DB rs P w i n f k queue s [Hcandidates [Hwaiting [[Hwf Hqueue] Htracking]]]
      Hsyntax Hfits Hload Hpop Hcandidate Hwidth.
    destruct (Hcandidates i n f k Hcandidate) as [Hmissing [Hrow Hready]].
    destruct (Hsyntax f k i Hrow) as [Houtput Hkeys].
    set (base := search_restate s (PTrieCode.set i n (search_final_costs s))
      (PTrieCode.remove i (search_candidates s)) (PTrieCode.remove i (search_waiters s))
      queue ((i, (n, (f, k))) :: search_finalised s)).
    pose proof (search_detached_load DB i n (f, k) queue s Hwf Hpop) as Hreleased.
    change (length (search_detached i s) + Resources.search_load base <
      Resources.search_load s) in Hreleased.
    pose proof (Facts.search_detached_valid rs (search_final_costs s) (search_waiters s)
      i n Hwaiting Hmissing) as Hframes.
    pose proof (search_detached_awake DB rs i n s Hwaiting) as Hawake.
    pose proof (T_search_resume_list_amort DB rs P w false (search_detached i s) base
      (Q.wf_pop _ _ _ _ Hwf Hpop) (Q.fits_pop _ _ _ _ _ Hwf Hfits Hpop)
      ltac:(lia) Hframes Hsyntax Hwidth (or_intror Hawake)) as Hregistered.
    cbn beta iota zeta in Hregistered. rewrite N.mul_0_l, N.add_0_r in Hregistered.
    change (T_search_resume_list (search_detached i s) base +
      search_potential P w (search_finish i n (f, k) queue s) <=
      search_potential P w base + search_frames_credit P w (search_detached i s) + 1)%N
      in Hregistered.
    pose proof (search_detached_potential DB P w i (PTrieCode.set i n (search_final_costs s))
      (PTrieCode.remove i (search_candidates s)) queue
      ((i, (n, (f, k))) :: search_finalised s) s) as Htransfer.
    fold base in Htransfer.
    pose proof (T_search_finish_overhead DB i n (f, k) queue s w Houtput) as Hoverhead.
    change (T_search_finish i n (f, k) queue s <=
      T_search_resume_list (search_detached i s) base +
      32 * (PTrieT.c_trie + 1) * N.of_nat (w + 1))%N in Hoverhead.
    clear - Hregistered Htransfer Hoverhead. lia.
  Qed.

  (** Fixed map work, cached-size lookup and one amortized pop share the heap envelope. *)
  Lemma search_step_charge : forall P w output_width,
    output_width <= w ->
    (Q.c_pq + Q.c_pq * N.of_nat (Q.unit_pq P w) +
      32 * (PTrieT.c_trie + 1) * N.of_nat (w + 1) + 4 * N.of_nat output_width + 6 <=
      64 * (PTrieT.c_trie + Q.c_pq + 1) * N.of_nat (Q.unit_pq P w))%N.
  Proof.
    intros P w output_width Hwidth.
    assert (Hunit : (N.of_nat (w + 1) <= N.of_nat (Q.unit_pq P w))%N).
    { change (N.of_nat (w + 1) <= N.of_nat ((Nat.log2 P + 1) * (w + 1)))%N.
      rewrite Nat2N.inj_mul, !Nat2N.inj_add. nia. }
    assert (Hmaps : (32 * (PTrieT.c_trie + 1) * N.of_nat (w + 1) <=
      32 * (PTrieT.c_trie + 1) * N.of_nat (Q.unit_pq P w))%N)
      by (now apply N.mul_le_mono_l).
    assert (Hpositive : (1 <= N.of_nat (Q.unit_pq P w))%N) by lia.
    assert (Hsize : (Q.c_pq <= Q.c_pq * N.of_nat (Q.unit_pq P w))%N).
    { rewrite <- (N.mul_1_r Q.c_pq) at 1. now apply N.mul_le_mono_l. }
    rewrite Nat2N.inj_add in Hunit. nia.
  Qed.

  (** A continuing search step spends row reserves and one public heap-operation allowance. *)
  Lemma T_search_step_amort : forall DB rs P w (s next : extraction_state V.t DB Q.t),
    Facts.search_invariant rs s -> search_syntax_width rs w ->
    Q.fits w (search_queue s) -> Resources.search_load s <= P ->
    Resources.search_rows_width rs (search_final_costs next) w ->
    search_step s = inl next ->
    (T_search_step s + search_potential P w next <= search_potential P w s +
      64 * (PTrieT.c_trie + Q.c_pq + 1) * N.of_nat (Q.unit_pq P w))%N.
  Proof.
    intros DB rs P w s next Hinv Hsyntax Hfits Hload Hwidth Hstep.
    destruct (Facts.search_step_cases DB rs s next Hinv Hstep)
      as [i [n [f [k [queue [Hpop [Hcandidate ->]]]]]]].
    change (T_search_step s + search_potential P w (search_finish i n (f, k) queue s) <=
      search_potential P w s +
      64 * (PTrieT.c_trie + Q.c_pq + 1) * N.of_nat (Q.unit_pq P w))%N.
    destruct (Facts.search_finish_fields DB i n (f, k) queue s)
      as [Hdb [Hrows [Hcount [Hcosts Hfinals]]]].
    rewrite Hcosts in Hwidth.
    pose proof (T_search_finish_amort DB rs P w i n f k queue s
      Hinv Hsyntax Hfits Hload Hpop Hcandidate Hwidth) as Hfinish.
    destruct Hinv as [Hcandidates [Hwaiting [[Hwf Hqueue] Htracking]]].
    destruct (Hcandidates i n f k Hcandidate) as [Hmissing [Hrow Hready]].
    destruct (Hsyntax f k i Hrow) as [Houtput Hkeys].
    assert (Hpending : Q.pending (search_queue s) <= P)
      by (unfold Resources.search_load in Hload; lia).
    pose proof (Q.T_pop_amort P w (search_queue s) Hwf Hfits Hpending) as Hpop_time.
    rewrite Hpop in Hpop_time. cbn beta iota zeta in Hpop_time.
    pose proof (Q.T_size_le (search_queue s)) as Hsize_time.
    pose proof (search_step_charge P w (Pos.size_nat i) Houtput) as Hcharge.
    destruct (Q.size (search_queue s)) as [|size] eqn:Hsize.
    - unfold search_step in Hstep. rewrite Hsize in Hstep. discriminate.
    - time_unfold @T_search_step. time_simpl. time_cbn.
      rewrite Hsize, Hpop, Hcandidate, Hmissing. PTrieT.trie_get_le. lia.
  Qed.


End SearchResourceT.

(** A finite bound on distinct finalisations supplies a terminating unary loop. *)
Lemma extraction_loop_complete {St Out} (step : St -> St + Out)
    (Inv : St -> Prop) (count : St -> nat) (bound : nat) :
  (forall s, Inv s -> count s <= bound) ->
  (forall s next, Inv s -> step s = inl next ->
    Inv next /\ count next = S (count s)) ->
  forall fuel s, Inv s -> bound < count s + fuel ->
    exists out last, loop_fuel step fuel s = inr out /\
      Inv last /\ step last = inr out.
Proof.
  intros Hbound Hstep fuel. induction fuel as [|fuel IH]; intros s Hinv Hfuel.
  - pose proof (Hbound s Hinv). lia.
  - cbn [loop_fuel]. destruct (step s) as [next|out] eqn:Hnext.
    + destruct (Hstep s next Hinv Hnext) as [Hinvnext Hcount].
      apply IH; [exact Hinvnext|]. rewrite Hcount. lia.
    + exists out, s. auto.
Qed.

(** A step invariant holds at every state reachable through continuing steps. *)
Lemma extraction_reachable_invariant {St Out} (step : St -> St + Out)
    (Inv : St -> Prop) :
  (forall s next, Inv s -> step s = inl next -> Inv next) ->
  forall s last, clos_refl_trans St (fun before after => step before = inl after) s last ->
    Inv s -> Inv last.
Proof.
  intros Hstep s last Hreach. induction Hreach; intro Hinv.
  - eapply Hstep; eassumption.
  - exact Hinv.
  - apply IHHreach2. now apply IHHreach1.
Qed.

(** Queue coverage and finalized-table validity together establish the complete search laws. *)
Module SearchCorrect (V : VALUE) (C : COST V) (Q : PQ).
  Module Search := SearchFacts V C Q.
  Module Finals := SearchFinals V C.
  Module Semantics := SearchSemantics V C.

  Definition search_verified {DB} (rs : list (search_row V.t))
      (s : extraction_state V.t DB Q.t) : Prop :=
    Search.search_invariant rs s /\
    Finals.finalised_valid rs (search_final_costs s) (search_finalised s) /\
    Semantics.search_knuth rs (search_final_costs s).

  (** Initialization combines the queue invariant with empty final observations. *)
  Lemma search_verified_initial : forall DB (db : DB) rs,
    Search.search_invariant rs (Search.search_initial db rs) ->
    search_verified rs (Search.search_initial db rs).
  Proof.
    intros DB db rs Hsearch. split; [exact Hsearch|].
    destruct (Search.search_initial_fields DB db rs) as [_ [_ [_ [Hcosts Hfinals]]]].
    rewrite Hcosts, Hfinals. split; [apply Finals.finalised_empty|].
    intros i n Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  (** A real minimum pop preserves finite attainment and optimality. *)
  Lemma search_verified_step : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_verified rs s -> Search.search_step s = inl next ->
    Search.search_invariant rs next -> search_verified rs next.
  Proof.
    intros DB rs s next [Hsearch [Hfinals Hoptimal]] Hstep Hnext.
    split; [exact Hnext|].
    destruct (Search.search_step_choice DB rs s next Hsearch Hstep)
      as [i [n [f [k [Hmissing [Hrow [Hknown [Hcost [Hprio [Hminimum
        [Hcosts Hentries]]]]]]]]]]].
    rewrite Hcosts, Hentries. split.
    - exact (Finals.finalised_valid_add rs (search_final_costs s) (search_finalised s)
        i n f k Hfinals Hmissing Hrow Hknown Hcost).
    - eapply Semantics.search_finalise_optimal.
      + exact Hoptimal.
      + exact (Search.search_invariant_covered DB rs s Hsearch).
      + exact Hmissing.
      + exact Hprio.
      + exact Hminimum.
  Qed.

  (** The source row count bounds every verified finalized list. *)
  Lemma search_verified_cardinality : forall DB rs (s : extraction_state V.t DB Q.t),
    search_verified rs s -> length (search_finalised s) <= length rs.
  Proof.
    intros DB rs s [_ [Hfinals _]].
    exact (Finals.finalised_cardinality rs (search_final_costs s) (search_finalised s) Hfinals).
  Qed.

  (** Each continuing verified step finalizes exactly one previously absent class. *)
  Lemma search_verified_grows : forall DB rs (s next : extraction_state V.t DB Q.t),
    search_verified rs s -> Search.search_step s = inl next ->
    length (search_finalised next) = S (length (search_finalised s)).
  Proof.
    intros DB rs s next [Hsearch _] Hstep.
    destruct (Search.search_step_choice DB rs s next Hsearch Hstep)
      as [i [n [f [k Hchoice]]]].
    destruct Hchoice as [_ [_ [_ [_ [_ [_ [_ Hentries]]]]]]].
    now rewrite Hentries.
  Qed.

  (** A verified stopping state contains every class with a finite represented tree. *)
  Lemma search_verified_stopped : forall DB rs (s : extraction_state V.t DB Q.t) entries,
    search_verified rs s -> Search.search_step s = inr entries ->
    Finals.finalised_valid rs (search_final_costs s) entries /\
    Semantics.search_knuth rs (search_final_costs s) /\
    Semantics.search_best_complete rs entries.
  Proof.
    intros DB rs s entries [Hsearch [Hfinals Hoptimal]] Hstep.
    destruct (Search.search_step_stopped DB s entries Hstep) as [-> Hsize].
    split; [exact Hfinals|]. split; [exact Hoptimal|].
    eapply Finals.finalised_complete.
    - exact Hfinals.
    - exact Hoptimal.
    - exact (Search.search_invariant_covered DB rs s Hsearch).
    - destruct Hsearch as [_ [_ [Hqueue _]]].
      exact (Search.search_queue_zero (search_candidates s) (search_queue s) Hqueue Hsize).
  Qed.

  (** The stored row-count fuel terminates and returns a complete optimal finite table. *)
  Lemma best_rows_correct : forall DB (db : DB) rs,
    Search.search_invariant rs (Search.search_initial db rs) ->
    (forall (s next : extraction_state V.t DB Q.t),
      Search.search_invariant rs s -> Search.search_step s = inl next ->
      Search.search_invariant rs next) ->
    loop_fuel Search.search_step (length rs + 1) (Search.search_initial db rs) =
      inr (Search.best_rows db rs) /\
    exists costs, Finals.finalised_valid rs costs (Search.best_rows db rs) /\
      Semantics.search_knuth rs costs /\
      Semantics.search_best_complete rs (Search.best_rows db rs).
  Proof.
    intros DB db rs Hinitial Hpreserve.
    assert (Hverified : search_verified rs (Search.search_initial db rs)).
    { now apply search_verified_initial. }
    assert (Hadvance : forall (s next : extraction_state V.t DB Q.t), search_verified rs s ->
      Search.search_step s = inl next -> search_verified rs next /\
      length (search_finalised next) = S (length (search_finalised s))).
    { intros s next Hinv Hstep. split.
      - apply (search_verified_step DB rs s next Hinv Hstep).
        apply (Hpreserve s next (proj1 Hinv) Hstep).
      - exact (search_verified_grows DB rs s next Hinv Hstep). }
    destruct (Search.search_initial_fields DB db rs)
      as [_ [_ [Hcount [_ Hentries]]]].
    destruct (extraction_loop_complete Search.search_step (search_verified rs)
      (fun s => length (search_finalised s)) (length rs)
      (search_verified_cardinality DB rs) Hadvance (length rs + 1)
      (Search.search_initial db rs) Hverified
      ltac:(change (length rs < length (search_finalised (Search.search_initial db rs)) +
        (length rs + 1)); lia))
      as [entries [last [Hrun [Hlast Hstop]]]].
    assert (Hbest : Search.best_rows db rs = entries).
    { unfold Search.best_rows. rewrite Hcount.
      replace (S (length rs)) with (length rs + 1) by lia.
      rewrite Hrun. reflexivity. }
    split; [now rewrite Hbest|]. rewrite Hbest.
    exists (search_final_costs last).
    exact (search_verified_stopped DB rs last entries Hlast Hstop).
  Qed.
End SearchCorrect.
(** Increasing the clock supplied for each step increases the loop clock. *)
Lemma extraction_loop_clock_mono {St Out} (run : St -> St + Out) (Ta Tb : St -> N) :
  (forall s, (Ta s <= Tb s)%N) -> forall fuel s,
  (T_loop_fuel run Ta fuel s <= T_loop_fuel run Tb fuel s)%N.
Proof.
  intros Hclock fuel. induction fuel as [|fuel IH]; intro s;
    time_unfold @T_loop_fuel.
  - lia.
  - destruct (run s) as [next|out].
    + specialize (IH next). specialize (Hclock s). lia.
    + specialize (Hclock s). lia.
Qed.

(** Row-number observations describe the plan without adding row-number runtime maps. *)
(** Self-delimiting pair and list encodings use only binary constructors. *)
Fixpoint extraction_glue (first last : positive) : positive :=
  match first with
  | xH => xO last
  | xO rest => xI (xO (extraction_glue rest last))
  | xI rest => xI (xI (extraction_glue rest last))
  end.
TimeFun extraction_glue.

Fixpoint extraction_list_code {A} (encode : A -> positive) (items : list A) : positive :=
  match items with
  | [] => xH
  | item :: rest => extraction_glue (encode item) (extraction_list_code encode rest)
  end.
TimeFun extraction_list_code.

(** Equal pair encodings identify both original components. *)
Lemma extraction_glue_inj : forall first last first' last',
  extraction_glue first last = extraction_glue first' last' -> first = first' /\ last = last'.
Proof.
  intro first. induction first as [first IH|first IH|]; intros last [first'|first'|] last' Heq;
    cbn [extraction_glue] in Heq; try discriminate.
  - injection Heq as Htail. destruct (IH last first' last' Htail) as [Hfirst Hlast].
    split; [now f_equal|exact Hlast].
  - injection Heq as Htail. destruct (IH last first' last' Htail) as [Hfirst Hlast].
    split; [now f_equal|exact Hlast].
  - injection Heq as Hlast. split; [reflexivity|exact Hlast].
Qed.

(** Pair encoding leaves enough bits for the complete second component. *)
Lemma extraction_glue_bits : forall first last,
  Pos.size_nat (extraction_glue first last) = 2 * Pos.size_nat first + Pos.size_nat last - 1.
Proof.
  induction first as [first IH|first IH|]; intro last; cbn [extraction_glue Pos.size_nat];
    rewrite ?IH; pose proof (Pos.size_nat_pos last); lia.
Qed.

(** Self-delimiting row codes keep specification row identifiers independent of database observations. *)
Fixpoint extraction_unglue (code : positive) : option (positive * positive) :=
  match code with
  | xH => None
  | xO rest => Some (xH, rest)
  | xI (xO rest) =>
    match extraction_unglue rest with
    | Some (first, last) => Some (xO first, last)
    | None => None
    end
  | xI (xI rest) =>
    match extraction_unglue rest with
    | Some (first, last) => Some (xI first, last)
    | None => None
    end
  | xI xH => None
  end.
TimeFun extraction_unglue.

Fixpoint extraction_identifier_children {V} (key : list (cell V)) : list positive :=
  match key with
  | [] => []
  | Id i :: rest => i :: extraction_identifier_children rest
  | Val _ :: rest => extraction_identifier_children rest
  end.
TimeFun extraction_identifier_children.

Definition extraction_cell_code {V} (encode : V -> positive) (item : cell V) : positive :=
  match item with Id i => xO i | Val v => xI (encode v) end.
TimeFun extraction_cell_code.

Fixpoint extraction_decode_identifiers (fuel : nat) (code : positive) : list positive :=
  match fuel with
  | O => []
  | S remaining =>
    match extraction_unglue code with
    | None => []
    | Some (item, rest) =>
      let children := extraction_decode_identifiers remaining rest in
      match item with xO i => i :: children | _ => children end
    end
  end.
TimeFun extraction_decode_identifiers.

Definition extraction_row_code {V} (encode : V -> positive) (row : search_row V) : positive :=
  extraction_glue (fst (fst row)) (extraction_glue (snd row) (extraction_list_code (extraction_cell_code encode) (snd (fst row)))).
TimeFun extraction_row_code.

Definition extraction_row_children (number : positive) : list positive :=
  match extraction_unglue number with
  | Some (_, rest) =>
    match extraction_unglue rest with
    | Some (_, key) => extraction_decode_identifiers (Pos.size_nat key) key
    | None => []
    end
  | None => []
  end.
TimeFun extraction_row_children.

Definition extraction_row_counter {V DB H} (s : extraction_state V DB H)
    (number : positive) : nat :=
  length (filter (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry))
    (search_finalised s))) (extraction_row_children number)).
TimeFun extraction_row_counter.

Definition extraction_ready_rows {V DB H} (encode : V -> positive)
    (fn_cost : positive -> list N -> N) (val_cost : V -> N)
    (s : extraction_state V DB H) : list (positive * N) :=
  map (fun row => (extraction_row_code encode row,
    fn_cost (fst (fst row)) (dag_cost_cells val_cost (search_final_costs s) (snd (fst row)))))
    (filter (fun row => Nat.eqb (extraction_row_counter s (extraction_row_code encode row)) 0 &&
      negb (existsb (fun entry => Pos.eqb (snd row) (fst entry)) (search_finalised s)))
      (search_rows s)).
TimeFun extraction_ready_rows.

(** The structural decoder exactly inverts a glued pair. *)
Lemma extraction_unglue_glue : forall first last,
  extraction_unglue (extraction_glue first last) = Some (first, last).
Proof.
  induction first as [first IH|first IH|]; intro last; cbn [extraction_glue extraction_unglue];
    now rewrite ?IH.
Qed.

(** A pair encoding is never the empty-list delimiter. *)
Lemma extraction_glue_nonempty : forall first last, extraction_glue first last <> xH.
Proof. intros [first|first|] last; discriminate. Qed.

(** Every coded list has enough bits to fuel one decoding step per cell. *)
Lemma extraction_list_code_fuel : forall V (encode : V -> positive) key,
  length key <= Pos.size_nat (extraction_list_code (extraction_cell_code encode) key).
Proof.
  intros V encode key. induction key as [|item rest IH]; cbn [length extraction_list_code].
  - cbn [Pos.size_nat]. lia.
  - rewrite extraction_glue_bits. pose proof (Pos.size_nat_pos (extraction_cell_code encode item)).
    pose proof (Pos.size_nat_pos (extraction_list_code (extraction_cell_code encode) rest)). lia.
Qed.

(** Decoding preserves identifier order and multiplicity while ignoring literal cells. *)
Lemma extraction_decode_identifiers_code : forall V (encode : V -> positive) key fuel,
  length key <= fuel ->
  extraction_decode_identifiers fuel (extraction_list_code (extraction_cell_code encode) key) =
    extraction_identifier_children key.
Proof.
  intros V encode key. induction key as [|item rest IH]; intros [|fuel] Hfuel;
    cbn [length] in Hfuel; try lia.
  - reflexivity.
  - reflexivity.
  - cbn [extraction_list_code extraction_decode_identifiers]. rewrite extraction_unglue_glue.
    rewrite IH by lia. destruct item; reflexivity.
Qed.

(** An encoded source row exposes exactly its identifier child occurrences. *)
Lemma extraction_row_children_code : forall V (encode : V -> positive) f key output,
  extraction_row_children (extraction_row_code encode (f, key, output)) =
    extraction_identifier_children key.
Proof.
  intros V encode f key output. unfold extraction_row_children, extraction_row_code.
  cbn [fst snd]. rewrite !extraction_unglue_glue.
  apply extraction_decode_identifiers_code, extraction_list_code_fuel.
Qed.

(** Injective value encodings give injective tagged cell encodings. *)
Lemma extraction_cell_code_inj : forall V (encode : V -> positive),
  (forall a b, encode a = encode b -> a = b) ->
  forall a b, extraction_cell_code encode a = extraction_cell_code encode b -> a = b.
Proof.
  intros V encode Hinj [i|v] [j|w] Heq; cbn [extraction_cell_code] in Heq;
    try discriminate; injection Heq as Heq; f_equal; auto.
Qed.

(** List coding preserves injectivity of its component encoding. *)
Lemma extraction_list_code_inj : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) ->
  forall first last, extraction_list_code encode first = extraction_list_code encode last -> first = last.
Proof.
  intros A encode Hinj first. induction first as [|a first IH]; intros [|b last] Heq;
    cbn [extraction_list_code] in Heq.
  - reflexivity.
  - exfalso. apply (extraction_glue_nonempty (encode b) (extraction_list_code encode last)).
    symmetry. exact Heq.
  - exfalso. exact (extraction_glue_nonempty (encode a) (extraction_list_code encode first) Heq).
  - destruct (extraction_glue_inj _ _ _ _ Heq) as [Hhead Htail]. f_equal.
    + exact (Hinj a b Hhead).
    + exact (IH last Htail).
Qed.

(** Row codes distinguish constructors, complete keys and output classes. *)
Lemma extraction_row_code_inj : forall V (encode : V -> positive),
  (forall a b, encode a = encode b -> a = b) ->
  forall first last, extraction_row_code encode first = extraction_row_code encode last -> first = last.
Proof.
  intros V encode Hinj [[f key] output] [[g args] target] Heq.
  unfold extraction_row_code in Heq. cbn [fst snd] in Heq.
  destruct (extraction_glue_inj _ _ _ _ Heq) as [Hfunction Hrest].
  destruct (extraction_glue_inj _ _ _ _ Hrest) as [Houtput Hkey].
  pose proof (extraction_list_code_inj _ _ (extraction_cell_code_inj V encode Hinj)
    key args Hkey) as Hargs. now subst.
Qed.

(** Ready entries are encoded source rows with no unfinished identifier occurrence. *)
Lemma extraction_ready_rows_counter : forall V DB H encode fn_cost val_cost
    (s : extraction_state V DB H) number cost,
  In (number, cost) (extraction_ready_rows encode fn_cost val_cost s) ->
  extraction_row_counter s number = 0.
Proof.
  intros V DB H encode fn_cost val_cost s number cost Hin.
  unfold extraction_ready_rows in Hin.
  apply in_map_iff in Hin as [row [Heq Hin]]. injection Heq as <- Hcost.
  apply filter_In in Hin as [_ Hready]. apply Bool.andb_true_iff in Hready as [Hcounter _].
  now apply Nat.eqb_eq in Hcounter.
Qed.

Module SearchGhosts (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V).
  Module Rows := ConstructorRows V I D.

  Definition row_identifiers (k : list (cell V.t)) : list positive :=
    flat_map (fun c => match c with Id i => [i] | Val _ => [] end) k.

  (** Row numbers start at one in the deterministic ghost constructor-row enumeration. *)
  Definition row_children (db : D.t) (number : positive) : list positive :=
    match nth_error (Rows.rows db) (Pos.to_nat number - 1) with
    | Some ((_, key), _) => row_identifiers key
    | None => []
    end.

  Definition row_counter {H} (s : extraction_state V.t D.t H) (number : positive) : nat :=
    length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (search_finalised s)))
      (row_children (search_database s) number)).

  Definition numbered_rows (db : D.t) : list (positive * search_row V.t) :=
    let rows := Rows.rows db in
    combine (map Pos.of_succ_nat (seq 0 (length rows))) rows.

  (** A ready observation names a real unfinalized row whose identifier children are final. *)
  Definition ready_rows {H} (s : extraction_state V.t D.t H) : list (positive * N) :=
    map (fun '(number, ((f, key), _)) =>
      (number, C.fn_cost f (map (chosen_cost C.val_cost (search_finalised s)) key)))
      (filter (fun entry =>
        Nat.eqb (row_counter s (fst entry)) 0 &&
        negb (existsb (fun final => Pos.eqb (snd (snd entry)) (fst final))
          (search_finalised s)))
        (numbered_rows (search_database s))).

  (** The counter is exactly the number of unfinished identifier occurrences in its row. *)
  Lemma row_counter_spec : forall H (s : extraction_state V.t D.t H) db number,
    search_database s = db ->
    row_counter s number = length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (search_finalised s)))
      (row_children db number)).
  Proof.
    intros H s db number Hdb. unfold row_counter. now rewrite Hdb.
  Qed.

  (** Filtering the numbered row list retains only rows with no unfinished child. *)
  Lemma ready_rows_counter : forall H (s : extraction_state V.t D.t H) number n,
    In (number, n) (ready_rows s) -> row_counter s number = 0.
  Proof.
    intros H s number n Hin. unfold ready_rows in Hin.
    apply in_map_iff in Hin as [[row_number [[f key] i]] [Heq Hin]].
    injection Heq as <- Hcost. apply filter_In in Hin as [_ Hready].
    apply Bool.andb_true_iff in Hready as [Hcounter _].
    now apply Nat.eqb_eq in Hcounter.
  Qed.
End SearchGhosts.

(** Continuing steps spend their potential while the final call pays a separate stop bound. *)
Lemma extraction_loop_clock_amort {St Out} (run : St -> St + Out) (T_run : St -> N)
    (Inv : St -> Prop) (potential : St -> N) (allowance stop : N) :
  (forall s next, Inv s -> run s = inl next ->
    Inv next /\ (T_run s + potential next <= potential s + allowance)%N) ->
  (forall s out, Inv s -> run s = inr out -> (T_run s <= stop)%N) ->
  forall fuel s, Inv s ->
    (T_loop_fuel run T_run fuel s <= potential s +
      (allowance + 1) * N.of_nat fuel + stop + 1)%N.
Proof.
  intros Hgo Hstop fuel. induction fuel as [|fuel IH]; intros s Hinv;
    time_unfold @T_loop_fuel.
  - cbn [N.of_nat]. lia.
  - rewrite Nat2N.inj_succ, N.mul_succ_r.
    destruct (run s) as [next|out] eqn:Hrun.
    + destruct (Hgo s next Hinv Hrun) as [Hnext Hcredit].
      specialize (IH next Hnext). lia.
    + specialize (Hstop s out Hinv Hrun). nia.
Qed.

(** Scaling a nonnegative amount by two factors at least one cannot reduce it. *)
Lemma extraction_scale_ge : forall amount first second,
  (1 <= first -> 1 <= second -> amount <= amount * first * second)%N.
Proof.
  intros amount first second Hfirst Hsecond.
  pose proof (N.mul_le_mono_l 1 first amount Hfirst) as Hleft.
  pose proof (N.mul_le_mono_l 1 second (amount * first) Hsecond) as Hright.
  rewrite N.mul_1_r in Hleft, Hright. exact (N.le_trans _ _ _ Hleft Hright).
Qed.

(** The public coefficient covers loop-control and stopping overhead beyond the two main charges. *)
Lemma extraction_driver_budget : forall rows budget first second coefficient,
  (1 <= rows -> 2 * rows <= budget -> 1 <= first -> 1 <= second -> 1 <= coefficient ->
    2 * coefficient * budget * first * second + 2 * coefficient * rows + rows + 1 <=
      4 * coefficient * budget * first * second)%N.
Proof.
  intros rows budget first second coefficient Hrows Hbudget Hfirst Hsecond Hcoefficient.
  assert (Hrow_credit : (rows <= coefficient * rows)%N).
  { pose proof (N.mul_le_mono_r 1 coefficient rows Hcoefficient). now rewrite N.mul_1_l in H. }
  assert (Hsmall : (2 * coefficient * rows + rows + 1 <= 4 * coefficient * rows)%N).
  { clear - Hrows Hrow_credit. nia. }
  assert (Hbase : (4 * coefficient * rows <= 2 * coefficient * budget)%N).
  { pose proof (N.mul_le_mono_l (2 * rows) budget (2 * coefficient) Hbudget).
    clear - H. nia. }
  pose proof (extraction_scale_ge (2 * coefficient * budget) first second Hfirst Hsecond)
    as Hscale.
  assert (Hpaid : (2 * coefficient * rows + rows + 1 <=
    2 * coefficient * budget * first * second)%N).
  { exact (N.le_trans _ _ _ Hsmall (N.le_trans _ _ _ Hbase Hscale)). }
  clear Hrows Hbudget Hfirst Hsecond Hcoefficient Hrow_credit Hsmall Hbase Hscale.
  nia.
Qed.

(** Initialization, amortized iterations and control overhead fit the public extraction budget. *)
Lemma extraction_best_budget : forall initial running total credit coefficient syntax rows
    arity depth first second,
  (1 <= rows -> 1 <= first -> 1 <= second -> 1 <= coefficient ->
    initial + credit <= coefficient * (syntax + rows * (arity + depth + 2)) * first * second ->
    running <= credit + (coefficient * (arity + depth + 2) * first * second + 1) * rows +
      coefficient * rows + 1 ->
    total <= initial + running + coefficient * rows ->
    total <= 4 * coefficient * (syntax + rows * (arity + depth + 2)) * first * second)%N.
Proof.
  intros initial running total credit coefficient syntax rows arity depth first second
    Hrows Hfirst Hsecond Hcoefficient Hinitial Hrunning Htotal.
  assert (Hmass : (coefficient * (arity + depth + 2) * first * second * rows <=
    coefficient * (syntax + rows * (arity + depth + 2)) * first * second)%N).
  { replace (coefficient * (arity + depth + 2) * first * second * rows)%N with
      (coefficient * (rows * (arity + depth + 2)) * first * second)%N by ring.
    apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_l. lia. }
  rewrite N.mul_add_distr_r, N.mul_1_l in Hrunning.
  assert (Hcombined : (total <=
    2 * (coefficient * (syntax + rows * (arity + depth + 2)) * first * second) +
      2 * (coefficient * rows) + rows + 1)%N) by lia.
  eapply N.le_trans; [exact Hcombined|].
  replace (2 * (coefficient * (syntax + rows * (arity + depth + 2)) * first * second) +
      2 * (coefficient * rows) + rows + 1)%N with
    (2 * coefficient * (syntax + rows * (arity + depth + 2)) * first * second +
      2 * coefficient * rows + rows + 1)%N by ring.
  apply extraction_driver_budget; try assumption. nia.
Qed.

Module ExtractCode (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V) (Q : PQ_OPS) <: EXTRACT_OPS V I D C.
  Include SearchCode V C Q.
  Definition inventory (ds : list decl) (sl : list (positive * list nat))
      : list (positive * (N * nat)) := inventory_scan (inventory_decl_table ds) sl 0%N.
  Definition best (cs : list (positive * (N * nat))) (db : D.t) : extraction_best V.t :=
    best_rows db (inventory_rows (fun slot => D.index slot false db)
      I.child I.children I.root cs).
  Definition check_dag (db : D.t) (c : positive) (g : extraction_dag V.t) : option N :=
    dag_check (dag_check_row (D.ids db) (fun i => fst (D.find i db))
      (fun f k => fst (D.lookup f k db))) C.fn_cost C.val_cost g c.
  Definition extract (cs : list (positive * (N * nat))) (db : D.t) (c : positive)
      : option (extraction_dag V.t) :=
    if N.ltb (D.ids db) (Npos c) then None else
      extraction_candidate (check_dag db) c (fst (D.find c db)) (best cs db).
End ExtractCode.

Module Extract (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V) (Q : PQ)
    <: EXTRACT V I D C.
  Include ExtractCode V I D C Q.
  Include EXTRACT_SPEC V I D C.
  Module SearchProof := SearchFacts V C Q.
  Module Enumeration := EnumeratedRows V I D.
  Module Semantics := SearchSemantics V C.
  Module DatabaseTrees := SearchDatabase V I D.

  (** A valid inventory enumerates every constructor row exactly once. *)
  Lemma inventory_rows_spec : forall cs db,
    D.wf db -> ctor_inventory cs db ->
    NoDup (Enumeration.enumerated_rows cs db) /\
    (forall f k i, In (f, k, i) (Enumeration.enumerated_rows cs db) <->
      row (D.view db) f k (Some (Id i))) /\
    length (Enumeration.enumerated_rows cs db) = length (Enumeration.Rows.rows db).
  Proof.
    intros cs db Hwf [Hnames [Hkinds [Hctors Hentries]]].
    assert (Hcovers : forall f k i, row (D.view db) f k (Some (Id i)) ->
      In f (map fst cs)).
    { intros f k i Hrow. apply (proj1 (Hkinds f)). now apply Hctors with k i. }
    split.
    - now apply Enumeration.enumerated_rows_nodup.
    - split.
      + intros f k i. split.
        * exact (Enumeration.enumerated_rows_sound cs db f k i Hwf Hentries).
        * exact (Enumeration.enumerated_rows_complete cs db f k i Hwf Hentries Hcovers).
      + now apply Enumeration.enumerated_rows_length.
  Qed.

  Definition unfold (g : extraction_dag V.t) (c : positive) : option (@Model.expr V.t) :=
    dag_unfold g c.
  Lemma inventory_spec : forall ds sl db, D.wf db -> D.slots db = sl ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f ss, lookup_kind ds f = Some OId -> lookup_sorts ds f = Some ss ->
      In (f, seq 0 (S (length ss))) sl) ->
    ctor_inventory (inventory ds sl) db.
  Proof.
    intros ds sl db Hwf Hslots Hkinds Hsorted Hfull.
    split; [apply inventory_scan_nodup |].
    split.
    - intro f. rewrite Hkinds. split.
      + intro Hkind.
        destruct (inventory_lookup_sorts ds f OId Hkind) as [ss Hsorts].
        eapply inventory_scan_complete.
        * rewrite inventory_decl_lookup, Hkind, Hsorts. reflexivity.
        * exact (Hfull f ss Hkind Hsorts).
      + intro Hin. apply in_map_iff in Hin as [[g [slot n]] [Heq Hin]].
        cbn [fst] in Heq. subst g.
        destruct (inventory_scan_sound _ _ _ _ _ _ Hin)
          as [positions [j [_ [_ [Hget _]]]]].
        rewrite inventory_decl_lookup in Hget.
        destruct (lookup_sorts ds f), (lookup_kind ds f) as [out|];
          try discriminate.
        inversion Hget. reflexivity.
    - split.
      + intros f k i Hrow.
        destruct (Hsorted _ _ _ Hrow) as [out [_ [Hkind Hout]]].
        destruct out; [discriminate |exact Hkind |discriminate].
      + intros f slot n Hin.
        destruct (inventory_scan_sound _ _ _ _ _ _ Hin)
          as [positions [j [Hnth [Hindex [Hget Hpositions]]]]].
        cbn [N.add] in Hindex. subst slot positions.
        exists (seq 0 (S n)). split.
        * unfold D.slot_of. rewrite Hslots, Nat2N.id. exact Hnth.
        * intros k o Hrow.
          destruct (Hsorted _ _ _ Hrow) as [out [Hsorts [Hkind Hout]]].
          rewrite inventory_decl_lookup, Hsorts, <- Hkinds, Hkind in Hget.
          injection Hget as Hlen Hout_kind. subst out.
          rewrite length_map in Hlen.
          destruct o as [[i|v]|]; try discriminate.
          split; [exact Hlen |]. split; [exists i; reflexivity |].
          cbn [option_list]. unfold D.permute.
          replace (S n) with (length (k ++ [Id i])).
          -- apply inventory_permute_full.
          -- rewrite length_app. cbn [length]. lia.
  Qed.

  Lemma unfold_spec : forall g c e, NoDup (map fst g) ->
    (unfold g c = Some e <-> dag_represents g c e).
  Proof.
    apply dag_unfold_spec.
  Qed.

  Module Correct := SearchCorrect V C Q.
  Module Finals := SearchFinals V C.

  (** Every finite source yields a complete attained optimal final table. *)
  Lemma best_rows_spec : forall (db : D.t) rs,
    exists costs, Finals.finalised_valid rs costs (best_rows db rs) /\
      Semantics.search_knuth rs costs /\ Semantics.search_best_complete rs (best_rows db rs).
  Proof.
    intros db rs.
    destruct (Correct.best_rows_correct D.t db rs
      (SearchProof.search_initial_invariant D.t db rs)
      (SearchProof.search_step_invariant D.t rs)) as [_ Hresult].
    exact Hresult.
  Qed.

  (** The public driver has the generic finite-row search specification. *)
  Lemma best_result : forall cs db,
    exists costs, Finals.finalised_valid (Enumeration.enumerated_rows cs db) costs (best cs db) /\
      Semantics.search_knuth (Enumeration.enumerated_rows cs db) costs /\
      Semantics.search_best_complete (Enumeration.enumerated_rows cs db) (best cs db).
  Proof.
    intros cs db. exact (best_rows_spec db (Enumeration.enumerated_rows cs db)).
  Qed.

  Lemma best_row : forall cs db c n f k, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    In (c, (n, (f, k))) (best cs db) ->
    row (D.view db) f k (Some (Id c)) /\
      n = C.fn_cost f (map (cost_of (best cs db)) k).
  Proof.
    intros cs db c n f k Hwf Hcanonical Hinventory Hin.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    destruct (best_result cs db) as [costs [Hfinals [Hoptimal Hcomplete]]].
    destruct (Finals.finalised_row (Enumeration.enumerated_rows cs db) costs (best cs db)
      c n f k Hfinals Hin) as [Hrow Hcost].
    split; [now apply (proj1 (Hrows f k c))|exact Hcost].
  Qed.

  Lemma best_optimal : forall cs db c e, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    represents (D.view db) (Id c) e ->
    exists n ch, In (D.repr db c, (n, ch)) (best cs db) /\ (n <= tree_cost e)%N.
  Proof.
    intros cs db c e Hwf Hcanonical Hinventory Hrep.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    destruct (best_result cs db) as [costs [Hfinals [Hoptimal Hcomplete]]].
    pose proof (DatabaseTrees.database_search_represents db (Enumeration.enumerated_rows cs db)
      Hwf Hcanonical (fun f k i Hrow => proj2 (Hrows f k i) Hrow) (Id c) e Hrep) as Hexact.
    change (search_represents (Enumeration.enumerated_rows cs db) (Id (D.repr db c)) e)
      in Hexact.
    destruct (Hcomplete (D.repr db c) e Hexact) as [n [ch Hin]].
    exists n, ch. split; [exact Hin|].
    exact (Finals.finalised_optimal (Enumeration.enumerated_rows cs db) costs (best cs db)
      Hfinals Hoptimal (D.repr db c) n ch Hin e Hexact).
  Qed.

  Lemma best_attained : forall cs db c n ch, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> In (c, (n, ch)) (best cs db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof.
    intros cs db c n ch Hwf Hcanonical Hinventory Hin.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    destruct (best_result cs db) as [costs [Hfinals [Hoptimal Hcomplete]]].
    destruct (Finals.finalised_attained (Enumeration.enumerated_rows cs db) costs (best cs db)
      Hfinals c n ch Hin) as [e [Hrep Hcost]].
    exists e. split; [|exact Hcost].
    exact (DatabaseTrees.search_database_represents db (Enumeration.enumerated_rows cs db)
      Hwf (fun f k i Hrow => proj1 (Hrows f k i) Hrow) (Id c) e Hrep).
  Qed.
  (** Canonical-key validation makes lookup's canonicalization an identity. *)
  Lemma checked_key_canonical : forall db k, D.wf db ->
    dag_check_key (D.ids db) (fun i => fst (D.find i db)) k = true ->
    map (D.canon db) k = k.
  Proof.
    intros db k Hwf Hcheck.
    transitivity (map (fun c : cell V.t => c) k); [|apply map_id].
    apply map_ext_in. intros [i|v] Hin; [|reflexivity].
    destruct (dag_check_key_spec V.t _ _ _ Hcheck i Hin) as [Halloc Hfixed].
    pose proof (proj1 (D.find_spec i db Hwf)) as Hfind.
    cbn [D.canon]. now rewrite <- Hfind, Hfixed.
  Qed.

  (** An accepted row check certifies the exact row named by the DAG entry. *)
  Lemma checked_row_present : forall db i f k, D.wf db ->
    dag_check_row (D.ids db) (fun j => fst (D.find j db))
      (fun f k => fst (D.lookup f k db)) i f k = true ->
    Model.row (D.view db) f k (Some (Id i)).
  Proof.
    intros db i f k Hwf Hcheck. unfold dag_check_row in Hcheck.
    destruct (dag_check_key (D.ids db) (fun j => fst (D.find j db)) k) eqn:Hkey;
      [|discriminate].
    destruct (fst (D.lookup f k db)) as [[[j|v]|]|] eqn:Hlookup; try discriminate.
    apply Pos.eqb_eq in Hcheck. subst j.
    pose proof (proj1 (D.lookup_spec f k db Hwf)) as Hspec.
    rewrite (checked_key_canonical db k Hwf Hkey), Hlookup in Hspec.
    apply (proj1 (D.old_row db f k (Some (Id i)) Hwf)). symmetry. exact Hspec.
  Qed.

  Lemma check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\
    exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e /\ n = tree_cost e.
  Proof.
    intros db c g n Hwf Hrun. unfold check_dag in Hrun.
    destruct (dag_check_correct V.t _ _ _ g c n Hrun)
      as [Hordered [Hchecked [e [Hrep [Hunfold Hcost]]]]].
    assert (Hrows : Forall (fun entry => Model.row (D.view db)
      (fst (snd entry)) (snd (snd entry)) (Some (Id (fst entry)))) g).
    { apply Forall_forall. intros [i [f k]] Hin. cbn [fst snd].
      apply (checked_row_present db i f k Hwf).
      exact (proj1 (Forall_forall _ _) Hchecked _ Hin). }
    split.
    - split; [exact (proj1 (dag_ordered_names V.t [] g Hordered)) |].
      split.
      + intros pre i f k post Heq child Hchild.
        exact (dag_ordered_prefix V.t [] g Hordered pre i f k post Heq child Hchild).
      + split; [exact Hrows |]. exists e. exact Hrep.
    - exists e. split.
      + apply (dag_unfold_model V.t (D.view db) g c e); [|exact Hrows |exact Hunfold].
        intro i. apply (proj2 (D.same_repr db i i Hwf)). reflexivity.
      + now split.
  Qed.

  Lemma extract_checked : forall cs db c g, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    extract cs db c = Some g -> exists n m ch,
      check_dag db c g = Some n /\ In (D.repr db c, (m, ch)) (best cs db) /\ (n <= m)%N.
  Proof.
    intros cs db c g Hwf Hcanonical Hinventory Hextract. unfold extract in Hextract.
    destruct (N.ltb (D.ids db) (Npos c)); [discriminate|].
    destruct (extraction_candidate_checked V.t (check_dag db) c
      (fst (D.find c db)) (best cs db) g Hextract) as [n [m [ch [Hcheck [Hin Hcost]]]]].
    rewrite (proj1 (D.find_spec c db Hwf)) in Hin.
    exists n, m, ch. split; [exact Hcheck|]. split; assumption.
  Qed.

End Extract.

(** The combined identifier and cost width fits the public product of positive widths. *)
Lemma extraction_initial_width : forall identifier_width cost_width,
  identifier_width + cost_width + 1 <= (identifier_width + 1) * (cost_width + 1).
Proof.
  intros identifier_width cost_width. nia.
Qed.

(** The initialization syntax allowance covers row work, queue depth and one empty scan. *)
Lemma extraction_initial_mass : forall syntax rows arity depth : N,
  (syntax + (arity + 1) * rows + 1 <=
    syntax + (rows + 1) * (arity + depth + 2))%N /\
  (rows * (arity + 1) <= syntax + (rows + 1) * (arity + depth + 2))%N /\
  (rows * (depth + 1) <= syntax + (rows + 1) * (arity + depth + 2))%N /\
  (rows + 1 <= syntax + (rows + 1) * (arity + depth + 2))%N.
Proof.
  intros syntax rows arity depth.
  assert (Hrow : (rows * (arity + 1) <= rows * (arity + depth + 2))%N).
  { apply N.mul_le_mono_l. lia. }
  assert (Hqueue : (rows * (depth + 1) <= (rows + 1) * (arity + depth + 2))%N).
  { apply N.mul_le_mono; lia. }
  assert (Hcount : (rows + 1 <= (rows + 1) * (arity + depth + 2))%N).
  { apply dag_budget_scale. lia. }
  replace ((rows + 1) * (arity + depth + 2))%N with
    (rows * (arity + depth + 2) + (arity + depth + 2))%N in * by ring.
  replace ((arity + 1) * rows)%N with (rows * (arity + 1))%N by ring.
  repeat split; lia.
Qed.

(** Inventory traversal and initial row credits fit the approved common step coefficient. *)
Lemma extraction_initial_budget : forall trie index database cost queue
    syntax rows arity depth unit width combined : N,
  (1 <= unit)%N -> (1 <= width)%N -> (combined <= unit * width)%N ->
  (1 + 1024 * (index + database + 1) * (syntax + (arity + 1) * rows + 1) * unit +
    rows * (512 * (trie + cost + 1) * combined * (2 * arity + 1) +
      queue * (depth + 1) * combined) +
    512 * (trie + cost + 1) * combined * rows + 16 * (rows + 1) <=
    (256 * 1024) * (trie + index + database + cost + queue + 1) *
      (syntax + (rows + 1) * (arity + depth + 2)) * unit * width)%N.
Proof.
  intros trie index database cost queue syntax rows arity depth unit width combined
    Hunit Hwidth Hcombined.
  set (coefficient := (trie + index + database + cost + queue + 1)%N).
  set (mass := (syntax + (rows + 1) * (arity + depth + 2))%N).
  set (budget := (coefficient * mass * unit * width)%N).
  assert (Hcoefficient : (1 <= coefficient)%N) by (unfold coefficient; lia).
  assert (Hindex : (index + database + 1 <= coefficient)%N) by (unfold coefficient; lia).
  assert (Hcost : (trie + cost + 1 <= coefficient)%N) by (unfold coefficient; lia).
  assert (Hqueue : (queue <= coefficient)%N) by (unfold coefficient; lia).
  destruct (extraction_initial_mass syntax rows arity depth)
    as [Hsyntax [Hrowmass [Hqueuemass Hcount]]].
  fold mass in Hsyntax, Hrowmass, Hqueuemass, Hcount.
  assert (Hmass : (mass <= budget)%N).
  { unfold budget. eapply N.le_trans.
    - apply enumeration_scale; [exact Hcoefficient |exact Hunit].
    - apply dag_budget_scale. exact Hwidth. }
  assert (Hone : (1 <= budget)%N) by lia.
  assert (Hwalk : (1024 * (index + database + 1) *
    (syntax + (arity + 1) * rows + 1) * unit <= 1024 * budget)%N).
  { replace (1024 * (index + database + 1) *
      (syntax + (arity + 1) * rows + 1) * unit)%N with
      (1024 * ((index + database + 1) * (syntax + (arity + 1) * rows + 1) * unit))%N
      by ring.
    apply N.mul_le_mono_l. unfold budget. eapply N.le_trans.
    - apply N.mul_le_mono_r, N.mul_le_mono; [exact Hindex |exact Hsyntax].
    - apply dag_budget_scale. exact Hwidth. }
  assert (Hwork : (rows * (512 * (trie + cost + 1) * combined * (2 * arity + 1)) +
    512 * (trie + cost + 1) * combined * rows <= 1024 * budget)%N).
  { replace (rows * (512 * (trie + cost + 1) * combined * (2 * arity + 1)) +
      512 * (trie + cost + 1) * combined * rows)%N with
      (1024 * ((trie + cost + 1) * (rows * (arity + 1)) * combined))%N by ring.
    apply N.mul_le_mono_l. unfold budget.
    replace (coefficient * mass * unit * width)%N with
      ((coefficient * mass) * (unit * width))%N by ring.
    apply N.mul_le_mono; [apply N.mul_le_mono; [exact Hcost |exact Hrowmass] |exact Hcombined]. }
  assert (Hpush : (rows * (queue * (depth + 1) * combined) <= budget)%N).
  { replace (rows * (queue * (depth + 1) * combined))%N with
      (queue * (rows * (depth + 1)) * combined)%N by ring.
    unfold budget. replace (coefficient * mass * unit * width)%N with
      ((coefficient * mass) * (unit * width))%N by ring.
    apply N.mul_le_mono;
      [apply N.mul_le_mono; [exact Hqueue |exact Hqueuemass] |exact Hcombined]. }
  assert (Hsetup : (16 * (rows + 1) <= 16 * budget)%N).
  { apply N.mul_le_mono_l. lia. }
  replace ((256 * 1024) * (trie + index + database + cost + queue + 1) *
    (syntax + (rows + 1) * (arity + depth + 2)) * unit * width)%N with
    (262144 * budget)%N by (unfold budget, coefficient, mass; ring).
  replace (rows * (512 * (trie + cost + 1) * combined * (2 * arity + 1) +
    queue * (depth + 1) * combined))%N with
    (rows * (512 * (trie + cost + 1) * combined * (2 * arity + 1)) +
      rows * (queue * (depth + 1) * combined))%N by ring.
  clear - Hone Hwalk Hwork Hpush Hsetup. lia.
Qed.

Module ExtractT (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I) (C : COST_T V)
    (Q : PQ_T)
    <: EXTRACT_ALL V I D C.
  Include Extract V I D C Q.
  TimeFun search_scan.
  TimeFun search_park.
  TimeFun search_offer.
  TimeFun search_resume.
  TimeFun search_resume_list.
  TimeFun search_start.
  TimeFun search_initial.
  TimeFun search_finish.
  TimeFun search_step.
  TimeFun best_rows.
  TimeFun inventory.
  TimeFun best.
  TimeFun check_dag.
  TimeFun extract.
  TimeFun unfold.
  Module Rows := ConstructorRows V I D.
  Module ResourceClocks := SearchResourceT V C Q.
  Definition R (db : D.t) : nat := length (Rows.rows db).
  Definition a (db : D.t) : nat := Rows.maximum_arity (Rows.rows db).
  Definition cost_width (db : D.t) : nat :=
    extraction_rows_width C.fn_cost C.val_cost (best_rows db (Rows.rows db)) (Rows.rows db).
  Definition c_ex : N :=
    (1024 * 1024) * (PTrieT.c_trie + I.c_ix + D.c_db + C.c_cost + Q.c_pq + 1).
  Lemma T_inventory_le : forall ds sl,
    (T_inventory ds sl <= c_ex * N.of_nat (layout_bits ds sl + 1) *
      N.of_nat (Nat.log2 (length sl) + 1))%N.
  Proof.
    intros ds sl.
    eapply N.le_trans with (m := (128 * (PTrieT.c_trie + 1) *
      N.of_nat (layout_bits ds sl + 1) * N.of_nat (Nat.log2 (length sl) + 1))%N).
    - pose proof (T_inventory_decl_table_le ds) as Hdecl.
      pose proof (T_inventory_scan_le sl (inventory_decl_table ds) 0%N (length sl)
        ltac:(cbn [N.to_nat]; lia)) as Hscan.
      time_unfold @T_inventory. time_simpl. time_cbn.
      unfold layout_bits. unfold inventory_slot_bits in Hscan.
      rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. nia.
    - apply N.mul_le_mono_r, N.mul_le_mono_r.
      unfold c_ex. nia.
  Qed.

  Lemma inventory_size : forall ds sl,
    inventory_bits (inventory ds sl) <=
      (layout_bits ds sl + 1) * (Nat.log2 (length sl) + 3).
  Proof.
    intros ds sl.
    pose proof (inventory_scan_size sl (inventory_decl_table ds) 0%N (length sl)
      ltac:(cbn [N.to_nat]; lia)) as Hsize.
    unfold inventory, layout_bits.
    unfold inventory_slot_bits in Hsize. nia.
  Qed.

  (** Constructor inventory supplies a full slot for each identifier-output row. *)
  Lemma inventory_row_slot : forall cs db f k i, ctor_inventory cs db ->
    Model.row (D.view db) f k (Some (Id i)) ->
    exists slot perm, D.slot_of db slot = Some (f, perm) /\
      D.permute perm (k ++ [Id i]) = k ++ [Id i].
  Proof.
    intros cs db f k i [_ [Hkinds [Hconstructors Hslots]]] Hrow.
    pose proof (proj1 (Hkinds f) (Hconstructors f k i Hrow)) as Hname.
    apply in_map_iff in Hname as [[g [slot n]] [Heq Hin]]. cbn [fst] in Heq. subst g.
    destruct (Hslots f slot n Hin) as [perm [Hslot Hfull]].
    exists slot, perm. split; [exact Hslot |].
    destruct (Hfull k (Some (Id i)) Hrow) as [_ [_ Hpermute]].
    exact Hpermute.
  Qed.

  Lemma R_spec : forall cs db, D.wf db -> ctor_inventory cs db ->
    exists rs, NoDup rs /\ length rs = R db /\
    forall f k i, In (f, k, i) rs <-> row (D.view db) f k (Some (Id i)).
  Proof.
    intros cs db Hwf Hinv. exists (Rows.rows db). split; [apply Rows.rows_nodup |].
    split; [reflexivity |]. intros f k i. split.
    - now apply Rows.rows_sound.
    - intro Hrow. apply Rows.rows_complete; [exact Hwf |exact Hrow |].
      eapply inventory_row_slot; eassumption.
  Qed.

  (** The executable inventory has the public constructor-row count. *)
  Lemma inventory_rows_count : forall cs db, D.wf db -> ctor_inventory cs db ->
    length (Enumeration.enumerated_rows cs db) = R db.
  Proof.
    intros cs db Hwf Hinventory.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [Hnodup [Hmembers _]].
    destruct (R_spec cs db Hwf Hinventory) as [rows [Hrows_nodup [Hrows_count Hrows]]].
    rewrite <- Hrows_count. apply Permutation_length, NoDup_Permutation;
      [exact Hnodup |exact Hrows_nodup |].
    intros [[f k] i]. rewrite Hmembers, Hrows. reflexivity.
  Qed.

  Lemma a_spec : forall cs db, D.wf db -> ctor_inventory cs db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> length k <= a db) /\
    (a db = 0 \/ exists f k i, row (D.view db) f k (Some (Id i)) /\ length k = a db).
  Proof.
    intros cs db Hwf Hinv. unfold a. split.
    - intros f k i Hrow. eapply Rows.maximum_arity_member.
      apply Rows.rows_complete; [exact Hwf |exact Hrow |].
      eapply inventory_row_slot; eassumption.
    - destruct (Rows.maximum_arity_attained (Rows.rows db)) as [Hzero |[f [k [i [Hin Heq]]]]].
      + now left.
      + right. exists f, k, i. split; [now apply Rows.rows_sound |exact Heq].
  Qed.

  (** Ghost row enumeration has the same exact stored-row support as the runtime source. *)
  Lemma ghost_rows_spec : forall cs db, D.wf db -> ctor_inventory cs db ->
    forall f k i, In (f, k, i) (Rows.rows db) <-> row (D.view db) f k (Some (Id i)).
  Proof.
    intros cs db Hwf Hinventory f k i. split.
    - now apply Rows.rows_sound.
    - intro Hrow. apply Rows.rows_complete; [exact Hwf|exact Hrow|].
      eapply inventory_row_slot; eassumption.
  Qed.

  (** Exact optimal costs do not depend on the ghost and executable row-list orders. *)
  Lemma cost_width_source : forall cs db, D.wf db -> ctor_inventory cs db ->
    cost_width db = extraction_rows_width C.fn_cost C.val_cost (best cs db) (Rows.rows db).
  Proof.
    intros cs db Hwf Hinventory.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    pose proof (ghost_rows_spec cs db Hwf Hinventory) as Hghost.
    destruct (best_rows_spec db (Rows.rows db)) as [left_costs [Hleft [Hleft_opt Hleft_all]]].
    destruct (best_result cs db) as [right_costs [Hright [Hright_opt Hright_all]]].
    assert (Hsame : forall r, In r (Rows.rows db) <->
      In r (Enumeration.enumerated_rows cs db)).
    { intros [[f k] i]. rewrite Hghost, Hrows. reflexivity. }
    assert (Hagree : forall c,
      chosen_cost C.val_cost (best_rows db (Rows.rows db)) c =
      chosen_cost C.val_cost (best cs db) c).
    { eapply Semantics.search_best_costs_agree; [exact Hsame| | |exact Hleft_all| | |exact Hright_all].
      - exact (Finals.finalised_attained (Rows.rows db) left_costs
          (best_rows db (Rows.rows db)) Hleft).
      - exact (Finals.finalised_optimal (Rows.rows db) left_costs
          (best_rows db (Rows.rows db)) Hleft Hleft_opt).
      - exact (Finals.finalised_attained (Enumeration.enumerated_rows cs db) right_costs
          (best cs db) Hright).
      - exact (Finals.finalised_optimal (Enumeration.enumerated_rows cs db) right_costs
          (best cs db) Hright Hright_opt). }
    unfold cost_width. now apply extraction_rows_width_agrees.
  Qed.

  Lemma cost_width_spec : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) ->
      N.size_nat (C.fn_cost f (map (cost_of (best cs db)) k)) <= cost_width db) /\
    (forall f k i v, row (D.view db) f k (Some (Id i)) -> In (Val v) k ->
      N.size_nat (C.val_cost v) <= cost_width db) /\
    (cost_width db = 0 \/
      (exists f k i, row (D.view db) f k (Some (Id i)) /\
        N.size_nat (C.fn_cost f (map (cost_of (best cs db)) k)) = cost_width db) \/
      (exists f k i v, row (D.view db) f k (Some (Id i)) /\ In (Val v) k /\
        N.size_nat (C.val_cost v) = cost_width db)).
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    rewrite (cost_width_source cs db Hwf Hinventory).
    pose proof (ghost_rows_spec cs db Hwf Hinventory) as Hrows.
    split.
    - intros f k i Hrow. apply extraction_rows_width_constructor with (i := i).
      now apply (proj2 (Hrows f k i)).
    - split.
      + intros f k i v Hrow Hin. eapply extraction_rows_width_literal.
        * exact (proj2 (Hrows f k i) Hrow).
        * exact Hin.
      + destruct (extraction_rows_width_attained V.t C.fn_cost C.val_cost
          (best cs db) (Rows.rows db)) as [Hzero|[Hconstructor|Hliteral]].
        * now left.
        * right. left. destruct Hconstructor as [f [k [i [Hin Hwidth]]]].
          exists f, k, i. split; [now apply (proj1 (Hrows f k i))|exact Hwidth].
        * right. right. destruct Hliteral as [f [k [i [v [Hrow [Hin Hwidth]]]]]].
          exists f, k, i, v. split; [now apply (proj1 (Hrows f k i))|].
          now split.
  Qed.


  Definition checker_row_budget (db : D.t) : N :=
    4 * (D.c_db + 1) * N.of_nat (D.unit db + 1).

  (** The guarded representative callback pays for one allocated find. *)
  Lemma checked_repr_clock : forall db i, D.wf db -> (Npos i <= D.ids db)%N ->
    (1 + (D.T_find i db + 1) <= checker_row_budget db)%N.
  Proof.
    intros db i Hwf Halloc. pose proof (D.T_find_le i db Hwf Halloc) as Hfind.
    unfold checker_row_budget. rewrite Nat2N.inj_add. nia.
  Qed.

  (** The lookup callback pays for key syntax at the fixed database spending unit. *)
  Lemma checked_lookup_clock : forall db f k, D.wf db ->
    (1 + (D.T_lookup f k db + 1) <= checker_row_budget db *
      N.of_nat (dag_key_bits V.encode k + 1))%N.
  Proof.
    intros db f k Hwf. pose proof (D.T_lookup_le f k db Hwf) as Hlookup.
    pose proof (dag_key_length V.t V.encode k) as Hlength.
    pose proof (dag_key_cells V.t V.encode k) as Hcells.
    unfold checker_row_budget. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** A database row check has a uniform syntax-linear callback bound. *)
  Lemma checked_row_clock : forall db i f k, D.wf db ->
    (T_dag_check_row (D.ids db) (fun j => fst (D.find j db))
      (fun j => 1 + (D.T_find j db + 1))
      (fun f k => fst (D.lookup f k db))
      (fun f k => 1 + (D.T_lookup f k db + 1)) i f k <=
    64 * (checker_row_budget db + 1) *
      N.of_nat (Pos.size_nat i + Pos.size_nat f + dag_key_bits V.encode k + 1))%N.
  Proof.
    intros db i f k Hwf.
    eapply N.le_trans.
    - apply (T_dag_check_row_le V.t V.encode (D.ids db) _ _ _ _ i f k
        (checker_row_budget db)); [intros j Hj; now apply checked_repr_clock |].
      now apply checked_lookup_clock.
    - apply N.mul_le_mono_l. lia.
  Qed.

  (** Every stored cell fits within the database's spending unit. *)
  Lemma stored_cell_unit : forall db f k o c, D.wf db ->
    Model.row (D.view db) f k o -> In c (k ++ option_list o) ->
    cell_bits V.encode c <= D.unit db.
  Proof.
    intros db f k o c Hwf Hrow Hin.
    pose proof (D.wmark_cells db f k o c Hwf Hrow Hin) as Hwidth.
    unfold D.unit. nia.
  Qed.

  (** Exact lookup of a stored row pays for its arity at one database unit. *)
  Lemma checked_lookup_row_clock : forall db f k o, D.wf db ->
    Model.row (D.view db) f k o ->
    (1 + (D.T_lookup f k db + 1) <=
      checker_row_budget db * N.of_nat (length k + 1))%N.
  Proof.
    intros db f k o Hwf Hrow.
    pose proof (D.T_lookup_le f k db Hwf) as Hlookup.
    pose proof (dag_key_cells V.t V.encode k) as Hcells.
    assert (Hkey : dag_key_bits V.encode k <= length k * (D.unit db + 1)).
    { apply dag_key_uniform. intros c Hin. eapply stored_cell_unit; try eassumption.
      apply in_or_app. now left. }
    unfold checker_row_budget. rewrite !Nat2N.inj_add in *.
    assert (Hmass : (N.of_nat
      (fold_right (fun c n => (cell_bits V.encode c + n)%nat) 0%nat k) <=
      N.of_nat (length k) * N.of_nat (D.unit db + 1))%N).
    { rewrite <- Nat2N.inj_mul. clear - Hcells Hkey. lia. }
    rewrite Nat2N.inj_add in Hmass. nia.
  Qed.

  (** Valid stored rows avoid multiplying their identifier syntax by the database unit. *)
  Lemma checked_row_stored_clock : forall db i f k, D.wf db ->
    Model.row (D.view db) f k (Some (Id i)) ->
    (T_dag_check_row (D.ids db) (fun j => fst (D.find j db))
      (fun j => 1 + (D.T_find j db + 1))
      (fun f k => fst (D.lookup f k db))
      (fun f k => 1 + (D.T_lookup f k db + 1)) i f k <=
      512 * (D.c_db + 1) * N.of_nat (length k + 1) *
        N.of_nat (D.unit db + 1))%N.
  Proof.
    intros db i f k Hwf Hrow.
    assert (Hout : Pos.size_nat i <= D.unit db).
    { pose proof (stored_cell_unit db f k (Some (Id i)) (Id i) Hwf Hrow
        ltac:(apply in_or_app; right; now left)) as Hwidth.
      cbn [cell_bits Pos.size_nat] in Hwidth. lia. }
    assert (Hkey : forall j, In (Id j) k -> Pos.size_nat j <= D.unit db).
    { intros j Hin. pose proof (stored_cell_unit db f k (Some (Id i)) (Id j) Hwf Hrow
        ltac:(apply in_or_app; now left)) as Hwidth.
      cbn [cell_bits Pos.size_nat] in Hwidth. lia. }
    eapply N.le_trans.
    - apply (T_dag_check_row_additive V.t (D.ids db) _ _ _ _ i f k
        (checker_row_budget db) (D.unit db)).
      + intros j Hj. now apply checked_repr_clock.
      + eapply checked_lookup_row_clock; eassumption.
      + exact Hout.
      + exact Hkey.
    - unfold checker_row_budget.
      replace (64 * (4 * (D.c_db + 1) * N.of_nat (D.unit db + 1) +
        N.of_nat (D.unit db + 1)) * N.of_nat (length k + 1))%N with
        ((64 * (4 * (D.c_db + 1) + 1)) * N.of_nat (length k + 1) *
          N.of_nat (D.unit db + 1))%N by ring.
      apply N.mul_le_mono_r, N.mul_le_mono_r. nia.
  Qed.

  (** Validation of database rows sums arities before applying the common spending unit. *)
  Lemma checked_validate_stored_clock : forall db g seen root, D.wf db ->
    (forall i f k, In (i, (f, k)) g -> Model.row (D.view db) f k (Some (Id i))) ->
    (T_dag_validate
      (dag_check_row (D.ids db) (fun j => fst (D.find j db))
        (fun f k => fst (D.lookup f k db)))
      (fun i f k => T_dag_check_row (D.ids db) (fun j => fst (D.find j db))
        (fun j => 1 + (D.T_find j db + 1))
        (fun f k => fst (D.lookup f k db))
        (fun f k => 1 + (D.T_lookup f k db + 1)) i f k) seen g root <=
      (128 * 1024) * (PTrieT.c_trie + D.c_db + 1) *
        N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1) +
        8 * N.of_nat (Pos.size_nat root + 1))%N.
  Proof.
    intros db g seen root Hwf Hrows.
    eapply N.le_trans.
    - apply (T_dag_validate_rows_le V.t V.encode _ _
        (512 * (D.c_db + 1) * N.of_nat (D.unit db + 1))%N (D.unit db)).
      + intros i f k Hin. pose proof (checked_row_stored_clock db i f k Hwf
          (Hrows i f k Hin)) as Hclock.
        replace (512 * (D.c_db + 1) * N.of_nat (D.unit db + 1) *
          N.of_nat (length k + 1))%N with
          (512 * (D.c_db + 1) * N.of_nat (length k + 1) *
            N.of_nat (D.unit db + 1))%N by ring.
        exact Hclock.
      + intros i f k Hin. pose proof (Hrows i f k Hin) as Hrow. split.
        * pose proof (stored_cell_unit db f k (Some (Id i)) (Id i) Hwf Hrow
            ltac:(apply in_or_app; right; now left)) as Hwidth.
          cbn [cell_bits Pos.size_nat] in Hwidth. lia.
        * intros c Hc. eapply stored_cell_unit; try eassumption.
          apply in_or_app. now left.
    - apply N.add_le_mono_r.
      replace (128 * (PTrieT.c_trie * N.of_nat (D.unit db + 1) +
        512 * (D.c_db + 1) * N.of_nat (D.unit db + 1) +
        N.of_nat (D.unit db + 1)) * N.of_nat (dag_row_work g + 1))%N with
        ((128 * (PTrieT.c_trie + 512 * (D.c_db + 1) + 1)) *
          N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1))%N by ring.
      apply N.mul_le_mono_r, N.mul_le_mono_r. nia.
  Qed.

  (** Checking actual stored rows charges their arities at one database spending unit. *)
  Lemma checked_certificate_stored_clock : forall db c g, D.wf db ->
    (forall i f k, In (i, (f, k)) g -> Model.row (D.view db) f k (Some (Id i))) ->
    (forall i f k, In (i, (f, k)) g -> Pos.size_nat f <= D.unit db) ->
    Pos.size_nat c <= D.unit db ->
    (T_check_dag db c g <=
      (256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
        N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1) *
        N.of_nat (match check_dag db c g with
          | Some n => N.size_nat n | None => 0 end + 1))%N.
  Proof.
    intros db c g Hwf Hrows Hnames Hroot.
    assert (Hsyntax_nat : cert_size V.encode g <=
      3 * dag_row_work g * (D.unit db + 1)).
    { apply dag_certificate_uniform. intros i f k Hin.
      pose proof (Hrows i f k Hin) as Hrow. split.
      - pose proof (stored_cell_unit db f k (Some (Id i)) (Id i) Hwf Hrow
          ltac:(apply in_or_app; right; now left)) as Hwidth.
        cbn [cell_bits Pos.size_nat] in Hwidth. lia.
      - split; [exact (Hnames i f k Hin) |].
        intros cell Hcell. eapply stored_cell_unit; try eassumption.
        apply in_or_app. now left. }
    assert (Hsyntax : (N.of_nat (cert_size V.encode g + 1) <=
      3 * N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1))%N).
    { assert (Hplus : cert_size V.encode g + 1 <=
        3 * (dag_row_work g + 1) * (D.unit db + 1)) by nia.
      assert (Hcast : (N.of_nat (cert_size V.encode g + 1) <=
        N.of_nat (3 * (dag_row_work g + 1) * (D.unit db + 1)))%N) by lia.
      rewrite !Nat2N.inj_mul in Hcast. exact Hcast. }
    assert (HrootN : (N.of_nat (Pos.size_nat c + 1) <= N.of_nat (D.unit db + 1))%N)
      by lia.
    time_unfold @T_check_dag. time_simpl. time_cbn.
    time_unfold @T_dag_check. time_simpl. time_cbn.
    unfold check_dag, dag_check.
    set (row_check := dag_check_row (D.ids db) (fun i => fst (D.find i db))
      (fun f k => fst (D.lookup f k db))) in *.
    set (row_clock := fun i f k => T_dag_check_row (D.ids db)
      (fun j => fst (D.find j db)) (fun j => (1 + (D.T_find j db + 1))%N)
      (fun f k => fst (D.lookup f k db))
      (fun f k => (1 + (D.T_lookup f k db + 1))%N) i f k) in *.
    pose proof (checked_validate_stored_clock db g Empty c Hwf Hrows) as Hvalidate.
    fold row_check row_clock in Hvalidate.
    pose proof (D.T_ids_le db) as Hids.
    destruct (dag_validate row_check Empty g c) eqn:Hvalid.
    - destruct (dag_validate_sound V.t row_check g Empty c []
        ltac:(intro i; unfold dag_seen; rewrite PTrie.get_empty; cbn;
          split; [discriminate |contradiction]) Hvalid) as [Hordered _].
      pose proof (PTrieT.T_set_le unit c tt Empty) as Hset.
      change (PTrieCode.T_set c tt Empty <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N in Hset.
      pose proof (T_dag_needed_le V.t V.encode g (PTrieCode.set c tt Empty)) as Hneeded.
      pose proof (T_dag_get_cost_le
        (dag_cost_table C.fn_cost C.val_cost (dag_needed g (PTrieCode.set c tt Empty)) g Empty)
        c) as Hget.
      pose proof (T_dag_cost_table_prefix_le V.t V.encode C.fn_cost
        (fun f cs => C.T_fn_cost f cs) C.val_cost (fun v => C.T_val_cost v) C.c_cost
        C.fn_cost_super C.T_fn_cost_le C.T_val_cost_le g c Hordered g [] eq_refl) as Hcosts.
      cbn [dag_cost_table] in Hcosts. time_cbn.
      eapply N.le_trans with (m := (1 + (D.c_db + (1 +
        ((128 * 1024) * (PTrieT.c_trie + D.c_db + 1) *
          N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1) +
         8 * N.of_nat (Pos.size_nat c + 1) +
         (PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1) +
          32 * (PTrieT.c_trie + 1) * N.of_nat (cert_size V.encode g + 1) +
          (256 * (PTrieT.c_trie + C.c_cost + 1) * N.of_nat (cert_size V.encode g + 1) *
             N.of_nat (N.size_nat (dag_get_cost (dag_cost_table C.fn_cost C.val_cost
               (dag_needed g (PTrieCode.set c tt Empty)) g Empty) c) + 1) +
           8 * N.of_nat (Pos.size_nat c + 1)))))))%N).
      + apply N.add_le_mono_l. apply N.add_le_mono; [exact Hids |].
        apply N.add_le_mono_l. apply N.add_le_mono; [exact Hvalidate |].
        apply N.add_le_mono.
        * apply N.add_le_mono; [exact Hset |exact Hneeded].
        * apply N.add_le_mono; [exact Hcosts |exact Hget].
      + apply dag_stored_check_budget; lia.
    - time_cbn.
      eapply N.le_trans with (m := (1 + (D.c_db + (1 +
        ((128 * 1024) * (PTrieT.c_trie + D.c_db + 1) *
          N.of_nat (dag_row_work g + 1) * N.of_nat (D.unit db + 1) +
         8 * N.of_nat (Pos.size_nat c + 1) + 0))))%N).
      + apply N.add_le_mono_l. apply N.add_le_mono; [exact Hids |].
        apply N.add_le_mono_l. apply N.add_le_mono; [exact Hvalidate |apply N.le_refl].
      + pose proof (dag_stored_check_budget PTrieT.c_trie D.c_db C.c_cost
          (N.of_nat (dag_row_work g + 1)) 0 (N.of_nat (Pos.size_nat c + 1))
          (N.of_nat (D.unit db + 1)) 1 ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) HrootN) as Hbudget.
        rewrite !N.mul_0_r, !N.mul_0_l, !N.add_0_r, !N.mul_1_r in Hbudget.
        rewrite N.mul_1_r, N.add_0_r. lia.
  Qed.

  (** The syntax-based checker estimate retains its original closed coefficient. *)
  Lemma checked_dag_syntax_clock : forall db c g, D.wf db ->
    (T_check_dag db c g <= (64 * 1024) *
      (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
      N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) *
      N.of_nat (D.unit db + 1) *
      N.of_nat (match check_dag db c g with
        | Some n => N.size_nat n
        | None => 0
        end + 1))%N.
  Proof.
    intros db c g Hwf.
    time_unfold @T_check_dag. time_simpl. time_cbn.
    time_unfold @T_dag_check. time_simpl. time_cbn.
    unfold check_dag, dag_check.
    set (row_check := dag_check_row (D.ids db) (fun i => fst (D.find i db))
      (fun f k => fst (D.lookup f k db))) in *.
    set (row_clock := fun i f k => T_dag_check_row (D.ids db)
      (fun j => fst (D.find j db)) (fun j => (1 + (D.T_find j db + 1))%N)
      (fun f k => fst (D.lookup f k db))
      (fun f k => (1 + (D.T_lookup f k db + 1))%N) i f k) in *.
    pose proof (T_dag_validate_le V.t V.encode row_check row_clock
      (64 * (checker_row_budget db + 1))%N
      ltac:(intros i f k; apply checked_row_clock; exact Hwf) g Empty c) as Hvalidate.
    pose proof (D.T_ids_le db) as Hids.
    destruct (dag_validate row_check Empty g c) eqn:Hvalid.
    - destruct (dag_validate_sound V.t row_check g Empty c []
        ltac:(intro i; unfold dag_seen; rewrite PTrie.get_empty; cbn;
          split; [discriminate |contradiction]) Hvalid) as [Hordered _].
      pose proof (PTrieT.T_set_le unit c tt Empty) as Hset.
      change (PTrieCode.T_set c tt Empty <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1))%N in Hset.
      pose proof (T_dag_needed_le V.t V.encode g (PTrieCode.set c tt Empty)) as Hneeded.
      pose proof (T_dag_get_cost_le
        (dag_cost_table C.fn_cost C.val_cost (dag_needed g (PTrieCode.set c tt Empty)) g Empty)
        c) as Hget.
      pose proof (T_dag_cost_table_prefix_le V.t V.encode C.fn_cost
        (fun f cs => C.T_fn_cost f cs) C.val_cost (fun v => C.T_val_cost v) C.c_cost
        C.fn_cost_super C.T_fn_cost_le C.T_val_cost_le g c Hordered g [] eq_refl) as Hcosts.
      cbn [dag_cost_table] in Hcosts. time_cbn.
      eapply N.le_trans with (m := (1 + (D.c_db + (1 +
        (64 * (PTrieT.c_trie + 64 * (checker_row_budget db + 1) + 1) *
          N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) +
         (PTrieT.c_trie * N.of_nat (Pos.size_nat c + 1) +
          32 * (PTrieT.c_trie + 1) * N.of_nat (cert_size V.encode g + 1) +
          (256 * (PTrieT.c_trie + C.c_cost + 1) * N.of_nat (cert_size V.encode g + 1) *
             N.of_nat (N.size_nat (dag_get_cost (dag_cost_table C.fn_cost C.val_cost
               (dag_needed g (PTrieCode.set c tt Empty)) g Empty) c) + 1) +
           8 * N.of_nat (Pos.size_nat c + 1)))))))%N).
      + apply N.add_le_mono_l. apply N.add_le_mono; [exact Hids |].
        apply N.add_le_mono_l. apply N.add_le_mono; [exact Hvalidate |].
        apply N.add_le_mono.
        * apply N.add_le_mono; [exact Hset |exact Hneeded].
        * apply N.add_le_mono; [exact Hcosts |exact Hget].
      + clear Hvalidate Hids Hset Hneeded Hget Hcosts Hordered Hvalid.
        unfold checker_row_budget.
        apply dag_check_budget; lia.
    - time_cbn.
      eapply N.le_trans with (m := (1 + (D.c_db + (1 +
        (64 * (PTrieT.c_trie + 64 * (checker_row_budget db + 1) + 1) *
          N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) + 0))))%N).
      + apply N.add_le_mono_l. apply N.add_le_mono; [exact Hids |].
        apply N.add_le_mono_l. apply N.add_le_mono; [exact Hvalidate |apply N.le_refl].
      + pose proof (dag_check_budget PTrieT.c_trie D.c_db C.c_cost
          (N.of_nat (cert_size V.encode g + Pos.size_nat c + 1)) 0 0
          (N.of_nat (D.unit db + 1)) 1 ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia)) as Hbudget.
        rewrite !N.mul_0_r, !N.mul_0_l, !N.add_0_r, !N.mul_1_r in Hbudget.
        unfold checker_row_budget. rewrite N.mul_1_r, N.add_0_r.
        exact Hbudget.
  Qed.

  Lemma T_check_dag_le : forall db c g, D.wf db ->
    (T_check_dag db c g <= c_ex * N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) *
      N.of_nat (D.unit db + 1) *
      N.of_nat (match check_dag db c g with
        | Some n => N.size_nat n
        | None => 0
        end + 1))%N.
  Proof.
    intros db c g Hwf.
    eapply N.le_trans; [exact (checked_dag_syntax_clock db c g Hwf) |].
    apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_r. unfold c_ex. nia.
  Qed.

  (** The cached allocation counter fits the public database spending unit. *)
  Lemma database_ids_unit : forall db, N.size_nat (D.ids db) <= D.unit db.
  Proof.
    intro db. pose proof (extraction_N_width_log (D.ids db)). unfold D.unit. nia.
  Qed.

  (** The allocation guard ensures that the queried root fits the database unit. *)
  Lemma allocated_root_unit : forall db c, (Npos c <= D.ids db)%N ->
    Pos.size_nat c <= D.unit db.
  Proof.
    intros db c Hallocated.
    assert (Hwidth : Pos.size_nat c <= N.size_nat (D.ids db)).
    { destruct (D.ids db) as [|bound]; [lia |]. cbn [N.size_nat].
      destruct (Pos.eq_dec c bound) as [-> |Hneq]; [lia |].
      apply Pos.size_nat_monotone. lia. }
    pose proof (database_ids_unit db). lia.
  Qed.

  (** A stored constructor name is bounded by the database high-water mark. *)
  Lemma stored_constructor_name_unit : forall cs db f k i,
    D.wf db -> ctor_inventory cs db -> Model.row (D.view db) f k (Some (Id i)) ->
    Pos.size_nat f <= D.unit db.
  Proof.
    intros cs db f k i Hwf [_ [_ [Hconstructors _]]] Hrow.
    pose proof (Hconstructors f k i Hrow) as Hkind.
    pose proof (D.wmark_names db f Hwf ltac:(rewrite Hkind; discriminate)) as Hwidth.
    unfold D.unit. nia.
  Qed.

  (** The selected table contains at most one chosen row for each source row. *)
  Lemma best_length : forall cs db, D.wf db -> ctor_inventory cs db ->
    length (best cs db) <= R db.
  Proof.
    intros cs db Hwf Hinventory.
    destruct (best_result cs db) as [costs [Hfinals _]].
    pose proof (Finals.finalised_cardinality (Enumeration.enumerated_rows cs db)
      costs (best cs db) Hfinals) as Hlength.
    rewrite (inventory_rows_count cs db Hwf Hinventory) in Hlength. exact Hlength.
  Qed.

  (** Every row copied into the selected certificate is a stored constructor row. *)
  Lemma best_certificate_row : forall cs db i f k,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    In (i, (f, k)) (extraction_certificate (best cs db)) ->
    Model.row (D.view db) f k (Some (Id i)).
  Proof.
    intros cs db i f k Hwf Hcanonical Hinventory Hin.
    apply Finals.certificate_entry in Hin as [n Hentry].
    exact (proj1 (best_row cs db i n f k Hwf Hcanonical Hinventory Hentry)).
  Qed.

  (** The selected certificate has at most the source row count times its maximum arity. *)
  Lemma best_certificate_work : forall cs db,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    dag_row_work (extraction_certificate (best cs db)) <= R db * (a db + 1).
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    assert (Harity : forall i f k, In (i, (f, k)) (extraction_certificate (best cs db)) ->
      length k <= a db).
    { intros i f k Hin. apply (proj1 (a_spec cs db Hwf Hinventory) f k i).
      now apply best_certificate_row with cs. }
    pose proof (dag_row_work_length V.t (extraction_certificate (best cs db)) (a db) Harity)
      as Hwork.
    assert (Hlength : length (extraction_certificate (best cs db)) <= R db).
    { unfold extraction_certificate. rewrite <- rev_alt, length_rev, length_map.
      now apply best_length. }
    eapply Nat.le_trans; [exact Hwork |]. apply Nat.mul_le_mono_r. exact Hlength.
  Qed.

  (** Every selected cost is one of the constructor costs covered by cost_width. *)
  Lemma best_cost_width : forall cs db i n ch,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    In (i, (n, ch)) (best cs db) -> N.size_nat n <= cost_width db.
  Proof.
    intros cs db i n [f k] Hwf Hcanonical Hinventory Hin.
    destruct (best_row cs db i n f k Hwf Hcanonical Hinventory Hin) as [Hrow Hcost].
    rewrite Hcost. exact (proj1 (cost_width_spec cs db Hwf Hcanonical Hinventory) f k i Hrow).
  Qed.

  (** Checking a selected certificate returns a cost covered by the source width. *)
  Lemma best_certificate_check_width : forall cs db c,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    match check_dag db c (extraction_certificate (best cs db)) with
    | Some n => N.size_nat n | None => 0 end <= cost_width db.
  Proof.
    intros cs db c Hwf Hcanonical Hinventory.
    destruct (best_result cs db) as [costs [Hfinals _]].
    unfold check_dag. eapply Finals.certificate_check_width; [exact Hfinals |].
    intros i n ch Hin. eapply best_cost_width; eassumption.
  Qed.

  (** The selected certificate checker fits the final extraction row and width envelope. *)
  Lemma best_certificate_clock : forall cs db c,
    D.wf db -> D.canonical db -> ctor_inventory cs db -> Pos.size_nat c <= D.unit db ->
    (T_check_dag db c (extraction_certificate (best cs db)) <=
      (256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
        N.of_nat (R db + 1) * N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db c Hwf Hcanonical Hinventory Hroot.
    pose proof (checked_certificate_stored_clock db c (extraction_certificate (best cs db))
      Hwf (fun i f k Hin => best_certificate_row cs db i f k Hwf Hcanonical Hinventory Hin)
      ltac:(intros i f k Hin; eapply stored_constructor_name_unit;
        [exact Hwf |exact Hinventory |];
        exact (best_certificate_row cs db i f k Hwf Hcanonical Hinventory Hin)) Hroot)
      as Hcheck.
    pose proof (best_certificate_check_width cs db c Hwf Hcanonical Hinventory) as Hwidth.
    pose proof (best_certificate_work cs db Hwf Hcanonical Hinventory) as Hwork.
    assert (Hwork_nat : dag_row_work (extraction_certificate (best cs db)) + 1 <=
      (R db + 1) * (a db + 1)) by nia.
    assert (HworkN : (N.of_nat (dag_row_work (extraction_certificate (best cs db)) + 1) <=
      N.of_nat (R db + 1) * N.of_nat (a db + 1))%N).
    { rewrite <- Nat2N.inj_mul. lia. }
    eapply N.le_trans; [exact Hcheck |].
    eapply N.le_trans with (m :=
      ((256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
        N.of_nat (dag_row_work (extraction_certificate (best cs db)) + 1) *
        N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N).
    - apply N.mul_le_mono_l. lia.
    - replace ((256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
        N.of_nat (R db + 1) * N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N with
        ((256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
          (N.of_nat (R db + 1) * N.of_nat (a db + 1)) * N.of_nat (D.unit db + 1) *
          N.of_nat (cost_width db + 1))%N by ring.
      apply N.mul_le_mono_r, N.mul_le_mono_r, N.mul_le_mono_l. exact HworkN.
  Qed.

  Lemma T_extract_le : forall cs db c, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_extract cs db c <= T_best cs db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db c Hwf Hcanonical Hinventory.
    pose proof (D.T_ids_le db) as Hids.
    pose proof (database_ids_unit db) as Hids_width.
    pose proof (extraction_guard_clock (D.ids db) c) as Hguard_raw.
    assert (Hguard : (N.T_ltb (D.ids db) (Npos c) <= N.of_nat (D.unit db + 1) + 3)%N)
      by lia.
    pose proof (best_length cs db Hwf Hinventory) as Hlength.
    assert (HlengthN : (N.of_nat (length (best cs db) + 1) <= N.of_nat (R db + 1))%N)
      by lia.
    pose proof (extraction_total_budget PTrieT.c_trie I.c_ix D.c_db C.c_cost Q.c_pq
      (N.of_nat (R db + 1)) (N.of_nat (a db + 1)) (N.of_nat (D.unit db + 1))
      (N.of_nat (cost_width db + 1)) (N.of_nat (length (best cs db) + 1))
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HlengthN) as Hbudget.
    time_unfold @T_extract. time_simpl.
    destruct (N.ltb (D.ids db) (Npos c)) eqn:Hallocated.
    - clear - Hids Hguard Hbudget. unfold c_ex.
      set (rowsN := N.of_nat (R db + 1)) in *.
      set (arityN := N.of_nat (a db + 1)) in *.
      set (unitN := N.of_nat (D.unit db + 1)) in *.
      set (widthN := N.of_nat (cost_width db + 1)) in *.
      set (selectedN := N.of_nat (length (best cs db) + 1)) in *.
      set (best_clock := T_best cs db) in *.
      clearbody rowsN arityN unitN widthN selectedN best_clock. lia.
    - apply N.ltb_ge in Hallocated.
      pose proof (allocated_root_unit db c Hallocated) as Hroot.
      pose proof (D.T_find_le c db Hwf Hallocated) as Hfind_raw.
      assert (Hfind : (D.T_find c db <= D.c_db * N.of_nat (D.unit db + 1))%N).
      { eapply N.le_trans; [exact Hfind_raw |]. apply N.mul_le_mono_l. lia. }
      set (checker := ((256 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1) *
        N.of_nat (R db + 1) * N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N).
      assert (Hcheck : (T_check_dag db c (extraction_certificate (best cs db)) <= checker)%N).
      { apply best_certificate_clock; assumption. }
      assert (Hentry_width : forall i n ch, In (i, (n, ch)) (best cs db) ->
        Pos.size_nat i <= D.unit db).
      { intros i n [f k] Hin.
        pose proof (proj1 (best_row cs db i n f k Hwf Hcanonical Hinventory Hin)) as Hrow.
        pose proof (stored_cell_unit db f k (Some (Id i)) (Id i) Hwf Hrow
          ltac:(apply in_or_app; right; now left)) as Hwidth.
        cbn [cell_bits Pos.size_nat] in Hwidth. lia. }
      pose proof (best_certificate_check_width cs db c Hwf Hcanonical Hinventory) as Hwidth.
      pose proof (T_extraction_candidate_le V.t (check_dag db)
        (fun root g => T_check_dag db root g) c (fst (D.find c db)) (best cs db)
        (D.unit db) (cost_width db) checker Hentry_width Hcheck Hwidth) as Hcandidate.
      unfold c_ex. unfold checker in Hcandidate.
      clear - Hids Hguard Hfind Hcandidate Hbudget.
      set (rowsN := N.of_nat (R db + 1)) in *.
      set (arityN := N.of_nat (a db + 1)) in *.
      set (unitN := N.of_nat (D.unit db + 1)) in *.
      set (widthN := N.of_nat (cost_width db + 1)) in *.
      set (selectedN := N.of_nat (length (best cs db) + 1)) in *.
      set (best_clock := T_best cs db) in *.
      clearbody rowsN arityN unitN widthN selectedN best_clock. lia.
  Qed.

  Definition state := extraction_state V.t D.t Q.t.
  (** Internal credit pays suspended row work and the queue's stale-entry potential. *)
  Definition extraction_potential (db : D.t) (s : state) : N :=
    ResourceClocks.search_potential (R db) (D.unit db + cost_width db) s.

  Definition initial (cs : list (positive * (N * nat))) (db : D.t) : state :=
    search_initial db (inventory_rows (fun slot => D.index slot false db)
      I.child I.children I.root cs).
  Definition step (_ : list (positive * (N * nat))) (_ : D.t) (s : state)
      : state + extraction_best V.t := search_step s.
  Definition finalised (s : state) : extraction_best V.t := search_finalised s.
  (** Specification row numbers encode full source rows and never enter the runtime queue. *)
  Definition counter (s : state) (number : positive) : nat := extraction_row_counter s number.
  Definition children (_ : D.t) (number : positive) : list positive :=
    extraction_row_children number.
  Definition ready (s : state) : list (positive * N) :=
    extraction_ready_rows V.encode C.fn_cost C.val_cost s.
  Definition heap_potential (s : state) : N :=
    extraction_potential (search_database s) s.
  TimeFun initial.
  TimeFun step.
  TimeFun finalised.
  TimeFun counter.
  TimeFun children.
  TimeFun ready.
  Definition k_step : N :=
    (256 * 1024) * (PTrieT.c_trie + I.c_ix + D.c_db + C.c_cost + Q.c_pq + 1).
  (** The public step adds one wrapper call to the generic derived search-step clock. *)
  Lemma extraction_step_clock : forall cs db s,
    T_step cs db s = (1 + ResourceClocks.T_search_step s)%N.
  Proof.
    intros cs db s. time_unfold @T_step. time_simpl. reflexivity.
  Qed.

  (** A queue step and its wrapper fit the public arity, logarithm and width allowance. *)
  Lemma extraction_step_allowance : forall db,
    (1 + 64 * (PTrieT.c_trie + Q.c_pq + 1) *
      N.of_nat (Q.unit_pq (R db) (D.unit db + cost_width db)) <=
      k_step * N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N.
  Proof.
    intro db.
    assert (Hwidth : Q.unit_pq (R db) (D.unit db + cost_width db) <=
      (a db + Nat.log2 (R db) + 2) * (D.unit db + 1) * (cost_width db + 1)).
    { unfold Q.unit_pq.
      replace ((a db + Nat.log2 (R db) + 2) * (D.unit db + 1) * (cost_width db + 1)) with
        ((a db + Nat.log2 (R db) + 2) * ((D.unit db + 1) * (cost_width db + 1))) by ring.
      apply Nat.mul_le_mono; [lia |nia]. }
    unfold k_step.
    replace ((256 * 1024) *
      (PTrieT.c_trie + I.c_ix + D.c_db + C.c_cost + Q.c_pq + 1) *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N with
      ((256 * 1024) * (PTrieT.c_trie + I.c_ix + D.c_db + C.c_cost + Q.c_pq + 1) *
        (N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
          N.of_nat (cost_width db + 1)))%N by ring.
    apply extraction_step_fee_budget.
    - change (1 * 1 * 1 <= N.of_nat (a db + Nat.log2 (R db) + 2) *
        N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
      apply N.mul_le_mono; [apply N.mul_le_mono; lia |lia].
    - rewrite <- !Nat2N.inj_mul. lia.
  Qed.

  Definition reachable (sl : list (positive * (N * nat))) (db : D.t) (s : state) : Prop :=
    clos_refl_trans state (fun a b => step sl db a = inl b) (initial sl db) s.
  Definition knuth_inv (db : D.t) (s : state) : Prop :=
    forall c n ch, In (c, (n, ch)) (finalised s) ->
      forall e, represents (D.view db) (Id c) e -> (n <= tree_cost e)%N.
  Module Resources := SearchResources V C Q.

  (** Every continuing state keeps its database, constructor source and cached source count. *)
  Lemma reachable_source : forall cs db s, reachable cs db s ->
    search_database s = db /\ search_rows s = Enumeration.enumerated_rows cs db /\
      search_row_count s = length (Enumeration.enumerated_rows cs db).
  Proof.
    intros cs db s Hreach.
    assert (Hboth : SearchProof.search_invariant (Enumeration.enumerated_rows cs db) s /\
      (search_database s = db /\ search_rows s = Enumeration.enumerated_rows cs db /\
        search_row_count s = length (Enumeration.enumerated_rows cs db))).
    { eapply (extraction_reachable_invariant (step cs db)
        (fun state => SearchProof.search_invariant (Enumeration.enumerated_rows cs db) state /\
          (search_database state = db /\ search_rows state = Enumeration.enumerated_rows cs db /\
            search_row_count state = length (Enumeration.enumerated_rows cs db)))).
      - intros before after [Hinv [Hdb [Hrows Hcount]]] Hstep. split.
        + eapply SearchProof.search_step_invariant; eassumption.
        + destruct (SearchProof.search_step_source D.t (Enumeration.enumerated_rows cs db)
            before after Hinv Hstep) as [Hdb' [Hrows' Hcount']].
          now rewrite Hdb', Hrows', Hcount'.
      - exact Hreach.
      - split; [apply SearchProof.search_initial_invariant|].
        destruct (SearchProof.search_initial_fields D.t db (Enumeration.enumerated_rows cs db))
          as [Hdb [Hrows [Hcount Hrest]]].
        split; [exact Hdb|]. split; assumption. }
    exact (proj2 Hboth).
  Qed.


  Lemma F1_initial : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    finalised (initial cs db) = [] /\ knuth_inv db (initial cs db).
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    destruct (SearchProof.search_initial_fields D.t db
      (inventory_rows (fun slot => D.index slot false db) I.child I.children I.root cs))
      as [_ [_ [_ [_ Hfinals]]]].
    assert (Hempty : finalised (initial cs db) = []) by exact Hfinals.
    split; [exact Hempty|]. unfold knuth_inv. rewrite Hempty.
    intros c n ch Hin. contradiction.
  Qed.

  Lemma F2_counter_spec : forall cs db s c, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s ->
    counter s c = length (filter
      (fun i => negb (existsb (fun entry => Pos.eqb i (fst entry)) (finalised s)))
      (children db c)).
  Proof. intros cs db s c Hwf Hcanonical Hinventory Hreach. reflexivity. Qed.

  Lemma F3_ready : forall cs db s c n, reachable cs db s ->
    In (c, n) (ready s) -> counter s c = 0.
  Proof.
    intros cs db s c n Hreach Hin.
    exact (extraction_ready_rows_counter V.t D.t Q.t V.encode C.fn_cost C.val_cost s c n Hin).
  Qed.

  (** Every continuing reachable state retains queue coverage and attained optimal finals. *)
  Lemma reachable_verified : forall cs db s, reachable cs db s ->
    Correct.search_verified (Enumeration.enumerated_rows cs db) s.
  Proof.
    intros cs db s Hreach. unfold reachable in Hreach.
    eapply (extraction_reachable_invariant (step cs db)
      (Correct.search_verified (Enumeration.enumerated_rows cs db))).
    - intros before after Hverified Hstep.
      eapply Correct.search_verified_step; [exact Hverified|exact Hstep|].
      eapply SearchProof.search_step_invariant; [exact (proj1 Hverified)|exact Hstep].
    - exact Hreach.
    - apply Correct.search_verified_initial. apply SearchProof.search_initial_invariant.
  Qed.

  (** Canonical stored outputs turn exact-row optimality into the public database invariant. *)
  Lemma verified_knuth : forall cs db s, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    Correct.search_verified (Enumeration.enumerated_rows cs db) s -> knuth_inv db s.
  Proof.
    intros cs db s Hwf Hcanonical Hinventory [_ [Hfinals Hoptimal]] c n [f k] Hin e Hrep.
    change (In (c, (n, (f, k))) (search_finalised s)) in Hin.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    destruct (Finals.finalised_row (Enumeration.enumerated_rows cs db)
      (search_final_costs s) (search_finalised s) c n f k Hfinals Hin) as [Hsource Hcost].
    pose proof (proj1 (Hrows f k c) Hsource) as Hrow.
    assert (Hfixed : D.repr db c = c).
    { apply (Hcanonical f k (Some (Id c)) Hrow c).
      apply in_or_app. right. now left. }
    pose proof (DatabaseTrees.database_search_represents db (Enumeration.enumerated_rows cs db)
      Hwf Hcanonical (fun g key i Hstored => proj2 (Hrows g key i) Hstored)
      (Id c) e Hrep) as Hexact.
    change (search_represents (Enumeration.enumerated_rows cs db) (Id (D.repr db c)) e)
      in Hexact. rewrite Hfixed in Hexact.
    apply (Hoptimal c n); [|exact Hexact].
    apply (proj2 (Finals.finalised_lookup_spec (Enumeration.enumerated_rows cs db)
      (search_final_costs s) (search_finalised s) c n Hfinals)).
    exists (f, k). exact Hin.
  Qed.

  Lemma F4_pop_final : forall cs db s s', D.wf db -> D.canonical db -> ctor_inventory cs db ->
    reachable cs db s -> knuth_inv db s -> step cs db s = inl s' -> knuth_inv db s'.
  Proof.
    intros cs db s next Hwf Hcanonical Hinventory Hreach Hknuth Hstep.
    apply (verified_knuth cs db next Hwf Hcanonical Hinventory), reachable_verified.
    unfold reachable in *. eapply rt_trans; [exact Hreach|].
    now apply rt_step.
  Qed.

  Lemma F5_finalised_attained : forall cs db s c n ch, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s -> In (c, (n, ch)) (finalised s) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof.
    intros cs db s c n ch Hwf Hcanonical Hinventory Hreach Hin.
    destruct (reachable_verified cs db s Hreach) as [_ [Hfinals Hoptimal]].
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    destruct (Finals.finalised_attained (Enumeration.enumerated_rows cs db)
      (search_final_costs s) (search_finalised s) Hfinals c n ch Hin) as [e [Hrep Hcost]].
    exists e. split; [|exact Hcost].
    exact (DatabaseTrees.search_database_represents db (Enumeration.enumerated_rows cs db)
      Hwf (fun f k i Hstored => proj1 (Hrows f k i) Hstored) (Id c) e Hrep).
  Qed.

  Lemma F6_best_loop : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    loop_fuel (step cs db) (R db + 1) (initial cs db) = inr (best cs db).
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    destruct (Correct.best_rows_correct D.t db (Enumeration.enumerated_rows cs db)
      (SearchProof.search_initial_invariant D.t db (Enumeration.enumerated_rows cs db))
      (SearchProof.search_step_invariant D.t (Enumeration.enumerated_rows cs db))) as [Hrun _].
    rewrite <- (inventory_rows_count cs db Hwf Hinventory). exact Hrun.
  Qed.
  (** Every cost already finalized by a reachable state is the eventual selected optimum. *)
  Lemma reachable_cost_selected : forall cs db s i n, reachable cs db s ->
    trie_get i (search_final_costs s) = Some n ->
    exists ch, In (i, (n, ch)) (best cs db).
  Proof.
    intros cs db s i n Hreach Hget.
    destruct (reachable_verified cs db s Hreach) as [_ [Hcurrent Hcurrent_opt]].
    destruct (best_result cs db) as [costs [Hbest [Hbest_opt Hcomplete]]].
    destruct (proj2 (proj2 Hcurrent) i n Hget) as [tree [Htree Hcost]].
    destruct (Hcomplete i tree Htree) as [m [ch Hin]].
    assert (Hbest_get : trie_get i costs = Some m).
    { apply (proj2 (Finals.finalised_lookup_spec (Enumeration.enumerated_rows cs db)
        costs (best cs db) i m Hbest)). exists ch. exact Hin. }
    destruct (proj2 (proj2 Hbest) i m Hbest_get) as [other [Hother Hother_cost]].
    assert (Hequal : n = m).
    { apply N.le_antisymm.
      - rewrite <- Hother_cost. exact (Hcurrent_opt i n Hget other Hother).
      - rewrite <- Hcost. exact (Hbest_opt i m Hbest_get tree Htree). }
    exists ch. rewrite Hequal. exact Hin.
  Qed.

  (** The public chosen-cost observation agrees with every reachable final-trie binding. *)
  Lemma reachable_cost_value : forall cs db s i n, reachable cs db s ->
    trie_get i (search_final_costs s) = Some n -> cost_of (best cs db) (Id i) = n.
  Proof.
    intros cs db s i n Hreach Hget.
    destruct (reachable_cost_selected cs db s i n Hreach Hget) as [ch Hin].
    destruct (best_result cs db) as [costs [Hbest Hrest]].
    assert (Hbest_get : trie_get i costs = Some n).
    { apply (proj2 (Finals.finalised_lookup_spec (Enumeration.enumerated_rows cs db)
        costs (best cs db) i n Hbest)). exists ch. exact Hin. }
    unfold cost_of. rewrite chosen_cost_extraction_lookup,
      (Finals.finalised_lookup_agrees costs (best cs db) (proj1 Hbest) i), Hbest_get.
    reflexivity.
  Qed.

  (** A ready key keeps its current final costs in the complete optimal result. *)
  Lemma reachable_key_costs : forall cs db s k, reachable cs db s ->
    Semantics.search_known (search_final_costs s) k ->
    dag_cost_cells C.val_cost (search_final_costs s) k = map (cost_of (best cs db)) k.
  Proof.
    intros cs db s k Hreach Hknown. rewrite dag_cost_cells_map.
    apply map_ext_in. intros [i|v] Hin.
    - destruct (Hknown i Hin) as [n Hget]. unfold dag_get_cost. rewrite Hget.
      symmetry. exact (reachable_cost_value cs db s i n Hreach Hget).
    - unfold cost_of. destruct (best cs db); reflexivity.
  Qed.

  (** Every reachable final cost fits the exact constructor-cost width. *)
  Lemma reachable_cost_width : forall cs db s i n, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s ->
    trie_get i (search_final_costs s) = Some n -> N.size_nat n <= cost_width db.
  Proof.
    intros cs db s i n Hwf Hcanonical Hinventory Hreach Hget.
    destruct (reachable_cost_selected cs db s i n Hreach Hget) as [[f k] Hin].
    destruct (best_row cs db i n f k Hwf Hcanonical Hinventory Hin) as [Hrow Hcost].
    rewrite Hcost. exact (proj1 (cost_width_spec cs db Hwf Hcanonical Hinventory) f k i Hrow).
  Qed.

  (** A ready original row supplies an entry within the combined identifier/cost queue width. *)
  Lemma reachable_row_width : forall cs db s f k i, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s ->
    In (f, k, i) (Enumeration.enumerated_rows cs db) ->
    Semantics.search_known (search_final_costs s) k ->
    Pos.size_nat i + N.size_nat (C.fn_cost f (dag_cost_cells C.val_cost (search_final_costs s) k))
      <= D.unit db + cost_width db.
  Proof.
    intros cs db s f k i Hwf Hcanonical Hinventory Hreach Hsource Hknown.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    pose proof (proj1 (Hrows f k i) Hsource) as Hrow.
    assert (Hid : Pos.size_nat i <= D.unit db).
    { pose proof (stored_cell_unit db f k (Some (Id i)) (Id i) Hwf Hrow
        ltac:(apply in_or_app; right; now left)) as Hwidth.
      cbn [cell_bits Pos.size_nat] in Hwidth. lia. }
    rewrite (reachable_key_costs cs db s k Hreach Hknown).
    pose proof (proj1 (cost_width_spec cs db Hwf Hcanonical Hinventory) f k i Hrow) as Hcost.
    lia.
  Qed.

  (** The queue's pending entries never exceed the exact constructor-row count. *)
  Lemma reachable_queue_pending : forall cs db s, D.wf db -> ctor_inventory cs db ->
    reachable cs db s -> Q.pending (search_queue s) <= R db.
  Proof.
    intros cs db s Hwf Hinventory Hreach.
    rewrite <- (inventory_rows_count cs db Hwf Hinventory).
    exact (Resources.search_reachable_pending D.t db (Enumeration.enumerated_rows cs db) s Hreach).
  Qed.

  (** The full parked-frame and pending-queue ledger remains within the constructor count. *)
  Lemma reachable_search_load : forall cs db s, D.wf db -> ctor_inventory cs db ->
    reachable cs db s -> Resources.search_load s <= R db.
  Proof.
    intros cs db s Hwf Hinventory Hreach.
    rewrite <- (inventory_rows_count cs db Hwf Hinventory).
    destruct (Resources.search_load_preserved D.t (Enumeration.enumerated_rows cs db)
      (initial cs db) s Hreach
      (SearchProof.search_initial_invariant D.t db (Enumeration.enumerated_rows cs db)))
      as [Hinv Hload].
    eapply Nat.le_trans; [exact Hload|].
    exact (Resources.search_initial_load D.t db (Enumeration.enumerated_rows cs db)).
  Qed.

  (** Reachable queue entries obey the combined stored-identifier and optimal-cost width. *)
  Lemma reachable_queue_fits : forall cs db s, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s ->
    Q.fits (D.unit db + cost_width db) (search_queue s).
  Proof.
    intros cs db s Hwf Hcanonical Hinventory Hreach.
    assert (Hboth : reachable cs db s /\ Q.fits (D.unit db + cost_width db) (search_queue s)).
    { eapply (extraction_reachable_invariant (step cs db)
        (fun state => reachable cs db state /\
          Q.fits (D.unit db + cost_width db) (search_queue state))).
      - intros before after [Hbefore Hfits] Hstep.
        assert (Hafter : reachable cs db after).
        { unfold reachable in *. eapply rt_trans; [exact Hbefore|]. now apply rt_step. }
        split; [exact Hafter|].
        pose proof (proj1 (reachable_verified cs db before Hbefore)) as Hinv.
        destruct (SearchProof.search_step_cases D.t (Enumeration.enumerated_rows cs db)
          before after Hinv Hstep) as [i [n [f [k [queue [Hpop [Hcandidate Hfinish]]]]]]].
        assert (Hcosts : search_final_costs after = PTrieCode.set i n (search_final_costs before)).
        { rewrite Hfinish.
          destruct (SearchProof.search_finish_fields D.t i n (f, k) queue before)
            as [_ [_ [_ [Hcosts _]]]]. exact Hcosts. }
        rewrite Hfinish. eapply Resources.search_finish_fits.
        + exact Hinv.
        + exact Hfits.
        + exact Hpop.
        + exact Hcandidate.
        + intros g key j Hsource Hknown.
          pose proof (reachable_row_width cs db after g key j Hwf Hcanonical Hinventory
            Hafter Hsource) as Hwidth. rewrite Hcosts in Hwidth. now apply Hwidth.
      - exact Hreach.
      - assert (Hinitial : reachable cs db (initial cs db)).
        { unfold reachable. apply rt_refl. }
        split; [exact Hinitial|]. apply Resources.search_initial_fits.
        assert (Hcosts : search_final_costs (initial cs db) = Empty).
        { destruct (SearchProof.search_initial_fields D.t db (Enumeration.enumerated_rows cs db))
            as [_ [_ [_ [Hcosts _]]]]. exact Hcosts. }
        intros f k i Hsource Hknown.
        pose proof (reachable_row_width cs db (initial cs db) f k i Hwf Hcanonical Hinventory
          Hinitial Hsource) as Hwidth. rewrite Hcosts in Hwidth. now apply Hwidth. }
    exact (proj2 Hboth).
  Qed.

  Module EnumerationTime := EnumeratedRowsT V I D.

  (** Source output identifiers and key cells fit the database's spending unit. *)
  Lemma inventory_source_syntax : forall cs db f k i, D.wf db -> ctor_inventory cs db ->
    In (f, k, i) (Enumeration.enumerated_rows cs db) ->
    Pos.size_nat i <= D.unit db /\
    (forall j, In (Id j) k -> Pos.size_nat j <= D.unit db) /\
    (forall v, In (Val v) k -> V.bits v <= D.unit db).
  Proof.
    intros cs db f k i Hwf Hinventory Hsource.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    pose proof (proj1 (Hrows f k i) Hsource) as Hrow.
    assert (Hcell : forall item, In item (k ++ [Id i]) -> cell_bits V.encode item <= D.unit db).
    { intros item Hin. exact (stored_cell_unit db f k (Some (Id i)) item Hwf Hrow Hin). }
    split.
    - pose proof (Hcell (Id i) ltac:(apply in_or_app; right; now left)) as Hwidth.
      cbn [cell_bits Pos.size_nat] in Hwidth. lia.
    - split.
      + intros j Hin. pose proof (Hcell (Id j) ltac:(apply in_or_app; now left)) as Hwidth.
        cbn [cell_bits Pos.size_nat] in Hwidth. lia.
      + intros v Hin. pose proof (Hcell (Val v) ltac:(apply in_or_app; now left)) as Hwidth.
        unfold V.bits. cbn [cell_bits Pos.size_nat] in Hwidth. lia.
  Qed.

  (** Registered source syntax fits the fixed combined identifier and cost width. *)
  Lemma inventory_source_width : forall cs db, D.wf db -> ctor_inventory cs db ->
    ResourceClocks.search_syntax_width (Enumeration.enumerated_rows cs db)
      (D.unit db + cost_width db).
  Proof.
    intros cs db Hwf Hinventory f k i Hsource.
    destruct (inventory_source_syntax cs db f k i Hwf Hinventory Hsource)
      as [Houtput [Hids Hvalues]].
    split; [lia |]. split.
    - intros j Hin. pose proof (Hids j Hin). lia.
    - intros v Hin. pose proof (Hvalues v Hin). lia.
  Qed.

  (** Every registered source row uses at most the public maximum constructor arity. *)
  Lemma inventory_source_arity : forall cs db, D.wf db -> ctor_inventory cs db ->
    forall f k i, In (f, k, i) (Enumeration.enumerated_rows cs db) -> length k <= a db.
  Proof.
    intros cs db Hwf Hinventory f k i Hsource.
    destruct (inventory_rows_spec cs db Hwf Hinventory) as [_ [Hrows _]].
    exact (proj1 (a_spec cs db Hwf Hinventory) f k i (proj1 (Hrows f k i) Hsource)).
  Qed.

  (** Rows ready before any finalization fit the combined identifier and optimal-cost width. *)
  Lemma initial_rows_width : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    Resources.search_rows_width (Enumeration.enumerated_rows cs db) Empty
      (D.unit db + cost_width db).
  Proof.
    intros cs db Hwf Hcanonical Hinventory f k i Hsource Hknown.
    assert (Hreach : reachable cs db (initial cs db)) by (unfold reachable; apply rt_refl).
    assert (Hcosts : search_final_costs (initial cs db) = Empty).
    { destruct (SearchProof.search_initial_fields D.t db (Enumeration.enumerated_rows cs db))
        as [_ [_ [_ [Hcosts _]]]]. exact Hcosts. }
    pose proof (reachable_row_width cs db (initial cs db) f k i Hwf Hcanonical Hinventory
      Hreach Hsource) as Hwidth. rewrite Hcosts in Hwidth. now apply Hwidth.
  Qed.

  (** Initialization's inventory phase has an additive syntax and constructor-row budget. *)
  Lemma initial_inventory_clock : forall cs db, D.wf db -> ctor_inventory cs db ->
    (T_inventory_rows (fun slot => D.index slot false db)
      (fun slot => (1 + D.T_index slot false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root cs <=
      1024 * (I.c_ix + D.c_db + 1) *
        N.of_nat (inventory_bits cs + (a db + 1) * R db + 1) *
        N.of_nat (D.unit db + 1))%N.
  Proof.
    intros cs db Hwf Hinventory.
    eapply EnumerationTime.inventory_rows_clock_bounded.
    - exact Hwf.
    - exact (proj2 (proj2 (proj2 Hinventory))).
    - exact (proj1 (a_spec cs db Hwf Hinventory)).
    - change (length (Enumeration.enumerated_rows cs db) <= R db).
      rewrite (inventory_rows_count cs db Hwf Hinventory). lia.
  Qed.

  (** An initial registration allowance composes with the checked inventory walk. *)
  Lemma initial_credit_composition : forall cs db credit,
    D.wf db -> ctor_inventory cs db ->
    (T_search_initial db (Enumeration.enumerated_rows cs db) + credit <=
      N.of_nat (R db) *
        (512 * (PTrieT.c_trie + C.c_cost + 1) *
          N.of_nat (D.unit db + cost_width db + 1) * N.of_nat (2 * a db + 1) +
         Q.c_pq * N.of_nat (Q.unit_pq (R db) (D.unit db + cost_width db))) +
      512 * (PTrieT.c_trie + C.c_cost + 1) *
        N.of_nat (D.unit db + cost_width db + 1) * N.of_nat (R db) +
      16 * N.of_nat (R db + 1))%N ->
    (T_initial cs db + credit <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db credit Hwf Hinventory Hregistration.
    pose proof (initial_inventory_clock cs db Hwf Hinventory) as Hwalk.
    set (rows := Enumeration.enumerated_rows cs db) in *.
    set (walk := T_inventory_rows (fun slot => D.index slot false db)
      (fun slot => (1 + D.T_index slot false db)%N) I.child I.T_child I.children I.T_children
      I.root I.T_root cs) in *.
    set (registration := T_search_initial db rows) in *.
    change (1 + (walk + registration) + credit <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
    unfold Q.unit_pq in Hregistration. unfold k_step.
    set (syntax := inventory_bits cs) in *.
    set (count := R db) in *.
    set (arity := a db) in *.
    set (depth := Nat.log2 count) in *.
    set (unit := D.unit db) in *.
    set (width := cost_width db) in *.
    clearbody syntax count arity depth unit width.
    assert (Hcombined : (N.of_nat (unit + width + 1) <=
      N.of_nat (unit + 1) * N.of_nat (width + 1))%N).
    { rewrite <- Nat2N.inj_mul.
      pose proof (extraction_initial_width unit width) as Hwidth. lia. }
    pose proof (extraction_initial_budget PTrieT.c_trie I.c_ix D.c_db C.c_cost Q.c_pq
      (N.of_nat syntax) (N.of_nat count) (N.of_nat arity) (N.of_nat depth)
      (N.of_nat (unit + 1)) (N.of_nat (width + 1))
      (N.of_nat (unit + width + 1)) ltac:(lia) ltac:(lia) Hcombined) as Hbudget.
    repeat first [rewrite Nat2N.inj_add in Hwalk |rewrite Nat2N.inj_mul in Hwalk].
    repeat first [rewrite Nat2N.inj_add in Hregistration |rewrite Nat2N.inj_mul in Hregistration].
    repeat first [rewrite Nat2N.inj_add in Hbudget |rewrite Nat2N.inj_mul in Hbudget].
    repeat first [rewrite Nat2N.inj_add |rewrite Nat2N.inj_mul].
    cbn [N.of_nat] in Hwalk, Hregistration, Hbudget |- *.
    eapply N.le_trans; [|exact Hbudget]. clear - Hwalk Hregistration. lia.
  Qed.

  (** Initial registration funds all stored frame and heap credit from its source rows. *)
  Lemma initial_registration_potential : forall cs db,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_search_initial db (Enumeration.enumerated_rows cs db) +
      extraction_potential db (initial cs db) <=
      N.of_nat (R db) *
        (512 * (PTrieT.c_trie + C.c_cost + 1) *
          N.of_nat (D.unit db + cost_width db + 1) * N.of_nat (2 * a db + 1) +
         Q.c_pq * N.of_nat (Q.unit_pq (R db) (D.unit db + cost_width db))) +
      512 * (PTrieT.c_trie + C.c_cost + 1) *
        N.of_nat (D.unit db + cost_width db + 1) * N.of_nat (R db) +
      16 * N.of_nat (R db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    set (rs := Enumeration.enumerated_rows cs db).
    set (w := D.unit db + cost_width db).
    pose proof (ResourceClocks.T_search_initial_amort D.t db rs w
      (inventory_source_width cs db Hwf Hinventory)
      (initial_rows_width cs db Hwf Hcanonical Hinventory)) as Hregistered.
    assert (Harity : forall row, In row rs -> length (snd (fst row)) <= a db).
    { intros [[f k] i] Hin. exact (inventory_source_arity cs db Hwf Hinventory f k i Hin). }
    pose proof (ResourceClocks.search_initial_credit_bound rs (length rs) w (a db) Harity)
      as Hframes.
    pose proof (inventory_rows_count cs db Hwf Hinventory) as Hcount. fold rs in Hcount.
    unfold search_row in Hregistered, Hframes.
    rewrite Hcount in Hregistered, Hframes.
    assert (Hwork : ResourceClocks.search_work_unit w =
      (512 * (PTrieT.c_trie + C.c_cost + 1) * N.of_nat (w + 1))%N).
    { unfold ResourceClocks.search_work_unit, ResourceClocks.search_cell_unit. ring. }
    rewrite Hwork in Hregistered, Hframes.
    unfold ResourceClocks.search_push_unit in Hframes.
    change (T_search_initial db rs + extraction_potential db (initial cs db) <=
      ResourceClocks.search_frames_credit (R db) w (map search_new_frame rs) +
      512 * (PTrieT.c_trie + C.c_cost + 1) * N.of_nat (w + 1) * N.of_nat (R db) +
      16 * N.of_nat (R db + 1))%N in Hregistered.
    eapply N.le_trans; [exact Hregistered |].
    apply N.add_le_mono_r, N.add_le_mono_r. exact Hframes.
  Qed.

  (** Initialization pays the exact inventory walk and its genuine suspended-work potential. *)
  Lemma T_initial_potential : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_initial cs db + extraction_potential db (initial cs db) <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory. apply initial_credit_composition;
      [exact Hwf |exact Hinventory |].
    exact (initial_registration_potential cs db Hwf Hcanonical Hinventory).
  Qed.



  (** Every continuing reachable step spends the internal credit at the public row allowance. *)
  Lemma extraction_step_amort : forall cs db s next,
    D.wf db -> D.canonical db -> ctor_inventory cs db -> reachable cs db s ->
    step cs db s = inl next ->
    (T_step cs db s + extraction_potential db next <= extraction_potential db s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db s next Hwf Hcanonical Hinventory Hreachable Hstep.
    assert (Hnext : reachable cs db next).
    { unfold reachable in *. eapply rt_trans; [exact Hreachable |]. now apply rt_step. }
    assert (Hgeneric : (ResourceClocks.T_search_step s +
      ResourceClocks.search_potential (R db) (D.unit db + cost_width db) next <=
      ResourceClocks.search_potential (R db) (D.unit db + cost_width db) s +
      64 * (PTrieT.c_trie + Q.c_pq + 1) *
        N.of_nat (Q.unit_pq (R db) (D.unit db + cost_width db)))%N).
    { apply (ResourceClocks.T_search_step_amort D.t (Enumeration.enumerated_rows cs db)
        (R db) (D.unit db + cost_width db) s next).
      - exact (proj1 (reachable_verified cs db s Hreachable)).
      - now apply inventory_source_width.
      - now apply reachable_queue_fits with cs.
      - now apply reachable_search_load with cs.
      - intros f k i Hsource Hknown.
        exact (reachable_row_width cs db next f k i Hwf Hcanonical Hinventory
          Hnext Hsource Hknown).
      - exact Hstep. }
    pose proof (extraction_step_allowance db) as Hallowance.
    unfold extraction_potential. rewrite extraction_step_clock.
    clear - Hgeneric Hallowance. lia.
  Qed.



  (** A stopping search reads cached queue size and returns the stored table. *)
  Lemma T_step_stopped_le : forall cs db s out, step cs db s = inr out ->
    (T_step cs db s <= Q.c_pq + 4)%N.
  Proof.
    intros cs db s out Hstop. unfold step, search_step in Hstop.
    destruct (Q.size (search_queue s)) as [|size] eqn:Hsize.
    - pose proof (Q.T_size_le (search_queue s)) as Hclock.
      time_unfold @T_step. time_simpl. time_cbn.
      time_unfold @T_search_step. time_simpl. time_cbn.
      rewrite Hsize. lia.
    - destruct (Q.pop (search_queue s)) as [[[n i] queue]|]; [|discriminate].
      destruct (trie_get i (search_candidates s)) as [[value row]|];
        destruct (trie_get i (search_final_costs s)); discriminate.
  Qed.

  Lemma T1b_step_stop : forall cs db s out, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s -> step cs db s = inr out ->
    (T_step cs db s <= k_step * N.of_nat (R db + 1))%N.
  Proof.
    intros cs db s out Hwf Hcanonical Hinventory Hreachable Hstop.
    pose proof (T_step_stopped_le cs db s out Hstop) as Hclock.
    assert (Hconstant : (Q.c_pq + 4 <= k_step)%N) by (unfold k_step; nia).
    eapply N.le_trans; [exact Hclock |].
    eapply N.le_trans; [exact Hconstant |].
    rewrite <- (N.mul_1_r k_step) at 1. apply N.mul_le_mono_l. lia.
  Qed.

  (** The bounded extraction loop charges its initialization, steps and fuel. *)
  Lemma T2_best_loop : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_best cs db <= T_initial cs db +
      T_loop_fuel (step cs db) (T_step cs db) (R db + 1) (initial cs db) +
      k_step * N.of_nat (R db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    pose proof (inventory_rows_count cs db Hwf Hinventory) as Hlength.
    destruct (SearchProof.search_initial_fields D.t db
      (inventory_rows (fun slot => D.index slot false db) I.child I.children I.root cs))
      as [_ [_ [Hcount _]]].
    assert (Hcount' : search_row_count (initial cs db) = R db).
    { transitivity (length (Enumeration.enumerated_rows cs db));
        [exact Hcount |exact Hlength]. }
    assert (Hfuel : S (search_row_count (initial cs db)) = R db + 1) by lia.
    assert (Hloop : (T_loop_fuel (search_step (DB := D.t))
      (T_search_step (DB := D.t)) (R db + 1) (initial cs db) <=
      T_loop_fuel (step cs db) (T_step cs db) (R db + 1) (initial cs db))%N).
    { unfold step. apply extraction_loop_clock_mono. intro s.
      time_unfold @T_step. time_simpl. time_cbn. lia. }
    assert (Hconstant : (3 <= k_step)%N) by (unfold k_step; nia).
    assert (Hallowance : (3 <= k_step * N.of_nat (R db + 1))%N).
    { eapply N.le_trans; [exact Hconstant |].
      rewrite <- (N.mul_1_r k_step) at 1. apply N.mul_le_mono_l. lia. }
    time_unfold @T_best. time_simpl. time_cbn.
    time_unfold @T_initial. time_simpl. time_cbn.
    time_unfold @T_best_rows. time_simpl. time_cbn.
    fold (initial cs db).
    change (fun H : extraction_state V.t D.t Q.t => T_search_step H)
      with (T_search_step (DB := D.t)).
    rewrite Hfuel.
    destruct (search_step (initial cs db)) as [next|out];
      [destruct (loop_fuel (search_step (DB := D.t))
        (search_row_count (initial cs db)) next)|]; lia.
  Qed.

  (** Any valid initialization and continuing-step potential bounds pay for the full search. *)
  Lemma T_best_potential_bound : forall cs db (potential : state -> N),
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_initial cs db + potential (initial cs db) <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N ->
    (forall s next, reachable cs db s -> step cs db s = inl next ->
      (T_step cs db s + potential next <= potential s + k_step *
        N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N) ->
    (T_best cs db <= c_ex *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + 1) +
        (R db + 1) * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db potential Hwf Hcanonical Hinventory Hinitial Hstep.
    assert (Hadvance : forall s next, reachable cs db s -> step cs db s = inl next ->
      reachable cs db next /\
      (T_step cs db s + potential next <= potential s + k_step *
        N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N).
    { intros s next Hreach Hrun. split.
      - unfold reachable in *. eapply rt_trans; [exact Hreach|]. now apply rt_step.
      - exact (Hstep s next Hreach Hrun). }
    assert (Hstop : forall s out, reachable cs db s -> step cs db s = inr out ->
      (T_step cs db s <= k_step * N.of_nat (R db + 1))%N).
    { intros s out Hreach Hrun.
      exact (T1b_step_stop cs db s out Hwf Hcanonical Hinventory Hreach Hrun). }
    assert (Hstart : reachable cs db (initial cs db)).
    { unfold reachable. apply rt_refl. }
    pose proof (extraction_loop_clock_amort (step cs db) (T_step cs db)
      (reachable cs db) potential
      (k_step * N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
        N.of_nat (cost_width db + 1))%N
      (k_step * N.of_nat (R db + 1))%N Hadvance Hstop (R db + 1) (initial cs db) Hstart)
      as Hloop.
    pose proof (T2_best_loop cs db Hwf Hcanonical Hinventory) as Hdriver.
    assert (Hcoefficient : (1 <= k_step)%N) by (unfold k_step; nia).
    assert (Harity : N.of_nat (a db + Nat.log2 (R db) + 2) =
      (N.of_nat (a db) + N.of_nat (Nat.log2 (R db)) + 2)%N).
    { now rewrite !Nat2N.inj_add. }
    assert (Hbudget : N.of_nat (inventory_bits cs + (R db + 1) *
      (a db + Nat.log2 (R db) + 2)) =
      (N.of_nat (inventory_bits cs) + N.of_nat (R db + 1) *
        (N.of_nat (a db) + N.of_nat (Nat.log2 (R db)) + 2))%N).
    { rewrite Nat2N.inj_add, Nat2N.inj_mul, Harity. reflexivity. }
    rewrite Harity in Hloop. rewrite Hbudget in Hinitial.
    pose proof (extraction_best_budget (T_initial cs db)
      (T_loop_fuel (step cs db) (T_step cs db) (R db + 1) (initial cs db))
      (T_best cs db) (potential (initial cs db)) k_step (N.of_nat (inventory_bits cs))
      (N.of_nat (R db + 1)) (N.of_nat (a db)) (N.of_nat (Nat.log2 (R db)))
      (N.of_nat (D.unit db + 1)) (N.of_nat (cost_width db + 1))
      ltac:(lia) ltac:(lia) ltac:(lia) Hcoefficient Hinitial Hloop Hdriver) as Htotal.
    rewrite <- Hbudget in Htotal.
    assert (Hshape : inventory_bits cs + (R db + 1) * (a db + 1) +
      (R db + 1) * (Nat.log2 (R db) + 1) =
      inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) by ring.
    assert (Hconstant : c_ex = (4 * k_step)%N) by (unfold c_ex, k_step; ring).
    rewrite Hshape, Hconstant. exact Htotal.
  Qed.

  (** The state's immutable database supplies the fixed parameters of its internal credit. *)
  Definition extraction_observer_potential (s : state) : N :=
    extraction_potential (search_database s) s.

  (** The proposed specification observer gives initialization precisely its proved credit. *)
  Lemma T_initial_observer_potential : forall cs db,
    D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_initial cs db + extraction_observer_potential (initial cs db) <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    assert (Hreach : reachable cs db (initial cs db)).
    { unfold reachable. apply rt_refl. }
    unfold extraction_observer_potential.
    rewrite (proj1 (reachable_source cs db (initial cs db) Hreach)).
    exact (T_initial_potential cs db Hwf Hcanonical Hinventory).
  Qed.

  (** The proposed specification observer uses the same fixed credit parameters across a step. *)
  Lemma T_step_observer_potential : forall cs db s next,
    D.wf db -> D.canonical db -> ctor_inventory cs db -> reachable cs db s ->
    step cs db s = inl next ->
    (T_step cs db s + extraction_observer_potential next <= extraction_observer_potential s +
      k_step * N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db s next Hwf Hcanonical Hinventory Hreach Hstep.
    assert (Hnext : reachable cs db next).
    { unfold reachable in *. eapply rt_trans; [exact Hreach|]. now apply rt_step. }
    unfold extraction_observer_potential.
    rewrite (proj1 (reachable_source cs db s Hreach)), (proj1 (reachable_source cs db next Hnext)).
    exact (extraction_step_amort cs db s next Hwf Hcanonical Hinventory Hreach Hstep).
  Qed.

  Lemma T0_initial : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_initial cs db + heap_potential (initial cs db) <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    eapply N.le_trans; [|exact (T_initial_observer_potential cs db Hwf Hcanonical Hinventory)].
    unfold heap_potential, extraction_observer_potential. lia.
  Qed.

  Lemma T1_step_amort : forall cs db s s', D.wf db -> D.canonical db -> ctor_inventory cs db ->
    reachable cs db s -> knuth_inv db s ->
    step cs db s = inl s' ->
    (T_step cs db s + heap_potential s' <= heap_potential s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db s next Hwf Hcanonical Hinventory Hreach Hknuth Hstep.
    exact (T_step_observer_potential cs db s next Hwf Hcanonical Hinventory Hreach Hstep).
  Qed.

  Lemma T_best_le : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_best cs db <= c_ex *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + 1) +
        (R db + 1) * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof.
    intros cs db Hwf Hcanonical Hinventory.
    apply (T_best_potential_bound cs db (extraction_potential db) Hwf Hcanonical Hinventory).
    - exact (T_initial_potential cs db Hwf Hcanonical Hinventory).
    - intros s next Hreach Hstep.
      exact (extraction_step_amort cs db s next Hwf Hcanonical Hinventory Hreach Hstep).
  Qed.

End ExtractT.
