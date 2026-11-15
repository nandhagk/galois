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
  pose proof (PTrieT.trie_get_clock (nat * output) f tb) as Hget.
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
  intros seen i. pose proof (PTrieT.trie_get_clock unit i seen) as Hget.
  time_unfold @T_dag_seen. time_simpl. time_cbn.
  destruct (trie_get i seen); rewrite !Nat2N.inj_add; lia.
Qed.

(** Cost lookup follows one trie path without inspecting the stored number. *)
Lemma T_dag_get_cost_le : forall costs i,
  (T_dag_get_cost costs i <= 8 * N.of_nat (Pos.size_nat i + 1))%N.
Proof.
  intros costs i. pose proof (PTrieT.trie_get_clock N i costs) as Hget.
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

End SearchFacts.

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

  Lemma best_row : forall cs db c n f k, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    In (c, (n, (f, k))) (best cs db) ->
    row (D.view db) f k (Some (Id c)) /\
      n = C.fn_cost f (map (cost_of (best cs db)) k).
  Proof. Admitted. (* STUB *)

  Lemma best_optimal : forall cs db c e, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    represents (D.view db) (Id c) e ->
    exists n ch, In (D.repr db c, (n, ch)) (best cs db) /\ (n <= tree_cost e)%N.
  Proof. Admitted. (* STUB *)

  Lemma best_attained : forall cs db c n ch, D.wf db -> D.canonical db ->
    ctor_inventory cs db ->
    In (c, (n, ch)) (best cs db) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)

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
  Definition R (db : D.t) : nat := length (Rows.rows db).
  Definition a (db : D.t) : nat := Rows.maximum_arity (Rows.rows db).
  (* STUB-CODE *)
  Definition cost_width (_ : D.t) : nat := 0.
  Definition c_ex : N :=
    (64 * 1024) * (PTrieT.c_trie + D.c_db + C.c_cost + 1).
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
  Proof. Admitted. (* STUB *)

  Lemma T_best_le : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_best cs db <= c_ex *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + 1) +
        (R db + 1) * (Nat.log2 (R db) + 1)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)

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

  Lemma T_check_dag_le : forall db c g, D.wf db ->
    (T_check_dag db c g <= c_ex * N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) *
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
        unfold c_ex, checker_row_budget.
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
        unfold c_ex, checker_row_budget. rewrite N.mul_1_r, N.add_0_r.
        exact Hbudget.
  Qed.

  Lemma T_extract_le : forall cs db c, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_extract cs db c <= T_best cs db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition state := extraction_state V.t D.t Q.t.
  Definition initial (cs : list (positive * (N * nat))) (db : D.t) : state :=
    search_initial db (inventory_rows (fun slot => D.index slot false db)
      I.child I.children I.root cs).
  Definition step (_ : list (positive * (N * nat))) (_ : D.t) (s : state)
      : state + extraction_best V.t := search_step s.
  Definition finalised (s : state) : extraction_best V.t := search_finalised s.
  (* STUB-CODE *)
  Definition counter (_ : state) (_ : positive) : nat := 0.
  (* STUB-CODE *)
  Definition children (_ : D.t) (_ : positive) : list positive := [].
  (* STUB-CODE *)
  Definition ready (_ : state) : list (positive * N) := [].
  (* STUB-CODE *)
  Definition heap_potential (_ : state) : N := 0%N.
  TimeFun initial.
  TimeFun step.
  TimeFun finalised.
  TimeFun counter.
  TimeFun children.
  TimeFun ready.
  TimeFun heap_potential.
  Definition k_step : N := 1. (* STUB *)
  Definition reachable (sl : list (positive * (N * nat))) (db : D.t) (s : state) : Prop :=
    clos_refl_trans state (fun a b => step sl db a = inl b) (initial sl db) s.
  Definition knuth_inv (db : D.t) (s : state) : Prop :=
    forall c n ch, In (c, (n, ch)) (finalised s) ->
      forall e, represents (D.view db) (Id c) e -> (n <= tree_cost e)%N.
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
  Proof. Admitted. (* STUB *)

  Lemma F3_ready : forall cs db s c n, reachable cs db s ->
    In (c, n) (ready s) -> counter s c = 0.
  Proof. Admitted. (* STUB *)

  Lemma F4_pop_final : forall cs db s s', D.wf db -> D.canonical db -> ctor_inventory cs db ->
    reachable cs db s -> knuth_inv db s -> step cs db s = inl s' -> knuth_inv db s'.
  Proof. Admitted. (* STUB *)

  Lemma F5_finalised_attained : forall cs db s c n ch, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s -> In (c, (n, ch)) (finalised s) ->
    exists e, represents (D.view db) (Id c) e /\ tree_cost e = n.
  Proof. Admitted. (* STUB *)

  Lemma F6_best_loop : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    loop_fuel (step cs db) (R db + 1) (initial cs db) = inr (best cs db).
  Proof. Admitted. (* STUB *)

  Lemma T0_initial : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_initial cs db + heap_potential (initial cs db) <= k_step *
      N.of_nat (inventory_bits cs + (R db + 1) * (a db + Nat.log2 (R db) + 2)) *
      N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T1_step_amort : forall cs db s s', D.wf db -> D.canonical db -> ctor_inventory cs db ->
    reachable cs db s -> knuth_inv db s ->
    step cs db s = inl s' ->
    (T_step cs db s + heap_potential s' <= heap_potential s + k_step *
      N.of_nat (a db + Nat.log2 (R db) + 2) * N.of_nat (D.unit db + 1) *
      N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T1b_step_stop : forall cs db s out, D.wf db -> D.canonical db ->
    ctor_inventory cs db -> reachable cs db s -> step cs db s = inr out ->
    (T_step cs db s <= k_step * N.of_nat (R db + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The bounded extraction loop charges its initialization, steps and fuel. *)
  Lemma T2_best_loop : forall cs db, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_best cs db <= T_initial cs db +
      T_loop_fuel (step cs db) (T_step cs db) (R db + 1) (initial cs db) +
      k_step * N.of_nat (R db + 1))%N.
  Proof. Admitted. (* STUB *)

End ExtractT.
