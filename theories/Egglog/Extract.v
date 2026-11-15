(** * Placeholder expression extraction

    These operations provide the interfaces for extraction and certificate checking.
    For example, the placeholder extractor returns no certificate.
    Builds on: ExtractSig. *)

From Stdlib Require Import List PArith NArith Arith Bool Lia Relations.Relation_Operators
  Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig IndexSig DatabaseSig Syntax Model Sorts ExtractSig.

Import List.ListNotations.

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

Module ExtractCode (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V) <: EXTRACT_OPS V I D C.
  Definition inventory (ds : list decl) (sl : list (positive * list nat))
      : list (positive * (N * nat)) := inventory_scan (inventory_decl_table ds) sl 0%N.
  (* STUB-CODE *)
  Definition best (_ : list (positive * (N * nat))) (_ : D.t) : extraction_best V.t := [].
  Definition check_dag (db : D.t) (c : positive) (g : extraction_dag V.t) : option N :=
    dag_check (dag_check_row (D.ids db) (fun i => fst (D.find i db))
      (fun f k => fst (D.lookup f k db))) C.fn_cost C.val_cost g c.
  Definition extract (cs : list (positive * (N * nat))) (db : D.t) (c : positive)
      : option (extraction_dag V.t) :=
    if N.ltb (D.ids db) (Npos c) then None else
      extraction_candidate (check_dag db) c (fst (D.find c db)) (best cs db).
End ExtractCode.

Module Extract (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V)
    <: EXTRACT V I D C.
  Include ExtractCode V I D C.
  Include EXTRACT_SPEC V I D C.
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
    <: EXTRACT_ALL V I D C.
  Include Extract V I D C.
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

  Definition state := unit.
  (* STUB-CODE *)
  Definition initial (_ : list (positive * (N * nat))) (_ : D.t) : state := tt.
  (* STUB-CODE *)
  Definition step (_ : list (positive * (N * nat))) (_ : D.t) (_ : state)
      : state + extraction_best V.t := inr [].
  (* STUB-CODE *)
  Definition finalised (_ : state) : extraction_best V.t := [].
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
  Proof. Admitted. (* STUB *)

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
