(** * Placeholder expression extraction

    These operations provide the interfaces for extraction and certificate checking.
    For example, the placeholder extractor returns no certificate.
    Builds on: ExtractSig. *)

From Stdlib Require Import List PArith NArith Arith Bool Lia Relations.Relation_Operators.
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

(** Only a constructor's unpermuted full slot is selected. *)
Definition inventory_slot (tb : ptrie (nat * output)) (f : positive)
    (positions : list nat) : bool :=
  match trie_get f tb with
  | Some (arity, OId) => inventory_sequence 0 (S arity) positions
  | _ => false
  end.
TimeFun inventory_slot.

(** A selected constructor is removed so that a later full slot cannot emit it again. *)
Fixpoint inventory_scan (tb : ptrie (nat * output)) (sl : list (positive * list nat))
    (slot : N) : list (positive * N) :=
  match sl with
  | [] => []
  | (f, positions) :: rest =>
    if inventory_slot tb f positions then
      (f, slot) :: inventory_scan (PTrieCode.remove f tb) rest (N.succ slot)
    else inventory_scan tb rest (N.succ slot)
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

(** Slot acceptance records the constructor arity and its full permutation. *)
Lemma inventory_slot_spec : forall tb f positions,
  inventory_slot tb f positions = true <->
    exists n, trie_get f tb = Some (n, OId) /\ positions = seq 0 (S n).
Proof.
  intros tb f positions. unfold inventory_slot.
  destruct (trie_get f tb) as [[n out]|] eqn:Hget.
  - destruct out; try (split; [discriminate | intros [? [H _]]; discriminate]).
    rewrite inventory_sequence_spec. split.
    + intro Hseq. exists n. auto.
    + intros [m [Hpair Hseq]]. injection Hpair as <-. exact Hseq.
  - split; [discriminate | intros [? [H _]]; discriminate].
Qed.

(** Each selected entry identifies its original position and declaration. *)
Lemma inventory_scan_sound : forall sl tb offset f slot,
  In (f, slot) (inventory_scan tb sl offset) ->
  exists n positions j, nth_error sl j = Some (f, positions) /\
    slot = (offset + N.of_nat j)%N /\ trie_get f tb = Some (n, OId) /\
    positions = seq 0 (S n).
Proof.
  induction sl as [|[head positions] sl IH]; intros tb offset f slot Hin;
    cbn [inventory_scan] in Hin; [contradiction |].
  destruct (inventory_slot tb head positions) eqn:Hslot.
  - destruct Hin as [Heq | Hin].
    + injection Heq as <- <-.
      apply inventory_slot_spec in Hslot as [n [Hget Hseq]].
      exists n, positions, 0. cbn [nth_error N.of_nat]. repeat split; auto; lia.
    + destruct (IH _ _ _ _ Hin) as [n [perm [j [Hnth [Hindex [Hget Hseq]]]]]].
      assert (Hneq : f <> head).
      { intro Heq. subst f. rewrite PTrie.get_remove_same in Hget. discriminate. }
      rewrite PTrie.get_remove_other in Hget by exact Hneq.
      exists n, perm, (S j). cbn [nth_error]. repeat split; auto.
      rewrite Nat2N.inj_succ. lia.
  - destruct (IH _ _ _ _ Hin) as [n [perm [j [Hnth [Hindex [Hget Hseq]]]]]].
    exists n, perm, (S j). cbn [nth_error]. repeat split; auto.
    rewrite Nat2N.inj_succ. lia.
Qed.

(** Removing each selected name makes the output duplicate free. *)
Lemma inventory_scan_nodup : forall sl tb offset,
  NoDup (map fst (inventory_scan tb sl offset)).
Proof.
  induction sl as [|[f positions] sl IH]; intros tb offset; cbn [inventory_scan].
  - constructor.
  - destruct (inventory_slot tb f positions); [|apply IH].
    cbn [map fst]. constructor; [|apply IH].
    intro Hin. apply in_map_iff in Hin as [[g slot] [Heq Hin]].
    cbn [fst] in Heq. subst g.
    destruct (inventory_scan_sound _ _ _ _ _ Hin)
      as [n [perm [j [_ [_ [Hget _]]]]]].
    rewrite PTrie.get_remove_same in Hget. discriminate.
Qed.

(** Any constructor with a full slot is selected at that slot or an earlier full slot. *)
Lemma inventory_scan_complete : forall sl tb offset f n,
  trie_get f tb = Some (n, OId) -> In (f, seq 0 (S n)) sl ->
  In f (map fst (inventory_scan tb sl offset)).
Proof.
  induction sl as [|[head positions] sl IH]; intros tb offset f n Hget Hin;
    [contradiction |].
  cbn [inventory_scan]. destruct (inventory_slot tb head positions) eqn:Hslot.
  - cbn [map fst]. destruct (Pos.eq_dec f head) as [-> | Hneq]; [now left |].
    right. eapply IH.
    + rewrite PTrie.get_remove_other by exact Hneq. exact Hget.
    + destruct Hin as [Heq | Hin]; [congruence |exact Hin].
  - eapply IH; [exact Hget |].
    destruct Hin as [Heq | Hin]; [|exact Hin].
    injection Heq as Hhead Hpositions. subst head positions.
    assert (Haccept : inventory_slot tb f (seq 0 (S n)) = true).
    { apply inventory_slot_spec. exists n. auto. }
    change (inventory_slot tb f (seq 0 (S n)) = false) in Hslot.
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
    cbn [inventory_scan]. destruct (inventory_slot tb f positions).
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
    destruct (inventory_slot tb f positions);
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
Definition dag_children_seen {V} (seen : ptrie unit) (k : list (cell V)) : bool :=
  forallb (fun c => match c with Id i => dag_seen seen i | Val _ => true end) k.
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
  intros V seen k. unfold dag_children_seen. rewrite forallb_forall. split.
  - intros H i Hin. exact (H (Id i) Hin).
  - intros H [i|v] Hin; [apply H; exact Hin |reflexivity].
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
Definition dag_cost_cells {V} (val_cost : V -> N) (costs : ptrie N)
    (k : list (cell V)) : list N :=
  map (fun c => match c with Id i => dag_get_cost costs i | Val v => val_cost v end) k.
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

Module ExtractCode (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V) <: EXTRACT_OPS V I D C.
  Definition inventory (ds : list decl) (sl : list (positive * list nat))
      : list (positive * N) := inventory_scan (inventory_decl_table ds) sl 0%N.
  (* STUB-CODE *)
  Definition best (_ : list (positive * N)) (_ : D.t) : extraction_best V.t := [].
  (* STUB-CODE *)
  Definition extract (_ : list (positive * N)) (_ : D.t) (_ : positive)
      : option (extraction_dag V.t) := None.
  Definition check_dag (db : D.t) (c : positive) (g : extraction_dag V.t) : option N :=
    dag_check (dag_check_row (D.ids db) (fun i => fst (D.find i db))
      (fun f k => fst (D.lookup f k db))) C.fn_cost C.val_cost g c.
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
      + intro Hin. apply in_map_iff in Hin as [[g slot] [Heq Hin]].
        cbn [fst] in Heq. subst g.
        destruct (inventory_scan_sound _ _ _ _ _ Hin)
          as [n [positions [j [_ [_ [Hget _]]]]]].
        rewrite inventory_decl_lookup in Hget.
        destruct (lookup_sorts ds f), (lookup_kind ds f) as [out|];
          try discriminate.
        inversion Hget. reflexivity.
    - split.
      + intros f k i Hrow.
        destruct (Hsorted _ _ _ Hrow) as [out [_ [Hkind Hout]]].
        destruct out; [discriminate |exact Hkind |discriminate].
      + intros f slot Hin.
        destruct (inventory_scan_sound _ _ _ _ _ Hin)
          as [n [positions [j [Hnth [Hindex [Hget Hpositions]]]]]].
        cbn [N.add] in Hindex. subst slot positions.
        exists (seq 0 (S n)). split.
        * unfold D.slot_of. rewrite Hslots, Nat2N.id. exact Hnth.
        * intros k o Hrow.
          destruct (Hsorted _ _ _ Hrow) as [out [Hsorts [Hkind Hout]]].
          rewrite inventory_decl_lookup, Hsorts, <- Hkinds, Hkind in Hget.
          injection Hget as Hlen Hout_kind. subst out.
          destruct o as [[i|v]|]; try discriminate.
          cbn [option_list]. unfold D.permute.
          replace (S n) with (length (k ++ [Id i])).
          -- apply inventory_permute_full.
          -- rewrite length_map in Hlen. rewrite length_app.
             cbn [length]. lia.
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
  Proof. Admitted. (* STUB *)

End Extract.

Module ExtractT (V : VALUE_T) (I : INDEX_T V) (D : DATABASE_T V I) (C : COST_T V)
    <: EXTRACT_ALL V I D C.
  Include Extract V I D C.
  TimeFun inventory.
  TimeFun best.
  TimeFun extract.
  TimeFun check_dag.
  TimeFun unfold.
  (* STUB-CODE *)
  Definition R (_ : D.t) : nat := 0.
  (* STUB-CODE *)
  Definition a (_ : D.t) : nat := 0.
  (* STUB-CODE *)
  Definition cost_width (_ : D.t) : nat := 0.
  Definition c_ex : N := 128 * (PTrieT.c_trie + 1).
  Lemma T_inventory_le : forall ds sl,
    (T_inventory ds sl <= c_ex * N.of_nat (layout_bits ds sl + 1) *
      N.of_nat (Nat.log2 (length sl) + 1))%N.
  Proof.
    intros ds sl.
    pose proof (T_inventory_decl_table_le ds) as Hdecl.
    pose proof (T_inventory_scan_le sl (inventory_decl_table ds) 0%N (length sl)
      ltac:(cbn [N.to_nat]; lia)) as Hscan.
    time_unfold @T_inventory. time_simpl. time_cbn.
    unfold c_ex, layout_bits. unfold inventory_slot_bits in Hscan.
    rewrite !Nat2N.inj_add in *. unfold PTrieT.c_trie in *. nia.
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

  Lemma R_spec : forall cs db, D.wf db -> ctor_inventory cs db ->
    exists rs, NoDup rs /\ length rs = R db /\
    forall f k i, In (f, k, i) rs <-> row (D.view db) f k (Some (Id i)).
  Proof. Admitted. (* STUB *)

  Lemma a_spec : forall cs db, D.wf db -> ctor_inventory cs db ->
    (forall f k i, row (D.view db) f k (Some (Id i)) -> length k <= a db) /\
    (a db = 0 \/ exists f k i, row (D.view db) f k (Some (Id i)) /\ length k = a db).
  Proof. Admitted. (* STUB *)

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

  Lemma T_check_dag_le : forall db c g, D.wf db ->
    (T_check_dag db c g <= c_ex * N.of_nat (cert_size V.encode g + Pos.size_nat c + 1) *
      N.of_nat (D.unit db + 1) *
      N.of_nat (match check_dag db c g with
        | Some n => N.size_nat n
        | None => 0
        end + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_extract_le : forall cs db c, D.wf db -> D.canonical db -> ctor_inventory cs db ->
    (T_extract cs db c <= T_best cs db + c_ex * N.of_nat (R db + 1) *
      N.of_nat (a db + 1) * N.of_nat (D.unit db + 1) * N.of_nat (cost_width db + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition state := unit.
  (* STUB-CODE *)
  Definition initial (_ : list (positive * N)) (_ : D.t) : state := tt.
  (* STUB-CODE *)
  Definition step (_ : list (positive * N)) (_ : D.t) (_ : state)
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
  Definition reachable (sl : list (positive * N)) (db : D.t) (s : state) : Prop :=
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
