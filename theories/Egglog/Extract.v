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

Module ExtractCode (V : VALUE_OPS) (I : INDEX_OPS V) (D : DATABASE_OPS V I)
    (C : COST_OPS V) <: EXTRACT_OPS V I D C.
  Definition inventory (ds : list decl) (sl : list (positive * list nat))
      : list (positive * N) := inventory_scan (inventory_decl_table ds) sl 0%N.
  (* STUB-CODE *)
  Definition best (_ : list (positive * N)) (_ : D.t) : extraction_best V.t := [].
  (* STUB-CODE *)
  Definition extract (_ : list (positive * N)) (_ : D.t) (_ : positive)
      : option (extraction_dag V.t) := None.
  (* STUB-CODE *)
  Definition check_dag (_ : D.t) (_ : positive) (_ : extraction_dag V.t) : option N := None.
End ExtractCode.

Module Extract (V : VALUE) (I : INDEX V) (D : DATABASE V I) (C : COST V)
    <: EXTRACT V I D C.
  Include ExtractCode V I D C.
  Include EXTRACT_SPEC V I D C.
  (* STUB-CODE *)
  Definition unfold (_ : extraction_dag V.t) (_ : positive) : option (@Model.expr V.t) := None.
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
  Proof. Admitted. (* STUB *)

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

  Lemma check_dag_sound : forall db c g n, D.wf db -> check_dag db c g = Some n ->
    dag_valid (D.view db) c g /\
    exists e, represents (D.view db) (Id c) e /\ unfold g c = Some e /\ n = tree_cost e.
  Proof. Admitted. (* STUB *)

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
  Definition c_ex : N := 1. (* STUB *)
  Lemma T_inventory_le : forall ds sl,
    (T_inventory ds sl <= c_ex * N.of_nat (layout_bits ds sl + 1) *
      N.of_nat (Nat.log2 (length sl) + 1))%N.
  Proof. Admitted. (* STUB *)

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
