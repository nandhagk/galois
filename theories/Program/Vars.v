(** * Variable presentations

    Edge and exit readers use first-order tables keyed by encoded identities.
    For example, an absent edge binding has no uses or definitions.

    Main results
    - [universe_spec] The universe contains exactly the syntactic variable occurrences.
    - [uses_complexity] Edge uses are linear in the edge key and the returned variables.
    - [defs_complexity] Edge definitions are linear in the edge key and the returned variables.
    - [exits_complexity] Exit observations are linear in the node key and the returned variables.
    - [universe_complexity] The universe has the aggregate reader and bit-width bound.

    Builds on: Program.VarsSig and Base.Trie. *)

From Stdlib Require Import List Arith PArith NArith Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Program Require Import CfgSig VarsSig.
Import ComplexityNotations.
Import Code.List.

Module Nat.
  TimeFun Nat.max.
End Nat.

Record var_tables (X : Type) := VarTables {
  edge_uses : ptrie (list X);
  edge_defs : ptrie (list X);
  node_exits : ptrie (list X)
}.

Arguments VarTables {X}.
Arguments edge_uses {X}.
Arguments edge_defs {X}.
Arguments node_exits {X}.

TimeFun edge_uses.
TimeFun edge_defs.
TimeFun node_exits.

Module Type VARS_DATA (P : TYPE) (X : KEY_OPS).
  Parameter tables : P.t -> var_tables X.t.
End VARS_DATA.

Module Type VARS_DATA_TIME (P : TYPE) (X : KEY_T) (Import D : VARS_DATA P X).
  Parameter T_tables : P.t -> N.
  Parameter c_tables : N.
  Parameter T_tables_le : forall p, (T_tables p <= c_tables)%N.
End VARS_DATA_TIME.

Module Type VARS_DATA_T (P : TYPE) (X : KEY_T) :=
  VARS_DATA P X <+ VARS_DATA_TIME P X.

Module VarsCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (D : VARS_DATA P X)
    <: VARS_OPS P N E C X.
  Definition uses p e :=
    match trie_get (E.encode e) (edge_uses (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition defs p e :=
    match trie_get (E.encode e) (edge_defs (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition exits p n :=
    match trie_get (N.encode n) (node_exits (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition universe p :=
    List.rev_append (PTrieCode.fold (fun acc _ x => x :: acc)
      (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
      (flat_map (fun e => uses p e ++ defs p e) (C.edges p) ++
        flat_map (exits p) (C.nodes p)) PTrieCode.empty) nil) nil.
End VarsCode.

Module Vars (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (X : KEY) (D : VARS_DATA P X)
    <: VARS P N E C X.
  Include VarsCode P N E C X D.
  Include VARS_SPEC P N E C X.

  (** Each stored variable is held at its own encoded address. *)
  Definition addressed (m : ptrie X.t) : Prop :=
    forall code x, PTrieCode.get code m = Some x -> X.encode x = code.

  (** The empty collection has no incorrectly addressed binding. *)
  Lemma addressed_empty : addressed PTrieCode.empty.
  Proof.
    intros code x Hget; rewrite PTrie.get_empty in Hget; discriminate.
  Qed.

  (** Inserting a variable at its encoding preserves address agreement. *)
  Lemma addressed_set : forall m x,
    addressed m -> addressed (PTrieCode.set (X.encode x) x m).
  Proof.
    intros m x Haddress code y Hget.
    destruct (Pos.eq_dec code (X.encode x)) as [Hsame|Hother].
    - subst code; rewrite PTrie.get_set_same in Hget; now injection Hget as <-.
    - rewrite PTrie.get_set_other in Hget by exact Hother; now apply Haddress.
  Qed.

  (** Scanning occurrences preserves address agreement. *)
  Lemma scan_addressed : forall xs m, addressed m ->
    addressed (fold_left (fun s x => PTrieCode.set (X.encode x) x s) xs m).
  Proof.
    intro xs; induction xs as [|x xs IH]; intros m Haddress; cbn [fold_left].
    - exact Haddress.
    - apply IH; now apply addressed_set.
  Qed.

  (** A scanned occurrence remains present, and scans add no new variables. *)
  Lemma scan_member : forall xs m x,
    PTrieCode.get (X.encode x)
      (fold_left (fun s y => PTrieCode.set (X.encode y) y s) xs m) = Some x <->
    In x xs \/ PTrieCode.get (X.encode x) m = Some x.
  Proof.
    intro xs; induction xs as [|y xs IH]; intros m x; cbn [fold_left In].
    - tauto.
    - rewrite IH; destruct (X.eqb_spec x y) as [Hsame|Hother].
      + subst y; rewrite PTrie.get_set_same; tauto.
      + rewrite PTrie.get_set_other; [intuition congruence|].
        intro Hcode; apply Hother; now apply X.encode_inj.
  Qed.

  (** The executable universe follows the stored variables' trie enumeration. *)
  Lemma universe_entries : forall p, universe p =
    map snd (PTrieCode.elements
      (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
        (occurrences p) PTrieCode.empty)).
  Proof.
    intro p; unfold universe; fold (occurrences p).
    rewrite PTrie.fold_spec, rev_append_rev, app_nil_r.
    generalize (PTrieCode.elements
      (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
        (occurrences p) PTrieCode.empty)); intro entries.
    assert (Hfold : forall acc,
      fold_left (fun acc kv => snd kv :: acc) entries acc =
      rev (map snd entries) ++ acc).
    { induction entries as [|[code x] rest IH]; intro acc;
        cbn [fold_left map rev snd].
      - reflexivity.
      - now rewrite IH, <- app_assoc. }
    now rewrite Hfold, app_nil_r, rev_involutive.
  Qed.

  (** The prepared enumeration contains exactly the flattened occurrences. *)
  Lemma universe_members : forall p x,
    In x (universe p) <-> In x (occurrences p).
  Proof.
    intros p x; rewrite universe_entries; split.
    - intro Hin; apply in_map_iff in Hin as [[code y] [Hsame Hin]].
      cbn [snd] in Hsame; subst y; apply PTrie.elements_spec in Hin.
      pose proof (scan_addressed (occurrences p) PTrieCode.empty addressed_empty
        code x Hin) as Hcode.
      rewrite <- Hcode, scan_member, PTrie.get_empty in Hin.
      destruct Hin as [Hin|Hempty]; [exact Hin|discriminate].
    - intro Hin; apply in_map_iff; exists (X.encode x, x); split; [reflexivity|].
      apply PTrie.elements_spec; rewrite scan_member; now left.
  Qed.

  (** Flattening the readers preserves the edge and exit occurrence predicate. *)
  Lemma occurrences_spec : forall p x, In x (occurrences p) <-> occurs p x.
  Proof.
    intros p x; unfold occurrences, occurs; rewrite in_app_iff, !in_flat_map; split.
    - intros [[e [He Hx]]|Hexit]; [left|now right].
      exists e; split; [exact He|now apply in_app_iff].
    - intros [[e [He Hx]]|Hexit]; [left|now right].
      exists e; split; [exact He|now apply in_app_iff].
  Qed.

  (** The universe contains exactly the syntactic variable occurrences. *)
  Lemma universe_spec : forall p x,
    In x (universe p) <->
      (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
      (exists n, In n (C.nodes p) /\ In x (exits p n)).
  Proof.
    intros p x; rewrite universe_members; apply occurrences_spec.
  Qed.

  (** Distinct trie addresses yield a universe without repeated variables. *)
  Lemma universe_nodup : forall p, NoDup (universe p).
  Proof.
    intro p; apply (NoDup_map_inv X.encode); rewrite universe_entries, map_map.
    assert (Hcodes : map (fun kv => X.encode (snd kv))
      (PTrieCode.elements (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
        (occurrences p) PTrieCode.empty)) =
      map fst (PTrieCode.elements (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
        (occurrences p) PTrieCode.empty))).
    { apply map_ext_in; intros [code x] Hin; cbn [fst snd].
      apply (scan_addressed (occurrences p) PTrieCode.empty addressed_empty code x).
      now apply PTrie.elements_spec. }
    rewrite Hcodes; apply PTrie.elements_nodup.
  Qed.
End Vars.

Module VarsT (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T)
    (D : VARS_DATA_T P X) <: VARS_ALL P N E C X.
  Include Vars P N E C X D.
  TimeFun uses.
  TimeFun defs.
  TimeFun exits.
  TimeFun occurrences.
  TimeFun occurrence_width.
  TimeFun universe.

  Definition universe_work p :=
    (C.T_edges p + C.T_nodes p +
      fold_right N.add 0%N (map (fun e => T_uses p e + T_defs p e)%N (C.edges p)) +
      fold_right N.add 0%N (map (T_exits p) (C.nodes p)) +
      N.of_nat (length (C.edges p) + length (C.nodes p) + length (occurrences p) + 1) *
        N.of_nat (occurrence_width p + 1) +
      fold_right N.add 0%N (map X.T_encode (occurrences p)))%N.

  Definition c_vars : N :=
    (2 * 4096 * 4096 + D.c_tables + E.c_key + N.c_key + 1056)%N.

  (** Flattening syntax preserves exactly the occurrence predicate. *)
  Lemma occurrences_iff : forall p x, In x (occurrences p) <-> occurs p x.
  Proof.
    apply occurrences_spec.
  Qed.

  (** Deduplicating occurrences gives the prepared variable universe. *)
  Lemma universe_occurrences_iff : forall p x, In x (universe p) <-> In x (occurrences p).
  Proof.
    apply universe_members.
  Qed.
  Definition seen p :=
    fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p) PTrieCode.empty.
  TimeFun seen.
  Definition k_seen : N := 4096%N.
  Definition k_collect : N := 4096%N.

  (** Use lookup pays for its table reader and encoded edge path. *)
  Lemma T_uses_le : forall p e,
    (T_uses p e <= c_vars * N.of_nat (E.bits e + length (uses p e) + 1))%N.
  Proof.
    intros p e; pose proof (D.T_tables_le p) as Htables.
    pose proof (E.T_encode_le e) as Hcode.
    unfold T_uses; time_simpl; PTrieT.trie_get_le.
    unfold c_vars, E.bits in *; rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Definition lookup pays for its table reader and encoded edge path. *)
  Lemma T_defs_le : forall p e,
    (T_defs p e <= c_vars * N.of_nat (E.bits e + length (defs p e) + 1))%N.
  Proof.
    intros p e; pose proof (D.T_tables_le p) as Htables.
    pose proof (E.T_encode_le e) as Hcode.
    unfold T_defs; time_simpl; PTrieT.trie_get_le.
    unfold c_vars, E.bits in *; rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Exit lookup pays for its table reader and encoded node path. *)
  Lemma T_exits_le : forall p n,
    (T_exits p n <= c_vars * N.of_nat (N.bits n + length (exits p n) + 1))%N.
  Proof.
    intros p n; pose proof (D.T_tables_le p) as Htables.
    pose proof (N.T_encode_le n) as Hcode.
    unfold T_exits; time_simpl; PTrieT.trie_get_le.
    unfold c_vars, N.bits in *; rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Edge uses are linear in the edge key and the returned variables. *)
  Lemma uses_complexity :
    T_uses p e ∈ 𝑂(N.of_nat (E.bits e + length (uses p e))) for (p, e).
  Proof.
    apply bigO_intro with (c := c_vars).
    intros [p e] _; pose proof (T_uses_le p e) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Edge definitions are linear in the edge key and the returned variables. *)
  Lemma defs_complexity :
    T_defs p e ∈ 𝑂(N.of_nat (E.bits e + length (defs p e))) for (p, e).
  Proof.
    apply bigO_intro with (c := c_vars).
    intros [p e] _; pose proof (T_defs_le p e) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Exit observations are linear in the node key and the returned variables. *)
  Lemma exits_complexity :
    T_exits p n ∈ 𝑂(N.of_nat (N.bits n + length (exits p n))) for (p, n).
  Proof.
    apply bigO_intro with (c := c_vars).
    intros [p n] _; pose proof (T_exits_le p n) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** The named preparation table is the executable occurrence scan. *)
  Lemma seen_def : forall p,
    seen p = fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p)
      PTrieCode.empty.
  Proof.
    reflexivity.
  Qed.

  (** Every occurrence key fits the maximum width of its occurrence list. *)
  Lemma occurrence_bits : forall p x, In x (occurrences p) ->
    X.bits x <= occurrence_width p.
  Proof.
    intros p x; unfold occurrence_width, X.bits.
    generalize (occurrences p); intro xs; induction xs as [|y xs IH]; intro Hin.
    - contradiction.
    - cbn [map fold_right]; destruct Hin as [Hsame|Hin].
      + subst y; apply PeanoNat.Nat.le_max_l.
      + eapply PeanoNat.Nat.le_trans; [now apply IH|apply PeanoNat.Nat.le_max_r].
  Qed.

  (** Each insertion adds at most the bit length of its occurrence key. *)
  Lemma scan_nodes : forall xs m width,
    (forall x, In x xs -> X.bits x <= width) ->
    PTrie.nodes (fold_left (fun s x => PTrieCode.set (X.encode x) x s) xs m) <=
      PTrie.nodes m + length xs * width.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros m width Hwidth; cbn [fold_left length].
    - lia.
    - pose proof (Hwidth x (or_introl eq_refl)) as Hhead.
      pose proof (PTrie.nodes_set X.t (X.encode x) x m) as Hnodes.
      specialize (IH (PTrieCode.set (X.encode x) x m) width
        (fun y Hy => Hwidth y (or_intror Hy))).
      unfold X.bits in Hhead; nia.
  Qed.

  (** Universe preparation allocates at most one trie node per input key bit. *)
  Lemma seen_nodes_le : forall p,
    PTrie.nodes (seen p) <= length (occurrences p) * occurrence_width p.
  Proof.
    intro p; unfold seen.
    pose proof (scan_nodes (occurrences p) PTrieCode.empty (occurrence_width p)
      (occurrence_bits p)) as Hnodes.
    exact Hnodes.
  Qed.

  (** A stored entry identifies an original occurrence at its own encoding. *)
  Lemma seen_entry : forall p code x, In (code, x) (PTrieCode.elements (seen p)) ->
    X.encode x = code /\ In x (occurrences p).
  Proof.
    intros p code x Hin; apply PTrie.elements_spec in Hin; unfold seen in Hin.
    pose proof (scan_addressed (occurrences p) PTrieCode.empty addressed_empty
      code x Hin) as Hcode; split; [exact Hcode|].
    rewrite <- Hcode, scan_member, PTrie.get_empty in Hin.
    destruct Hin as [Hin|Hempty]; [exact Hin|discriminate].
  Qed.

  (** Deduplication never increases the occurrence count. *)
  Lemma seen_length : forall p,
    length (PTrieCode.elements (seen p)) <= length (occurrences p).
  Proof.
    intro p; assert (Hlength : length (universe p) <= length (occurrences p)).
    { apply NoDup_incl_length; [apply universe_nodup|].
      intros x Hx; now apply universe_members in Hx. }
    rewrite universe_entries, length_map in Hlength; exact Hlength.
  Qed.

  (** A list of bounded natural weights has a bounded total weight. *)
  Lemma sum_weights : forall A (weight : A -> nat) xs bound,
    (forall x, In x xs -> weight x <= bound) ->
    fold_right Nat.add 0 (map weight xs) <= length xs * bound.
  Proof.
    intros A weight xs; induction xs as [|x xs IH]; intros bound Hbound.
    - reflexivity.
    - pose proof (Hbound x (or_introl eq_refl)) as Hhead.
      specialize (IH bound (fun y Hy => Hbound y (or_intror Hy))).
      cbn [fold_right map length]; nia.
  Qed.

  (** The trie key mass is charged to the original occurrence widths. *)
  Lemma seen_weight : forall p,
    PTrieT.weight (seen p) <= length (occurrences p) * (occurrence_width p + 1).
  Proof.
    intro p; unfold PTrieT.weight.
    eapply PeanoNat.Nat.le_trans with (m :=
      length (PTrieCode.elements (seen p)) * (occurrence_width p + 1)).
    - apply sum_weights; intros [code x] Hin; cbn [fst].
      destruct (seen_entry p code x Hin) as [Hcode Hx].
      pose proof (occurrence_bits p x Hx) as Hbits; unfold X.bits in Hbits.
      rewrite <- Hcode; lia.
    - pose proof (seen_length p); nia.
  Qed.

  (** Collecting one value per binding cannot exceed the occurrence count. *)
  Lemma collected_length : forall p,
    length (PTrieCode.fold (fun acc _ x => x :: acc) (seen p) nil) <=
      length (occurrences p).
  Proof.
    intro p; pose proof (seen_length p) as Hlength.
    rewrite <- length_map with (f := @snd positive X.t) in Hlength.
    unfold seen in Hlength.
    rewrite <- universe_entries in Hlength.
    unfold universe in Hlength; fold (occurrences p) in Hlength; fold (seen p) in Hlength.
    now rewrite rev_append_rev, app_nil_r, length_rev in Hlength.
  Qed.

  (** Flat-map traversal pays each reader and its actual output length. *)
  Lemma flat_map_time : forall A B (f : A -> list B) Tf xs budget,
    (forall x, In x xs ->
      (Tf x <= budget x + N.of_nat (length (f x)) + 4)%N) ->
    (Code.List.T_flat_map f Tf xs <=
      fold_right N.add 0%N (map budget xs) +
      2 * N.of_nat (length (flat_map f xs)) + 6 * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs; induction xs as [|x xs IH]; intros budget Hbudget.
    - time_step.
    - pose proof (Hbudget x (or_introl eq_refl)) as Hhead.
      specialize (IH budget (fun y Hy => Hbudget y (or_intror Hy))).
      pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happend.
      time_step; rewrite length_app, !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** A left fold pays its callback bound at every visited occurrence. *)
  Lemma fold_left_time : forall A B (f : A -> B -> A) Tf xs acc budget,
    (forall state x, In x xs -> (Tf state x <= budget x)%N) ->
    (List.T_fold_left f Tf xs acc <=
      fold_right N.add 0%N (map budget xs) + 2 * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs; induction xs as [|x xs IH]; intros acc budget Hbudget.
    - time_step.
    - pose proof (Hbudget acc x (or_introl eq_refl)) as Hhead.
      specialize (IH (f acc x) budget
        (fun state y Hy => Hbudget state y (or_intror Hy))).
      time_step.
  Qed.

  (** A fixed surcharge is paid once per entry in a sum of callback costs. *)
  Lemma sum_extra : forall A (cost : A -> N) xs extra,
    fold_right N.add 0%N (map (fun x => (cost x + extra)%N) xs) =
      (fold_right N.add 0%N (map cost xs) + N.of_nat (length xs) * extra)%N.
  Proof.
    intros A cost xs; induction xs as [|x xs IH]; intro extra; time_cbn.
    - reflexivity.
    - rewrite IH; nia.
  Qed.

  (** Flattening the reader tables pays their clocks and the lists it traverses. *)
  Lemma occurrences_time : forall p,
    (T_occurrences p <= C.T_edges p + C.T_nodes p +
      fold_right N.add 0%N (map (fun e => (T_uses p e + T_defs p e)%N) (C.edges p)) +
      fold_right N.add 0%N (map (T_exits p) (C.nodes p)) +
      8 * N.of_nat (length (C.edges p) + length (C.nodes p) +
        length (occurrences p) + 1))%N.
  Proof.
    intro p.
    assert (Hedge : forall e, In e (C.edges p) ->
      (1 + (T_uses p e + T_defs p e + Datatypes.T_app (uses p e) (defs p e)) <=
        T_uses p e + T_defs p e + N.of_nat (length (uses p e ++ defs p e)) + 4)%N).
    { intros e _; pose proof (Datatypes.T_app_le (uses p e) (defs p e)) as Happend.
      rewrite length_app; time_cbn_all; nia. }
    pose proof (flat_map_time E.t X.t (fun e => uses p e ++ defs p e)
      (fun e => (1 + (T_uses p e + T_defs p e +
        Datatypes.T_app (uses p e) (defs p e)))%N)
      (C.edges p) (fun e => (T_uses p e + T_defs p e)%N) Hedge) as Hedges.
    pose proof (flat_map_time N.t X.t (exits p) (fun n => T_exits p n)
      (C.nodes p) (T_exits p) (fun n _ => ltac:(nia))) as Hnodes.
    pose proof (Datatypes.T_app_le
      (flat_map (fun e => uses p e ++ defs p e) (C.edges p))
      (flat_map (exits p) (C.nodes p))) as Happend.
    unfold T_occurrences; time_simpl; unfold occurrences; rewrite length_app.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** The occurrence scan charges each encoding and its bounded trie insertion. *)
  Lemma scan_time : forall xs m width,
    (forall x, In x xs -> X.bits x <= width) ->
    (List.T_fold_left (fun s x => PTrieCode.set (X.encode x) x s)
      (fun s x => (1 + (X.T_encode x + PTrieCode.T_set (X.encode x) x s))%N) xs m <=
      fold_right N.add 0%N (map X.T_encode xs) +
      N.of_nat (length xs) * (1024 * N.of_nat (width + 1) + 3) + 1)%N.
  Proof.
    intros xs m width Hwidth.
    assert (Hcallback : forall state x, In x xs ->
      (1 + (X.T_encode x + PTrieCode.T_set (X.encode x) x state) <=
        X.T_encode x + (1024 * N.of_nat (width + 1) + 1))%N).
    { intros state x Hin; pose proof (Hwidth x Hin) as Hbits.
      pose proof (PTrieT.T_set_le X.t (X.encode x) x state) as Hset.
      unfold PTrieT.c_trie in Hset; unfold X.bits in Hbits.
      apply time_of_nat_le in Hbits; rewrite !Nat2N.inj_add in *; time_cbn_all; nia. }
    pose proof (fold_left_time (PTrieCode.t X.t) X.t
      (fun s x => PTrieCode.set (X.encode x) x s)
      (fun s x => (1 + (X.T_encode x + PTrieCode.T_set (X.encode x) x s))%N)
      xs m (fun x => (X.T_encode x + (1024 * N.of_nat (width + 1) + 1))%N)
      Hcallback) as Hscan.
    rewrite sum_extra in Hscan; nia.
  Qed.

  (** Preparing the trie pays all readers and every encoded occurrence path. *)
  Lemma T_seen_le : forall p,
    (T_seen p <= k_seen * universe_work p)%N.
  Proof.
    intro p; pose proof (occurrences_time p) as Hreaders.
    pose proof (scan_time (occurrences p) PTrieCode.empty (occurrence_width p)
      (occurrence_bits p)) as Hscan.
    unfold T_seen, k_seen, universe_work; time_simpl.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** Collecting the prepared trie pays its bounded skeleton and encoded key mass. *)
  Lemma T_universe_split : forall p,
    (T_universe p <= k_collect * (T_seen p +
      N.of_nat (length (occurrences p) + 1) * N.of_nat (occurrence_width p + 1)))%N.
  Proof.
    intro p.
    pose proof (PTrieT.T_fold_le X.t (list X.t)
      (fun acc _ x => x :: acc) (fun _ _ _ => 1%N)
      (seen p) nil 1%N (fun _ _ _ => N.le_refl 1)) as Hfold.
    pose proof (List.T_rev_append_le
      (PTrieCode.fold (fun acc _ x => x :: acc) (seen p) nil) nil) as Hreverse.
    pose proof (seen_nodes_le p) as Hnodes.
    pose proof (seen_weight p) as Hweight.
    pose proof (collected_length p) as Hlength.
    assert (Hcompose : (T_universe p <= T_seen p +
      PTrieT.T_fold (fun acc _ x => x :: acc) (fun _ _ _ => 1%N) (seen p) nil +
      List.T_rev_append (PTrieCode.fold (fun acc _ x => x :: acc) (seen p) nil) nil + 8)%N).
    { unfold T_universe, T_seen, T_occurrences, seen, occurrences; time_simpl; nia. }
    apply time_of_nat_le in Hnodes, Hweight, Hlength.
    unfold PTrieT.c_trie in Hfold; unfold k_collect.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *; time_cbn_all; nia.
  Qed.

  (** Universe preparation pays for each encoded occurrence lookup. *)
  Lemma T_universe_le : forall p,
    (T_universe p <= c_vars * universe_work p)%N.
  Proof.
    intro p; pose proof (T_seen_le p) as Hseen; pose proof (T_universe_split p) as Hcollect.
    assert (Hsize : (N.of_nat (length (occurrences p) + 1) *
      N.of_nat (occurrence_width p + 1) <= universe_work p)%N).
    { unfold universe_work; rewrite !Nat2N.inj_add; nia. }
    unfold k_seen, k_collect, c_vars in *; nia.
  Qed.

  (** The universe bound includes every reader, encoding and occurrence width. *)
  Lemma universe_complexity : T_universe p ∈ 𝑂(universe_work p) for p.
  Proof.
    exists c_vars; intros p _; pose proof (T_universe_le p); nia.
  Qed.
End VarsT.
