(** * Variable presentations

    Edge and exit readers use first-order tables keyed by encoded identities.
    For example, an absent edge binding has no uses or definitions.
    Builds on: Program.VarsSig and Base.Trie. *)

From Stdlib Require Import List Arith PArith NArith Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Program Require Import CfgSig VarsSig.
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

  Definition c_vars : N := 1%N. (* STUB *)

  (** Universe preparation pays for each encoded occurrence lookup. *)
  Lemma T_universe_le : forall p,
    (T_universe p <= c_vars * universe_work p)%N.
  Proof. Admitted. (* STUB *)

  (** The universe bound includes every reader, encoding and occurrence width. *)
  Lemma universe_bigO : bigO (fun _ : P.t => True) universe_work T_universe.
  Proof. Admitted. (* STUB *)

  (** Flattening syntax preserves exactly the occurrence predicate. *)
  Lemma F1_occurrences : forall p x, In x (occurrences p) <-> occurs p x.
  Proof.
    apply occurrences_spec.
  Qed.

  (** Deduplicating occurrences gives the prepared variable universe. *)
  Lemma F2_universe : forall p x, In x (universe p) <-> In x (occurrences p).
  Proof.
    apply universe_members.
  Qed.
  Definition seen p :=
    fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p) PTrieCode.empty.
  TimeFun seen.
  Definition k_seen : N := 1%N. (* STUB *)
  Definition k_collect : N := 1%N. (* STUB *)

  Lemma T_uses_le : forall p e,
    (T_uses p e <= c_vars * N.of_nat (E.bits e + length (uses p e) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_defs_le : forall p e,
    (T_defs p e <= c_vars * N.of_nat (E.bits e + length (defs p e) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_exits_le : forall p n,
    (T_exits p n <= c_vars * N.of_nat (N.bits n + length (exits p n) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The named preparation table is the executable occurrence scan. *)
  Lemma F3_seen : forall p,
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
  Lemma F4_seen_nodes : forall p,
    PTrie.nodes (seen p) <= length (occurrences p) * occurrence_width p.
  Proof.
    intro p; unfold seen.
    pose proof (scan_nodes (occurrences p) PTrieCode.empty (occurrence_width p)
      (occurrence_bits p)) as Hnodes.
    exact Hnodes.
  Qed.

  Lemma T1_seen : forall p,
    (T_seen p <= k_seen * universe_work p)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_universe : forall p,
    (T_universe p <= k_collect * (T_seen p +
      N.of_nat (length (occurrences p) + 1) * N.of_nat (occurrence_width p + 1)))%N.
  Proof. Admitted. (* STUB *)
End VarsT.
