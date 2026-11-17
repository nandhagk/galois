(** * Control-flow graph helpers

    Prepare adjacency tables from a client presentation.
    For example, parallel edges remain separate entries in each adjacency list.

    Main results
    - [out_spec] Outgoing adjacency lists exactly the edges with the requested source.
    - [inc_spec] Incoming adjacency lists exactly the edges with the requested destination.
    - [occurrences_project] Projecting occurrence values recovers the original edge list.
    - [occurrences_positions] Occurrence counters form a contiguous sequence.
    - [occurrences_nodup] Occurrence keys distinguish duplicate client edges.
    - [edges_complexity] Edge enumeration is linear in its output, O(n) for n edges.
    - [entries_complexity] Entry enumeration is linear in its output, O(n) for n entries.
    - [out_complexity] Outgoing lookup is linear in the node key and the returned edges, O(|n| + k)
      for k edges.
    - [inc_complexity] Incoming lookup is linear in the node key and the returned edges, O(|n| + k)
      for k edges.
    - [nodes_complexity] Node enumeration is linear in its output, O(n) for n nodes.
    - [prepare_complexity] Preparation is linear in the entries and edges times the widest
      endpoint key.

    Builds on: Program.CfgSig and Graph.Data. *)
From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Graph Require Import Data.
From Galois.Program Require Import CfgSig.
Import List.ListNotations.
Import ComplexityNotations.
Import Code.List.

Fixpoint occurrences {E} (es : list E) (i : nat) : list (E * nat) :=
  match es with
  | [] => []
  | e :: rest => (e, i) :: occurrences rest (S i)
  end.

(** Projecting occurrence values recovers the original edge list. *)
Theorem occurrences_project {E} (es : list E) i : map fst (occurrences es i) = es.
Proof.
  revert i; induction es as [|e es IH]; intro i; cbn [occurrences map fst];
    rewrite ?IH; reflexivity.
Qed.

(** Occurrence counters form a contiguous sequence. *)
Theorem occurrences_positions {E} (es : list E) i :
  map snd (occurrences es i) = seq i (length es).
Proof.
  revert i; induction es as [|e es IH]; intro i; cbn [occurrences map snd seq length];
    rewrite ?IH; reflexivity.
Qed.

(** Occurrence keys distinguish duplicate client edges. *)
Theorem occurrences_nodup {E} (es : list E) i : NoDup (occurrences es i).
Proof.
  apply (NoDup_map_inv snd); rewrite occurrences_positions; apply seq_NoDup.
Qed.

Record cfg_prepared (P N E : Type) := CfgPrepared {
  cfg_program : P;
  cfg_nodes : list N;
  cfg_out : ptrie (list E);
  cfg_inc : ptrie (list E)
}.

Arguments CfgPrepared {P N E} _ _ _ _.
Arguments cfg_program {P N E} _.
Arguments cfg_nodes {P N E} _.
Arguments cfg_out {P N E} _.
Arguments cfg_inc {P N E} _.

Definition cfg_add {A} (k : positive) (x : A) (m : ptrie (list A)) :=
  PTrieCode.set k (x :: match trie_get k m with Some xs => xs | None => [] end) m.

TimeFun cfg_add.

Definition cfg_distinct {A} (encode : A -> positive) (xs : list A) : list A :=
  rev_append (snd (fold_left (fun acc x =>
    let c := encode x in
    match trie_get c (fst acc) with
    | Some _ => acc
    | None => (PTrieCode.set c tt (fst acc), x :: snd acc)
    end) xs (Empty, []))) [].

TimeFun cfg_distinct.

(** The seen-key trie agrees with the distinct values accumulated so far. *)
Lemma cfg_distinct_fold {A} (encode : A -> positive)
    (Hinj : forall x y, encode x = encode y -> x = y) :
  forall xs (m : ptrie unit) ys,
    NoDup ys ->
    (forall x, trie_get (encode x) m = Some tt <-> In x ys) ->
    let acc := fold_left (fun acc x =>
      let c := encode x in
      match trie_get c (fst acc) with
      | Some _ => acc
      | None => (PTrieCode.set c tt (fst acc), x :: snd acc)
      end) xs (m, ys) in
    NoDup (snd acc) /\ forall x, In x (snd acc) <-> In x xs \/ In x ys.
Proof.
  induction xs as [|a xs IH]; intros m ys Hnodup Hseen.
  - cbn [fold_left snd In]. split; [exact Hnodup | tauto].
  - cbn [fold_left fst snd].
    destruct (trie_get (encode a) m) as [[]|] eqn:Ha.
    + destruct (IH m ys Hnodup Hseen) as [Hnd Hmem].
      split; [exact Hnd |]. intro x. rewrite Hmem.
      pose proof (proj1 (Hseen a) Ha) as Hin.
      cbn [In]. split.
      * tauto.
      * intros [[Hax | Hxs] | Hys]; [subst x; tauto | tauto | tauto].
    + assert (Hnew : NoDup (a :: ys)).
      { constructor; [|exact Hnodup]. intro Hin.
        apply (proj2 (Hseen a)) in Hin. congruence. }
      assert (Hseen' : forall x,
        trie_get (encode x) (PTrieCode.set (encode a) tt m) = Some tt <->
        In x (a :: ys)).
      { intro x. destruct (Pos.eq_dec (encode x) (encode a)) as [Heq | Hneq].
        - apply Hinj in Heq; subst x.
          change (PTrie.get (encode a) (PTrie.set (encode a) tt m) = Some tt <->
            In a (a :: ys)).
          rewrite PTrie.get_set_same. cbn [In]. tauto.
        - change (PTrie.get (encode x) (PTrie.set (encode a) tt m) = Some tt <->
            In x (a :: ys)).
          rewrite PTrie.get_set_other by exact Hneq.
          change (trie_get (encode x) m = Some tt <-> In x (a :: ys)).
          rewrite Hseen. cbn [In]. split; [tauto |].
          intros [Hax | Hin]; [subst x; contradiction | exact Hin]. }
      destruct (IH (PTrieCode.set (encode a) tt m) (a :: ys) Hnew Hseen')
        as [Hnd Hmem].
      split; [exact Hnd |]. intro x. rewrite Hmem. cbn [In]. tauto.
Qed.

(** Deduplication retains exactly the input values and removes every duplicate. *)
Lemma cfg_distinct_spec {A} (encode : A -> positive)
    (Hinj : forall x y, encode x = encode y -> x = y) xs :
  NoDup (cfg_distinct encode xs) /\
    forall x, In x (cfg_distinct encode xs) <-> In x xs.
Proof.
  assert (Hseen : forall x, trie_get (encode x) Empty = Some tt <-> In x []).
  { intro x. change (PTrie.get (encode x) PTrie.empty = Some tt <-> False).
    rewrite PTrie.get_empty. split; [discriminate | contradiction]. }
  destruct (cfg_distinct_fold encode Hinj xs Empty [] (NoDup_nil _) Hseen)
    as [Hnd Hmem].
  unfold cfg_distinct. rewrite rev_append_rev, app_nil_r.
  split; [now apply NoDup_rev |]. intro x. rewrite <- in_rev, Hmem. cbn [In]. tauto.
Qed.

(** A bucket contains exactly the listed values whose encoded key selects it. *)
Lemma cfg_bucket_spec {A} (key : A -> positive) xs k x :
  In x (match trie_get k
    (fold_right (fun a m => cfg_add (key a) a m) Empty xs) with
    | Some ys => ys
    | None => []
    end) <-> In x xs /\ key x = k.
Proof.
  induction xs as [|a xs IH].
  - cbn [fold_right]. change (In x (match PTrie.get k PTrie.empty with
      | Some ys => ys | None => [] end) <-> In x [] /\ key x = k).
    rewrite PTrie.get_empty. cbn [In]. tauto.
  - cbn [fold_right]. unfold cfg_add.
    destruct (Pos.eq_dec k (key a)) as [Heq | Hneq].
    + subst k.
      rewrite PTrie.get_set_same. cbn [In]. rewrite IH.
      split.
      * intros [Hax | [Hin Hkey]]; [subst x; auto | auto].
      * intros [[Hax | Hin] Hkey]; [left; exact Hax | right; auto].
    + rewrite PTrie.get_set_other by exact Hneq. rewrite IH. cbn [In].
      split; [tauto |]. intros [[Hax | Hin] Hkey].
      * subst x. congruence.
      * auto.
Qed.

(** Distinct accumulation adds at most one value per input element. *)
Lemma cfg_distinct_fold_length {A} (encode : A -> positive) xs :
  forall (m : ptrie unit) ys,
    length (snd (fold_left (fun acc x =>
      let c := encode x in
      match trie_get c (fst acc) with
      | Some _ => acc
      | None => (PTrieCode.set c tt (fst acc), x :: snd acc)
      end) xs (m, ys))) <= length xs + length ys.
Proof.
  induction xs as [|x xs IH]; intros m ys; cbn [fold_left fst snd length].
  - lia.
  - destruct (trie_get (encode x) m).
    + eapply Nat.le_trans; [apply IH | lia].
    + eapply Nat.le_trans; [apply IH | cbn [length]; lia].
Qed.

(** A fold only needs callback bounds for the elements that it visits. *)
Lemma cfg_fold_left_time {A B} (f : A -> B -> A) (T_f : A -> B -> N) k xs :
  forall a, (forall a x, In x xs -> (T_f a x <= k)%N) ->
    (List.T_fold_left f T_f xs a <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; intros a Hf.
  - time_step.
  - pose proof (Hf a x (or_introl eq_refl)) as Hhead.
    assert (Htail :
      (List.T_fold_left f T_f xs (f a x) <= (k + 1) * N.of_nat (length xs) + 1)%N).
    { apply IH. intros acc y Hin. apply Hf. now right. }
    time_step.
Qed.

(** A right fold likewise uses only callback bounds on its input list. *)
Lemma cfg_fold_right_time {A B} (f : B -> A -> A) (T_f : B -> A -> N) k a xs :
  (forall x a, In x xs -> (T_f x a <= k)%N) ->
    (List.T_fold_right f T_f a xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; intro Hf.
  - time_step.
  - pose proof (Hf x (fold_right f a xs) (or_introl eq_refl)) as Hhead.
    assert (Htail :
      (List.T_fold_right f T_f a xs <= (k + 1) * N.of_nat (length xs) + 1)%N).
    { apply IH. intros y acc Hin. apply Hf. now right. }
    time_step.
Qed.

(** Adding an indexed value pays for one lookup and one insertion. *)
Lemma cfg_add_time {A} k (x : A) m :
  (T_cfg_add k x m <=
    (2 * PTrieT.c_trie + 1) * N.of_nat (Pos.size_nat k + 1))%N.
Proof.
  pose proof (PTrieT.T_get_le (list A) k m) as Hget.
  pose proof (PTrieT.T_set_le (list A) k
    (x :: match trie_get k m with Some ys => ys | None => [] end) m) as Hset.
  unfold PTrieT.T_get in Hget. time_unfold @T_cfg_add. nia.
Qed.

(** Deduplication is linear in input count times the largest encoded width. *)
Lemma cfg_distinct_time {A} (encode : A -> positive) (T_encode : A -> N) xs c w :
  (forall x, In x xs -> (T_encode x <= c * N.of_nat (w + 1))%N) ->
  (forall x, In x xs -> Pos.size_nat (encode x) <= w) ->
  (T_cfg_distinct encode T_encode xs <=
    (c + 2 * PTrieT.c_trie + 16) * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
Proof.
  intros Hencode Hbits. unfold T_cfg_distinct.
  match goal with
  | |- context [List.T_fold_left ?f ?Tf ?l ?acc] =>
    assert (Hfold : (List.T_fold_left f Tf l acc <=
      ((c + 2 * PTrieT.c_trie + 8) * N.of_nat (w + 1) + 1) *
        N.of_nat (length xs) + 1)%N)
  end.
  { apply cfg_fold_left_time. intros [m ys] x Hin.
    pose proof (Hencode x Hin) as Henc.
    pose proof (Hbits x Hin) as Hbit.
    pose proof (PTrieT.T_get_le unit (encode x) m) as Hget.
    pose proof (PTrieT.T_set_le unit (encode x) tt m) as Hset.
    unfold PTrieT.T_get in Hget. cbn [fst snd].
    destruct (trie_get (encode x) m); unfold Datatypes.T_fst, Datatypes.T_snd;
      time_cbn; nia. }
  match goal with
  | |- context [List.T_rev_append ?ys []] =>
    pose proof (List.T_rev_append_le ys []) as Hrev
  end.
  pose proof (cfg_distinct_fold_length encode xs Empty []) as Hlen.
  unfold Datatypes.T_snd in *. time_cbn_all. nia.
Qed.

TimeFun cfg_program.
TimeFun cfg_nodes.
TimeFun cfg_out.
TimeFun cfg_inc.

Module CfgCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E).
  Definition nodes p := cfg_distinct N.encode
    (C.entries p ++ flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)).
  Definition graph_of p : digraph :=
    Digraph (map N.encode (nodes p))
      (fold_right (fun e m => cfg_add (N.encode (C.src p e)) (N.encode (C.dst p e)) m)
        Empty (C.edges p)).
  Definition prepare p : cfg_prepared P.t N.t E.t :=
    CfgPrepared p (nodes p)
      (fold_right (fun e m => cfg_add (N.encode (C.src p e)) e m) Empty (C.edges p))
      (fold_right (fun e m => cfg_add (N.encode (C.dst p e)) e m) Empty (C.edges p)).
End CfgCode.

Module PreparedType (P : TYPE) (N : KEY_OPS) (E : TYPE) <: TYPE.
  Definition t := cfg_prepared P.t N.t E.t.
End PreparedType.

Module PreparedCfg (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E).
  Module PT := PreparedType P N E.
  Module Ops <: CFG_OPS PT N E.
    Definition entries (p : PT.t) := C.entries (cfg_program p).
    Definition edges (p : PT.t) := C.edges (cfg_program p).
    Definition src (p : PT.t) := C.src (cfg_program p).
    Definition dst (p : PT.t) := C.dst (cfg_program p).
  End Ops.
  Module Adj <: CFG_ADJ_OPS PT N E Ops.
    Definition nodes := @cfg_nodes P.t N.t E.t.
    Definition out (p : PT.t) n := match trie_get (N.encode n) (cfg_out p) with
      | Some es => es | None => [] end.
    Definition inc (p : PT.t) n := match trie_get (N.encode n) (cfg_inc p) with
      | Some es => es | None => [] end.
  End Adj.
End PreparedCfg.

Module PreparedCfgLaws (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E).
  Module Code := CfgCode P N E C.
  Module PC := PreparedCfg P N E C.
  Module Laws <: CFG PC.PT N E.
  Include PC.Ops.
  Include PC.Adj.

  Definition wf (p : PC.PT.t) := p = Code.prepare (cfg_program p).

  (** Preparation establishes the cache and node correspondence used by the laws. *)
  Lemma prepare_wf : forall p, wf (Code.prepare p).
  Proof.
    reflexivity.
  Qed.

  Lemma nodes_nodup : forall p, wf p -> NoDup (nodes p).
  Proof.
    intros p Hwf. unfold wf in Hwf. rewrite Hwf.
    apply (proj1 (cfg_distinct_spec N.encode N.encode_inj _)).
  Qed.

  Lemma entries_nodes : forall p n, wf p -> In n (entries p) -> In n (nodes p).
  Proof.
    intros p n Hwf Hin. unfold wf in Hwf. rewrite Hwf.
    apply (proj2 (cfg_distinct_spec N.encode N.encode_inj _) n).
    apply in_or_app. left. exact Hin.
  Qed.

  Lemma edges_nodes : forall p e, wf p -> In e (edges p) ->
    In (src p e) (nodes p) /\ In (dst p e) (nodes p).
  Proof.
    intros p e Hwf Hin. unfold wf in Hwf. rewrite Hwf.
    split; apply (proj2 (cfg_distinct_spec N.encode N.encode_inj _));
      apply in_or_app; right; apply in_flat_map; exists e; split;
      [exact Hin | cbn; auto | exact Hin | cbn; auto].
  Qed.

  Lemma out_spec : forall p n e, wf p ->
    (In e (out p n) <-> In e (edges p) /\ src p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold out, edges, src. cbn [Code.prepare cfg_program cfg_out].
    rewrite cfg_bucket_spec. split.
    - intros [Hin Hkey]. split; [exact Hin | now apply N.encode_inj].
    - intros [Hin Hsrc]. split; [exact Hin | now rewrite Hsrc].
  Qed.

  Lemma inc_spec : forall p n e, wf p ->
    (In e (inc p n) <-> In e (edges p) /\ dst p e = n).
  Proof.
    intros p n e Hwf. unfold wf in Hwf. rewrite Hwf.
    unfold inc, edges, dst. cbn [Code.prepare cfg_program cfg_inc].
    rewrite cfg_bucket_spec. split.
    - intros [Hin Hkey]. split; [exact Hin | now apply N.encode_inj].
    - intros [Hin Hdst]. split; [exact Hin | now rewrite Hdst].
  Qed.
  End Laws.
  Include Laws.
End PreparedCfgLaws.

Module CfgT (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_BASE_T P N E).
  Module PT := PreparedType P N E.
  Module Timed <: CFG_PREPARE_TIME P PT N E C.
  Include CfgCode P N E C.
  TimeFun nodes.
  TimeFun graph_of.
  TimeFun prepare.
  Definition c_cfg_prep : N :=
    (128 * (C.c_cfg + N.c_key + PTrieT.c_trie + 1))%N.

  (** Every listed node width is bounded by the list's maximum width. *)
  Local Lemma node_width_member xs x :
    In x xs -> N.bits x <= fold_right Nat.max 0%nat (map N.bits xs).
  Proof.
    induction xs as [|y ys IH]; cbn [In map fold_right].
    - contradiction.
    - intros [Heq | Hin].
      + subst x. apply Nat.le_max_l.
      + eapply Nat.le_trans; [now apply IH | apply Nat.le_max_r].
  Qed.

  (** Enumerating an edge's two endpoints doubles the edge-list length. *)
  Local Lemma endpoints_length p es :
    length (flat_map (fun e => [C.src p e; C.dst p e]) es) = 2 * length es.
  Proof.
    induction es as [|e es IH]; cbn [flat_map app length]; lia.
  Qed.

  (** Endpoint enumeration pays a fixed charge and the two projections per edge. *)
  Local Lemma endpoints_time p es :
    (Code.List.T_flat_map (fun e => [C.src p e; C.dst p e])
      (fun e => 1 + (C.T_src p e + C.T_dst p e)) es <=
      (2 * C.c_cfg + 5) * N.of_nat (length es) + 1)%N.
  Proof.
    induction es as [|e es IH].
    - time_step.
    - pose proof (C.T_src_le p e) as Hsrc.
      pose proof (C.T_dst_le p e) as Hdst.
      pose proof (Datatypes.T_app_le [C.src p e; C.dst p e]
        (flat_map (fun e => [C.src p e; C.dst p e]) es)) as Happ.
      time_unfold @Code.List.T_flat_map. time_cbn_all. nia.
  Qed.

  (** A per-item bound fits any larger count and positive width budget. *)
  Local Lemma product_budget (cost c u a l w : N) :
    (cost <= c * u)%N -> (c <= a)%N -> (u <= l)%N -> (1 <= w)%N ->
    (cost <= a * l * w)%N.
  Proof.
    intros Hcost Hc Hu Hw.
    eapply N.le_trans; [exact Hcost |].
    eapply N.le_trans.
    - apply N.mul_le_mono; [exact Hc | exact Hu].
    - rewrite <- (N.mul_1_r (a * l)) at 1.
      apply N.mul_le_mono_l. exact Hw.
  Qed.

  (** Deduplication fits the preparation budget for entries and edge endpoints. *)
  Local Lemma distinct_nodes_time p :
    (T_cfg_distinct N.encode (fun x => N.T_encode x) (C.entries p ++
      flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)) <=
      32 * (C.c_cfg + N.c_key + PTrieT.c_trie + 1) *
      N.of_nat (length (C.entries p) + length (C.edges p) + 1) *
      N.of_nat (fold_right Nat.max 0%nat (map N.bits (C.entries p ++
        flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p))) + 1))%N.
  Proof.
    set (ns := C.entries p ++
      flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)).
    set (w := fold_right Nat.max 0%nat (map N.bits ns)).
    assert (Hwidth : forall x, In x ns -> N.bits x <= w).
    { intros x Hin. now apply node_width_member. }
    assert (Hdistinct : (T_cfg_distinct N.encode (fun x => N.T_encode x) ns <=
      (N.c_key + 2 * PTrieT.c_trie + 16) * N.of_nat (length ns + 1) *
        N.of_nat (w + 1))%N).
    { apply cfg_distinct_time.
      - intros x Hin. pose proof (N.T_encode_le x) as Henc.
        pose proof (Hwidth x Hin) as Hbit. nia.
      - exact Hwidth. }
    assert (Hlength : length ns = length (C.entries p) + 2 * length (C.edges p)).
    { unfold ns. rewrite length_app, endpoints_length. reflexivity. }
    set (a := (C.c_cfg + N.c_key + PTrieT.c_trie + 1)%N).
    set (l := N.of_nat (length (C.entries p) + length (C.edges p) + 1)).
    assert (Hcount : (N.of_nat (length ns + 1) <= 2 * l)%N).
    { unfold l. lia. }
    eapply N.le_trans; [exact Hdistinct |].
    apply N.mul_le_mono_r.
    eapply N.le_trans.
    - apply N.mul_le_mono_l. exact Hcount.
    - rewrite N.mul_assoc. apply N.mul_le_mono_r. unfold a. lia.
  Qed.

  (** Node preparation charges enumeration and width-bounded deduplication. *)
  Local Lemma nodes_time p :
    (T_nodes p <= 64 * (C.c_cfg + N.c_key + PTrieT.c_trie + 1) *
      N.of_nat (length (C.entries p) + length (C.edges p) + 1) *
      N.of_nat (fold_right Nat.max 0%nat (map N.bits (C.entries p ++
        flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p))) + 1))%N.
  Proof.
    set (ns := C.entries p ++
      flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)).
    set (w := fold_right Nat.max 0%nat (map N.bits ns)).
    pose proof (endpoints_time p (C.edges p)) as Hflat.
    pose proof (C.T_entries_le p) as Hentries.
    pose proof (C.T_edges_le p) as Hedges.
    pose proof (Datatypes.T_app_le (C.entries p)
      (flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p))) as Happ.
    set (a := (C.c_cfg + N.c_key + PTrieT.c_trie + 1)%N).
    set (l := N.of_nat (length (C.entries p) + length (C.edges p) + 1)).
    set (width := N.of_nat (w + 1)).
    pose proof (distinct_nodes_time p) as Hdistinct_bound.
    change (T_cfg_distinct N.encode (fun x => N.T_encode x) ns <=
      32 * a * l * width)%N in Hdistinct_bound.
    assert (Ha : (1 <= a)%N) by (unfold a; lia).
    assert (Hl : (1 <= l)%N) by (unfold l; lia).
    assert (Hw : (1 <= width)%N) by (unfold width; lia).
    assert (Hbudget : (1 <= a * l * width)%N).
    { change (1 * 1 * 1 <= a * l * width)%N.
      apply N.mul_le_mono; [now apply N.mul_le_mono | exact Hw]. }
    assert (Hentries_bound : (C.T_entries p <= a * l * width)%N).
    { eapply product_budget; [exact Hentries | unfold a; lia | unfold l; lia | exact Hw]. }
    assert (Hedges_bound : (C.T_edges p <= a * l * width)%N).
    { eapply product_budget; [exact Hedges | unfold a; lia | unfold l; lia | exact Hw]. }
    assert (Hflat_part :
      ((2 * C.c_cfg + 5) * N.of_nat (length (C.edges p)) <= 7 * a * l * width)%N).
    { eapply product_budget; [reflexivity | unfold a; lia | unfold l; lia | exact Hw]. }
    assert (Happ_bound : (Datatypes.T_app (C.entries p)
      (flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)) <= a * l * width)%N).
    { eapply product_budget with (c := 1%N) (u := (N.of_nat (length (C.entries p)) + 1)%N).
      - lia.
      - exact Ha.
      - unfold l. lia.
      - exact Hw. }
    unfold T_nodes. fold ns. fold w. fold a. fold l. fold width.
    rewrite <- !N.mul_assoc in Hbudget, Hdistinct_bound, Hentries_bound,
      Hedges_bound, Hflat_part, Happ_bound |- *.
    lia.
  Qed.

  (** Index construction pays the key and trie costs of each listed edge. *)
  Local Lemma index_time (key : E.t -> N.t) (T_key : E.t -> N) es w :
    (forall e, In e es -> (T_key e <= C.c_cfg)%N) ->
    (forall e, In e es -> N.bits (key e) <= w) ->
    (List.T_fold_right
      (fun e m => cfg_add (N.encode (key e)) e m)
      (fun e m => 1 + (T_key e + N.T_encode (key e) +
        T_cfg_add (N.encode (key e)) e m)) Empty es <=
      8 * (C.c_cfg + N.c_key + PTrieT.c_trie + 1) *
        N.of_nat (length es + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hkey Hbits.
    eapply N.le_trans.
    - apply cfg_fold_right_time with
        (k := ((C.c_cfg + N.c_key + 2 * PTrieT.c_trie + 4) *
          N.of_nat (w + 1))%N).
      intros e m Hin.
      pose proof (Hkey e Hin) as Hproj.
      pose proof (Hbits e Hin) as Hbit.
      pose proof (N.T_encode_le (key e)) as Henc.
      pose proof (cfg_add_time (N.encode (key e)) e m) as Hadd.
      change (T_cfg_add (N.encode (key e)) e m <=
        (2 * PTrieT.c_trie + 1) * N.of_nat (N.bits (key e) + 1))%N in Hadd.
      nia.
    - nia.
  Qed.

  (** Listed edge endpoints are included in the maximum preparation width. *)
  Local Lemma endpoints_width p e :
    In e (C.edges p) ->
    let w := fold_right Nat.max 0%nat (map N.bits (C.entries p ++
      flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p))) in
    N.bits (C.src p e) <= w /\ N.bits (C.dst p e) <= w.
  Proof.
    intro Hin. split; apply node_width_member; apply in_or_app; right;
      apply in_flat_map; exists e; split;
      [exact Hin | cbn; auto | exact Hin | cbn; auto].
  Qed.

  (** Preparation pays for every indexed endpoint and entry. *)
  Lemma T_prepare_le : forall p,
    (T_prepare p <= c_cfg_prep * N.of_nat (length (C.entries p) + length (C.edges p) + 1) *
      N.of_nat (fold_right Nat.max 0%nat (List.map N.bits (C.entries p ++
        flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))) + 1))%N.
  Proof.
    intro p.
    set (w := fold_right Nat.max 0%nat (map N.bits (C.entries p ++
      flat_map (fun e => [C.src p e; C.dst p e]) (C.edges p)))).
    assert (Hsrc : forall e, In e (C.edges p) -> N.bits (C.src p e) <= w).
    { intros e Hin. exact (proj1 (endpoints_width p e Hin)). }
    assert (Hdst : forall e, In e (C.edges p) -> N.bits (C.dst p e) <= w).
    { intros e Hin. exact (proj2 (endpoints_width p e Hin)). }
    pose proof (index_time (C.src p) (C.T_src p) (C.edges p) w
      (fun e _ => C.T_src_le p e) Hsrc) as Hout.
    pose proof (index_time (C.dst p) (C.T_dst p) (C.edges p) w
      (fun e _ => C.T_dst_le p e) Hdst) as Hinc.
    pose proof (nodes_time p) as Hnodes. fold w in Hnodes.
    pose proof (C.T_edges_le p) as Hedges.
    unfold T_prepare, c_cfg_prep. fold w. nia.
  Qed.

  (** Preparation is linear in the entries and edges times the widest endpoint key. *)
  Lemma prepare_complexity :
    T_prepare p ∈ 𝑂(N.of_nat ((length (C.entries p) + length (C.edges p) + 1) *
      (fold_right Nat.max 0%nat (List.map N.bits (C.entries p ++
        flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))) + 1)))
      for p.
  Proof.
    apply bigO_intro with (c := c_cfg_prep).
    intros p _. pose proof (T_prepare_le p) as Hprepare.
    rewrite Nat2N.inj_mul. nia.
  Qed.
  End Timed.
  Include Timed.
End CfgT.
