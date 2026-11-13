(** * Stored database operations

    Databases store rows and identifier equalities.
    For example, an initialized database supplies indexes on request.
    Builds on: DatabaseSig. *)

From Stdlib Require Import List PArith NArith PeanoNat Bool Lia Relations.Relation_Operators
  Sorting.Permutation Sorting.Sorted.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Code Loop UnionFind Trie Key Map.
From Galois.Egglog Require Import ValueSig IndexSig Syntax Model DatabaseSig ModelFacts.

Import List.ListNotations.

Module Pos.
  TimeFun Pos.max.
End Pos.

Module N.
  TimeFun N.of_nat N.max.
End N.

(** Sorted positions retain their original positive ranks in a projection. *)
Record database_slot_layout := {
  ranked_positions : list (nat * positive);
  projection_steps : list (nat * positive)
}.

TimeFun ranked_positions.
TimeFun projection_steps.

Fixpoint slot_rank_insert (p : nat * positive) (ps : list (nat * positive))
    : list (nat * positive) :=
  match ps with
  | [] => [p]
  | q :: rest =>
    if Nat.leb (fst p) (fst q) then p :: ps else q :: slot_rank_insert p rest
  end.

TimeFun slot_rank_insert.

Fixpoint slot_rank_positions (rank : positive) (perm : list nat) : list (nat * positive) :=
  match perm with
  | [] => []
  | p :: rest => slot_rank_insert (p, rank) (slot_rank_positions (Pos.succ rank) rest)
  end.

TimeFun slot_rank_positions.

Fixpoint slot_position_difference (position previous : nat) : nat :=
  match previous, position with
  | 0, _ => position
  | S before, S current => slot_position_difference current before
  | S _, 0 => 0
  end.

TimeFun slot_position_difference.

(** A gap is measured from the preceding selected position, starting at zero. *)
Fixpoint slot_position_gaps (previous : nat) (ps : list (nat * positive))
    : list (nat * positive) :=
  match ps with
  | [] => []
  | (p, rank) :: rest =>
    (slot_position_difference p previous, rank) :: slot_position_gaps p rest
  end.

TimeFun slot_position_gaps.

Definition prepare_slot_layout (perm : list nat) : database_slot_layout :=
  let positions := slot_rank_positions 1 perm in
  {| ranked_positions := positions; projection_steps := slot_position_gaps 0 positions |}.

TimeFun prepare_slot_layout.

Definition prepare_slot_layouts (sl : list (positive * list nat))
    : list (positive * database_slot_layout) :=
  map (fun s => (fst s, prepare_slot_layout (snd s))) sl.

TimeFun prepare_slot_layouts.

Fixpoint slot_skip {C : Type} (gap : nat) (u : list C) : list C :=
  match gap, u with
  | 0, _ => u
  | S n, _ :: rest => slot_skip n rest
  | S _, [] => []
  end.

TimeFun slot_skip.

(** Each gap advances the remaining tuple and saves its head at the original rank. *)
Fixpoint slot_pick_ranked {C : Type} (steps : list (nat * positive)) (u : list C)
    (picked : PTrieCode.t C) : PTrieCode.t C :=
  match steps with
  | [] => picked
  | (gap, rank) :: rest =>
    let suffix := slot_skip gap u in
    match suffix with
    | [] => picked
    | c :: _ => slot_pick_ranked rest suffix (PTrieCode.set rank c picked)
    end
  end.

TimeFun slot_pick_ranked.

(** Reading increasing original ranks restores permutation order. *)
Fixpoint slot_read_ranked {C : Type} (remaining : nat) (rank : positive)
    (picked : PTrieCode.t C) : list C :=
  match remaining with
  | 0 => []
  | S n =>
    match PTrieCode.get rank picked with
    | None => slot_read_ranked n (Pos.succ rank) picked
    | Some c => c :: slot_read_ranked n (Pos.succ rank) picked
    end
  end.

TimeFun slot_read_ranked.

Definition project_slot_layout {C : Type} (layout : database_slot_layout) (u : list C)
    : list C :=
  slot_read_ranked (length (projection_steps layout)) 1
    (slot_pick_ranked (projection_steps layout) u PTrieCode.empty).

TimeFun project_slot_layout.

(** * Prepared projection facts *)

(** Sorting one pair retains precisely that pair and the old entries. *)
Lemma slot_rank_insert_in : forall p ps q,
  In q (slot_rank_insert p ps) <-> q = p \/ In q ps.
Proof.
  intros p ps. induction ps as [| a ps IH]; intro q; cbn [slot_rank_insert].
  - cbn. intuition congruence.
  - destruct (Nat.leb (fst p) (fst a)); cbn [In].
    + intuition congruence.
    + rewrite IH. intuition congruence.
Qed.

(** Insertion adds one ranked position. *)
Lemma slot_rank_insert_length : forall p ps,
  length (slot_rank_insert p ps) = S (length ps).
Proof.
  intros p ps. induction ps as [| a ps IH]; cbn [slot_rank_insert].
  - reflexivity.
  - destruct (Nat.leb (fst p) (fst a)); cbn [length]; congruence.
Qed.

(** Ranking preserves the number of requested positions. *)
Lemma slot_rank_positions_length : forall rank perm,
  length (slot_rank_positions rank perm) = length perm.
Proof.
  intros rank perm. revert rank. induction perm as [| p perm IH]; intro rank.
  - reflexivity.
  - cbn [slot_rank_positions length]. rewrite slot_rank_insert_length, IH. reflexivity.
Qed.

(** Replacing positions with gaps preserves their number. *)
Lemma slot_position_gaps_length : forall previous ps,
  length (slot_position_gaps previous ps) = length ps.
Proof.
  intros previous ps. revert previous. induction ps as [| [p rank] ps IH]; intro previous.
  - reflexivity.
  - cbn [slot_position_gaps length]. now rewrite IH.
Qed.

(** A stored gap is the truncated difference of its endpoint positions. *)
Lemma slot_position_difference_sub : forall position previous,
  slot_position_difference position previous = position - previous.
Proof.
  intros position previous. revert position.
  induction previous as [| previous IH]; intros [| position]; cbn; auto.
Qed.

(** Scanning a gap returns the corresponding list suffix. *)
Lemma slot_skip_spec : forall C gap (u : list C), slot_skip gap u = skipn gap u.
Proof.
  intros C gap. induction gap as [| gap IH]; intros [| c u]; cbn; auto.
Qed.

(** A scan leaves bindings of ranks outside its steps unchanged. *)
Lemma slot_pick_ranked_other : forall C steps (u : list C) picked rank,
  ~ In rank (map snd steps) ->
  PTrieCode.get rank (slot_pick_ranked steps u picked) = PTrieCode.get rank picked.
Proof.
  intros C steps. induction steps as [| [gap r] steps IH]; intros u picked rank Habsent.
  - reflexivity.
  - cbn [slot_pick_ranked]. destruct (slot_skip gap u) as [| c rest].
    + reflexivity.
    + rewrite IH.
      * apply PTrie.get_set_other. intro Heq. apply Habsent. cbn. now left.
      * intro Hin. apply Habsent. cbn. now right.
Qed.

(** Insertion changes only the order of the ranked entries. *)
Lemma slot_rank_insert_perm : forall p ps,
  Permutation (p :: ps) (slot_rank_insert p ps).
Proof.
  intros p ps. induction ps as [| a ps IH]; cbn [slot_rank_insert].
  - reflexivity.
  - destruct (Nat.leb (fst p) (fst a)).
    + reflexivity.
    + eapply perm_trans; [apply perm_swap | now apply perm_skip].
Qed.

(** Insertion keeps absolute positions in increasing order. *)
Lemma slot_rank_insert_sorted : forall p ps,
  StronglySorted (fun a b => fst a <= fst b) ps ->
  StronglySorted (fun a b => fst a <= fst b) (slot_rank_insert p ps).
Proof.
  intros p ps Hsorted. induction Hsorted as [| a ps Hsorted IH Hlower].
  - cbn [slot_rank_insert]. constructor; constructor.
  - cbn [slot_rank_insert]. destruct (Nat.leb (fst p) (fst a)) eqn:Hle.
    + apply Nat.leb_le in Hle. constructor.
      * constructor; assumption.
      * constructor; [exact Hle |].
        eapply Forall_impl; [| exact Hlower]. intros q Hq. cbn in *. lia.
    + apply Nat.leb_gt in Hle. constructor; [exact IH |].
      apply Forall_forall. intros q Hin. apply slot_rank_insert_in in Hin.
      destruct Hin as [-> | Hin]; [cbn; lia |].
      rewrite Forall_forall in Hlower. exact (Hlower q Hin).
Qed.

(** Prepared absolute positions are increasing even when positions repeat. *)
Lemma slot_rank_positions_sorted : forall rank perm,
  StronglySorted (fun a b => fst a <= fst b) (slot_rank_positions rank perm).
Proof.
  intros rank perm. revert rank. induction perm as [| p perm IH]; intro rank.
  - constructor.
  - cbn [slot_rank_positions]. apply slot_rank_insert_sorted. apply IH.
Qed.

(** Every ranked entry retains its source position and a rank above its starting rank. *)
Lemma slot_rank_positions_origin : forall rank perm p r,
  In (p, r) (slot_rank_positions rank perm) ->
  In p perm /\ Pos.to_nat rank <= Pos.to_nat r.
Proof.
  intros rank perm. revert rank. induction perm as [| a perm IH]; intros rank p r Hin.
  - contradiction.
  - cbn [slot_rank_positions] in Hin. apply slot_rank_insert_in in Hin.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst. split; [now left | lia].
    + destruct (IH (Pos.succ rank) p r Hin) as [Hposition Hrank].
      split; [now right |]. rewrite Pos2Nat.inj_succ in Hrank. lia.
Qed.

(** Original ranks remain distinct after sorting, including repeated source positions. *)
Lemma slot_rank_positions_nodup : forall rank perm,
  NoDup (map snd (slot_rank_positions rank perm)).
Proof.
  intros rank perm. revert rank. induction perm as [| p perm IH]; intro rank.
  - constructor.
  - cbn [slot_rank_positions]. eapply Permutation_NoDup.
    + apply Permutation_map. apply slot_rank_insert_perm.
    + cbn [map snd]. constructor; [| apply IH].
      intro Hin. apply in_map_iff in Hin. destruct Hin as [[q r] [Heq Hin]].
      cbn in Heq. subst r.
      destruct (slot_rank_positions_origin (Pos.succ rank) perm q rank Hin) as [_ Hrank].
      rewrite Pos2Nat.inj_succ in Hrank. lia.
Qed.

(** Gap construction does not change the original ranks. *)
Lemma slot_position_gaps_ranks : forall previous ps,
  map snd (slot_position_gaps previous ps) = map snd ps.
Proof.
  intros previous ps. revert previous. induction ps as [| [p rank] ps IH]; intro previous.
  - reflexivity.
  - cbn [slot_position_gaps map snd]. now rewrite IH.
Qed.

(** Advancing by a nonnegative position gap reaches its absolute tuple suffix. *)
Lemma slot_skip_gap : forall C previous position (u : list C), previous <= position ->
  slot_skip (slot_position_difference position previous) (skipn previous u) = skipn position u.
Proof.
  intros C previous position u Hle.
  rewrite slot_skip_spec, slot_position_difference_sub, skipn_skipn. f_equal. lia.
Qed.

(** The tuple scan saves each fitting position at its unique original rank. *)
Lemma slot_pick_ranked_spec : forall C (u : list C) ps previous picked,
  StronglySorted (fun a b => fst a <= fst b) ps ->
  Forall (fun q => previous <= fst q) ps ->
  Forall (fun q => fst q < length u) ps -> NoDup (map snd ps) ->
  forall p rank, In (p, rank) ps ->
  PTrieCode.get rank
    (slot_pick_ranked (slot_position_gaps previous ps) (skipn previous u) picked) =
      nth_error u p.
Proof.
  intros C u ps. induction ps as [| [position r] ps IH];
    intros previous picked Hsorted Hlower Hfits Hdistinct p rank Hin.
  - contradiction.
  - apply StronglySorted_inv in Hsorted as [Hsorted Hnext].
    inversion Hlower as [| ? ? Hbefore Hlower']; subst.
    inversion Hfits as [| ? ? Hinside Hfits']; subst.
    cbn [map snd] in Hdistinct.
    inversion Hdistinct as [| ? ? Habsent Hdistinct']; subst.
    cbn [fst] in Hbefore, Hinside.
    cbn [slot_position_gaps slot_pick_ranked]. rewrite slot_skip_gap by exact Hbefore.
    destruct (skipn position u) as [| c suffix] eqn:Hsuffix.
    + pose proof (length_skipn position u) as Hlength.
      rewrite Hsuffix in Hlength. cbn in Hlength. lia.
    + destruct Hin as [Heq | Hin].
      * injection Heq as Heqpos Heqrank. subst p rank.
        rewrite slot_pick_ranked_other.
        -- rewrite PTrie.get_set_same.
           pose proof (nth_error_skipn position u 0) as Hnth.
           rewrite Hsuffix, Nat.add_0_r in Hnth. exact Hnth.
        -- rewrite slot_position_gaps_ranks. exact Habsent.
      * rewrite <- Hsuffix. eapply IH; eassumption.
Qed.

(** Reading original ranks recovers the source order of every recorded position. *)
Lemma slot_read_ranked_spec : forall C (u : list C) perm rank picked,
  (forall p r, In (p, r) (slot_rank_positions rank perm) ->
    PTrieCode.get r picked = nth_error u p) ->
  slot_read_ranked (length perm) rank picked =
    flat_map (fun p => option_list (nth_error u p)) perm.
Proof.
  intros C u perm. induction perm as [| p perm IH]; intros rank picked Hagree.
  - reflexivity.
  - assert (Hhead : PTrieCode.get rank picked = nth_error u p).
    { apply Hagree. cbn [slot_rank_positions]. apply slot_rank_insert_in. now left. }
    assert (Htail : slot_read_ranked (length perm) (Pos.succ rank) picked =
      flat_map (fun p => option_list (nth_error u p)) perm).
    { apply IH. intros q r Hin. apply Hagree. cbn [slot_rank_positions].
      apply slot_rank_insert_in. now right. }
    cbn [length slot_read_ranked flat_map]. rewrite Hhead, Htail.
    destruct (nth_error u p); reflexivity.
Qed.

(** A prepared projection restores the requested order, including repeated fitting positions. *)
Theorem project_slot_layout_correct : forall C perm (u : list C),
  Forall (fun p => p < length u) perm ->
  project_slot_layout (prepare_slot_layout perm) u =
    flat_map (fun p => option_list (nth_error u p)) perm.
Proof.
  intros C perm u Hfits. unfold project_slot_layout, prepare_slot_layout.
  cbn [projection_steps]. rewrite slot_position_gaps_length, slot_rank_positions_length.
  apply slot_read_ranked_spec. intros p rank Hin.
  eapply (slot_pick_ranked_spec C u (slot_rank_positions 1 perm) 0 PTrieCode.empty).
  - apply slot_rank_positions_sorted.
  - apply Forall_forall. intros [q r] _. cbn. lia.
  - apply Forall_forall. intros [q r] Hq. cbn [fst].
    rewrite Forall_forall in Hfits. apply Hfits.
    exact (proj1 (slot_rank_positions_origin 1 perm q r Hq)).
  - apply slot_rank_positions_nodup.
  - exact Hin.
Qed.

(** * Preparation costs *)

(** Computing a gap charges at most one call per unit of its endpoint. *)
Lemma T_slot_position_difference_le : forall position previous,
  (T_slot_position_difference position previous <= N.of_nat (position + 1))%N.
Proof.
  intro position. induction position as [| position IH]; intros [| previous];
    time_step slot_position_difference.
Qed.

(** Scanning a gap charges at most one call per skipped cell. *)
Lemma T_slot_skip_le : forall C gap (u : list C),
  (T_slot_skip gap u <= N.of_nat (gap + 1))%N.
Proof.
  intros C gap. induction gap as [| gap IH]; intros [| c u]; time_step.
Qed.

(** Insertion reads each existing position once with a comparison bounded by the new position. *)
Lemma T_slot_rank_insert_le : forall p ps,
  (T_slot_rank_insert p ps <= N.of_nat ((length ps + 1) * (fst p + 5)))%N.
Proof.
  intros p ps. induction ps as [| q ps IH]; time_step slot_rank_insert.
Qed.

(** Sorting one entry preserves the sum of unary position sizes. *)
Lemma slot_rank_insert_mass : forall p ps,
  fold_right (fun q n => S (fst q) + n) 0 (slot_rank_insert p ps) =
    S (fst p) + fold_right (fun q n => S (fst q) + n) 0 ps.
Proof.
  intros p ps. induction ps as [| q ps IH]; cbn [slot_rank_insert].
  - reflexivity.
  - destruct (Nat.leb (fst p) (fst q)); cbn [fold_right]; [lia |].
    rewrite IH. lia.
Qed.

(** The sorted positions have exactly the source permutation's unary size. *)
Lemma slot_rank_positions_mass : forall rank perm,
  fold_right (fun q n => S (fst q) + n) 0 (slot_rank_positions rank perm) =
    fold_right Nat.add 0 (map S perm).
Proof.
  intros rank perm. revert rank. induction perm as [| p perm IH]; intro rank.
  - reflexivity.
  - cbn [slot_rank_positions map fold_right]. rewrite slot_rank_insert_mass, IH. reflexivity.
Qed.

(** Gap construction pays the unary size of each absolute position once. *)
Lemma T_slot_position_gaps_le : forall previous ps,
  (T_slot_position_gaps previous ps <=
    N.of_nat (length ps + fold_right (fun q n => (S (fst q) + n)%nat) 0%nat ps + 1))%N.
Proof.
  intros previous ps. revert previous. induction ps as [| [p rank] ps IH];
    intro previous; time_step slot_position_gaps.
Qed.

(** A positive rank's bit length is bounded by its unary value. *)
Local Lemma slot_rank_bits_value : forall rank, Pos.size_nat rank <= Pos.to_nat rank.
Proof.
  intro rank. induction rank as [rank IH | rank IH |]; cbn [Pos.size_nat].
  - rewrite Pos2Nat.inj_xI. lia.
  - rewrite Pos2Nat.inj_xO. pose proof (Pos2Nat.is_pos rank). lia.
  - reflexivity.
Qed.

(** Ranking pays for insertion comparisons and each increasing positive rank. *)
Lemma T_slot_rank_positions_le : forall rank perm,
  (T_slot_rank_positions rank perm <=
    8 * N.of_nat ((length perm + 1) *
      (fold_right Nat.add 0%nat (map S perm) + length perm + Pos.to_nat rank + 1)))%N.
Proof.
  intros rank perm. revert rank. induction perm as [| p perm IH]; intro rank.
  - time_step slot_rank_positions.
  - pose proof (IH (Pos.succ rank)) as Htail.
    pose proof (slot_rank_bits_value rank) as Hbits.
    pose proof (T_slot_rank_insert_le (p, rank)
      (slot_rank_positions (Pos.succ rank) perm)) as Hinsert.
    rewrite slot_rank_positions_length in Hinsert.
    rewrite Pos2Nat.inj_succ in Htail. time_step slot_rank_positions.
Qed.

(** One prepared layout is bounded by the work charged for its source positions. *)
Lemma T_prepare_slot_layout_le : forall perm,
  (T_prepare_slot_layout perm <=
    20 * N.of_nat ((length perm + 1) *
      (fold_right Nat.add 0%nat (map S perm) + length perm + 1)))%N.
Proof.
  intro perm.
  pose proof (T_slot_rank_positions_le 1 perm) as Hrank.
  pose proof (T_slot_position_gaps_le 0 (slot_rank_positions 1 perm)) as Hgap.
  rewrite slot_rank_positions_length, slot_rank_positions_mass in Hgap.
  time_step prepare_slot_layout.
Qed.

(** Preparing the full layout list fits the released aggregate layout-work budget. *)
Lemma T_prepare_slot_layouts_le : forall sl,
  (T_prepare_slot_layouts sl <=
    25 * N.of_nat (layout_work sl + length sl + 1))%N.
Proof.
  intro sl. induction sl as [| [f perm] sl IH]; time_step prepare_slot_layouts; time_step.
  unfold T_prepare_slot_layouts, layout_work in IH.
  revert IH. time_simpl. intro IH. time_cbn_all. nia.
Qed.

(** * Projection costs *)

(** A skip pays for the cells it consumes and one final call. *)
Lemma T_slot_skip_remaining_le : forall C gap (u : list C),
  (T_slot_skip gap u + N.of_nat (length (slot_skip gap u)) <=
    N.of_nat (length u + 1))%N.
Proof.
  intros C gap. induction gap as [| gap IH]; intros [| c u].
  - time_step.
  - time_step.
  - time_step.
  - pose proof (IH u) as Htail. time_step.
Qed.

(** Every original rank lies below the rank immediately after the permutation. *)
Lemma slot_rank_positions_upper : forall first perm p rank,
  In (p, rank) (slot_rank_positions first perm) ->
  Pos.to_nat rank < Pos.to_nat first + length perm.
Proof.
  intros first perm. revert first.
  induction perm as [| q perm IH]; intros first p rank Hin; cbn [slot_rank_positions] in Hin.
  - contradiction.
  - apply slot_rank_insert_in in Hin. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. cbn [length]. lia.
    + specialize (IH (Pos.succ first) p rank Hin).
      rewrite Pos2Nat.inj_succ in IH. cbn [length]. lia.
Qed.

Local Opaque PTrieT.c_trie.

(** Arithmetic below generalizes the released trie constant so simplification cannot
    use its concrete placeholder value. *)

(** The tuple walk charges consumed cells once and one bounded trie write per selected rank. *)
Lemma T_slot_pick_ranked_le : forall C steps (u : list C) picked bits,
  Forall (fun q => Pos.size_nat (snd q) <= bits) steps ->
  (T_slot_pick_ranked steps u picked <= N.of_nat (length u + 1) +
    (PTrieT.c_trie + 2) * N.of_nat (length steps) * N.of_nat (bits + 1))%N.
Proof.
  intros C steps. induction steps as [| [gap rank] steps IH]; intros u picked bits Hbits.
  - time_unfold (@T_slot_pick_ranked). time_simpl. time_cbn.
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost. nia.
  - inversion Hbits as [| q qs Hrank Hrest]; subst.
    pose proof (T_slot_skip_remaining_le C gap u) as Hskip.
    time_unfold (@T_slot_pick_ranked). time_simpl. time_cbn.
    destruct (slot_skip gap u) as [| c suffix] eqn:Hsuffix.
    + time_cbn_all. set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost. nia.
    + pose proof (IH (c :: suffix) (PTrieCode.set rank c picked) bits Hrest) as Htail.
      pose proof (PTrieT.T_set_le C rank c picked) as Hset.
      time_cbn_all. set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost.
      rewrite ?Nat2N.inj_add in *. nia.
Qed.

(** Reading consecutive ranks pays their common upper bit width at each step. *)
Lemma T_slot_read_ranked_le : forall C remaining rank (picked : PTrieCode.t C) limit,
  Pos.to_nat rank + remaining <= Pos.to_nat limit ->
  (T_slot_read_ranked remaining rank picked <=
    (PTrieT.c_trie + 2) * N.of_nat (remaining + 1) * N.of_nat (Pos.size_nat limit + 1))%N.
Proof.
  intros C remaining. induction remaining as [| remaining IH];
    intros rank picked limit Hrange.
  - time_unfold (@T_slot_read_ranked). time_simpl. time_cbn.
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost. nia.
  - assert (Hrank : Pos.size_nat rank <= Pos.size_nat limit).
    { apply Pos.size_nat_monotone. apply Pos2Nat.inj_lt. lia. }
    assert (Hnext : Pos.to_nat (Pos.succ rank) + remaining <= Pos.to_nat limit).
    { rewrite Pos2Nat.inj_succ. lia. }
    pose proof (IH (Pos.succ rank) picked limit Hnext) as Htail.
    pose proof (PTrieT.T_get_le C rank picked) as Hget.
    pose proof (Pos.T_succ_le rank) as Hsucc.
    time_unfold (@T_slot_read_ranked). time_simpl. time_cbn.
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost.
    destruct (PTrieCode.get rank picked); time_cbn_all;
      rewrite ?Nat2N.inj_add in *; nia.
Qed.

(** Prepared ranks use at most the bit width of one plus the permutation length. *)
Lemma slot_prepared_rank_bits : forall perm,
  Forall (fun q => Pos.size_nat (snd q) <= Pos.size_nat (Pos.of_succ_nat (length perm)))
    (projection_steps (prepare_slot_layout perm)).
Proof.
  intro perm. apply Forall_forall. intros [gap rank] Hin. cbn [snd].
  unfold prepare_slot_layout in Hin. cbn [projection_steps] in Hin.
  assert (Hrank : In rank (map snd (slot_rank_positions 1 perm))).
  { rewrite <- (slot_position_gaps_ranks 0 (slot_rank_positions 1 perm)).
    apply in_map_iff. exists (gap, rank). split; [reflexivity | exact Hin]. }
  apply in_map_iff in Hrank. destruct Hrank as [[position r] [Heq Hentry]].
  cbn [snd] in Heq. subst r.
  apply Pos.size_nat_monotone. apply Pos2Nat.inj_lt.
  rewrite SuccNat2Pos.id_succ.
  pose proof (slot_rank_positions_upper 1 perm position rank Hentry) as Hupper.
  cbn [Pos.to_nat] in Hupper. lia.
Qed.

(** Every prepared layout charges one tuple walk and the bit cost of its original ranks. *)
Theorem T_project_slot_layout_le : forall C perm (u : list C),
  (T_project_slot_layout (prepare_slot_layout perm) u <= N.of_nat (length u + 1) +
    (2 * PTrieT.c_trie + 10) * N.of_nat (length perm + 1) *
      N.of_nat (Pos.size_nat (Pos.of_succ_nat (length perm)) + 1))%N.
Proof.
  intros C perm u.
  pose proof (T_slot_pick_ranked_le C (projection_steps (prepare_slot_layout perm)) u
    PTrieCode.empty (Pos.size_nat (Pos.of_succ_nat (length perm)))
    (slot_prepared_rank_bits perm)) as Hpick.
  assert (Hrange : Pos.to_nat 1 + length perm <= Pos.to_nat (Pos.of_succ_nat (length perm))).
  { rewrite SuccNat2Pos.id_succ. cbn. lia. }
  pose proof (T_slot_read_ranked_le C (length perm) 1
    (slot_pick_ranked (projection_steps (prepare_slot_layout perm)) u PTrieCode.empty)
    (Pos.of_succ_nat (length perm)) Hrange) as Hread.
  pose proof (Datatypes.T_length_le (projection_steps (prepare_slot_layout perm))) as Hlength.
  time_unfold (@T_project_slot_layout). time_simpl. time_cbn_all.
  rewrite ?slot_position_gaps_length, ?slot_rank_positions_length in *.
  set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost.
  rewrite ?Nat2N.inj_add in *.
  change (N.of_nat 1) with 1%N in *. nia.
Qed.

(** Stable row identifiers retain historical keys through collisions. *)
Record database_row_store (C : Type) := {
  row_history : list ((positive * list C) * positive);
  row_links : list (positive * positive);
  row_weights : list (positive * N);
  row_keys : list (positive * list C);
  row_fresh : positive
}.

(** Slot groups and tuple counts retain the layout of the initialized database. *)
Record database_slot_store (C : Type) := {
  prepared_slots : list (positive * database_slot_layout);
  slot_positions : list (bool * N * N);
  function_groups : list (positive * N);
  slot_groups : list ((bool * N) * list N);
  projection_counts : list ((N * list C) * N)
}.

(** Runtime contents are stored independently of the union-find membership counter.
    The abstract index type is an explicit parameter of the concrete state. *)
Record database_runtime (C X : Type) := DatabaseRuntime {
  runtime_allocated : N;
  runtime_changed : bool;
  runtime_declarations : list decl;
  runtime_kinds : PTrieCode.t output;
  runtime_rows : PTrieCode.t ((positive * list C) * option C);
  runtime_slots : list (positive * list nat);
  runtime_equalities : list (positive * positive);
  runtime_queue : list positive;
  runtime_all_indexes : PTrieCode.t X;
  runtime_new_indexes : PTrieCode.t X;
  runtime_projection_counts : PTrieCode.t (PTrieCode.t (list C * N));
  runtime_function_slots : PTrieCode.t (list (N * database_slot_layout));
  runtime_max_name : positive;
  runtime_slot_bound : N
}.

Arguments DatabaseRuntime {C X}.
Arguments runtime_allocated {C X}.
Arguments runtime_changed {C X}.
Arguments runtime_declarations {C X}.
Arguments runtime_kinds {C X}.
Arguments runtime_rows {C X}.
Arguments runtime_slots {C X}.
Arguments runtime_equalities {C X}.
Arguments runtime_queue {C X}.
Arguments runtime_all_indexes {C X}.
Arguments runtime_new_indexes {C X}.
Arguments runtime_projection_counts {C X}.
Arguments runtime_function_slots {C X}.
Arguments runtime_max_name {C X}.
Arguments runtime_slot_bound {C X}.

TimeFun runtime_allocated runtime_changed runtime_declarations runtime_kinds runtime_rows.
TimeFun runtime_slots runtime_equalities runtime_queue runtime_all_indexes runtime_new_indexes.
TimeFun runtime_projection_counts runtime_function_slots runtime_max_name runtime_slot_bound.

Record database_state (C X : Type) := DatabaseState {
  db_forest : UnionFindCode.t;
  db_nuses : N;
  db_npending : N;
  db_wmark : N;
  db_written_cells : list C;
  db_index_counters : list positive;
  db_row_store : database_row_store C;
  db_slot_store : database_slot_store C;
  db_runtime : database_runtime C X
}.

Arguments DatabaseState {C X}.
Arguments db_forest {C X}.
Arguments db_nuses {C X}.
Arguments db_npending {C X}.
Arguments db_wmark {C X}.
Arguments db_written_cells {C X}.
Arguments db_index_counters {C X}.
Arguments db_row_store {C X}.
Arguments db_slot_store {C X}.
Arguments db_runtime {C X}.

TimeFun db_forest.
TimeFun db_nuses.
TimeFun db_npending.
TimeFun db_wmark.
TimeFun db_written_cells.
TimeFun db_index_counters.
TimeFun db_row_store.
TimeFun db_slot_store.
TimeFun db_runtime.

(** Earlier declarations override later declarations, as in [lookup_kind]. *)
Definition database_kinds (ds : list decl) : PTrieCode.t output :=
  fold_right (fun d kinds => PTrieCode.set (name d) (out d) kinds) PTrieCode.empty ds.
TimeFun database_kinds.

Definition database_max_name (ds : list decl) : positive :=
  fold_right (fun d bound => Pos.max (name d) bound) 1%positive ds.
TimeFun database_max_name.

Fixpoint database_slot_groups (next : N) (prepared : list (positive * database_slot_layout))
    (groups : PTrieCode.t (list (N * database_slot_layout)))
    : PTrieCode.t (list (N * database_slot_layout)) :=
  match prepared with
  | [] => groups
  | (f, layout) :: rest =>
    let previous := match PTrieCode.get f groups with Some slots => slots | None => [] end in
    database_slot_groups (N.succ next) rest (PTrieCode.set f ((next, layout) :: previous) groups)
  end.
TimeFun database_slot_groups.

(** Reading a missing function group gives its empty slot list. *)
Definition database_group_entries (f : positive)
    (groups : PTrieCode.t (list (N * database_slot_layout))) : list (N * database_slot_layout) :=
  match PTrieCode.get f groups with Some slots => slots | None => [] end.

(** A prepared list entry receives its offset from the starting slot number. *)
Definition database_slot_member (next : N) (prepared : list (positive * database_slot_layout))
    (f : positive) (s : N) (layout : database_slot_layout) : Prop :=
  exists n, nth_error prepared n = Some (f, layout) /\ s = (next + N.of_nat n)%N.

(** Prepending to one function group adds exactly its new numbered layout. *)
Lemma database_group_add_member : forall f g next block groups s layout,
  In (s, layout) (database_group_entries f
    (PTrieCode.set g ((next, block) :: database_group_entries g groups) groups)) <->
  In (s, layout) (database_group_entries f groups) \/
    (f = g /\ s = next /\ layout = block).
Proof.
  intros f g next block groups s layout. unfold database_group_entries.
  destruct (Pos.eq_dec f g) as [-> | Hdifferent].
  - rewrite PTrie.get_set_same. cbn [In]. intuition congruence.
  - rewrite PTrie.get_set_other by exact Hdifferent. intuition congruence.
Qed.

(** Numbering a nonempty prepared list separates its head from the incremented tail. *)
Lemma database_slot_member_cons : forall next g block rest f s layout,
  database_slot_member next ((g, block) :: rest) f s layout <->
    (f = g /\ s = next /\ layout = block) \/
    database_slot_member (N.succ next) rest f s layout.
Proof.
  intros next g block rest f s layout. unfold database_slot_member. split.
  - intros [n [Hentry Hslot]]. destruct n as [| n].
    + cbn [nth_error] in Hentry. injection Hentry as Hfunction Hlayout.
      left. split; [congruence |]. split; [cbn in Hslot; lia | congruence].
    + right. exists n. split; [exact Hentry |]. rewrite Nat2N.inj_succ in Hslot. lia.
  - intros [[-> [-> ->]] | [n [Hentry Hslot]]].
    + exists 0. split; [reflexivity | lia].
    + exists (S n). split; [exact Hentry |]. rewrite Nat2N.inj_succ. lia.
Qed.

(** Group construction adds exactly the numbered entries of the prepared input. *)
Lemma database_slot_groups_member : forall prepared next groups f s layout,
  In (s, layout) (database_group_entries f (database_slot_groups next prepared groups)) <->
    In (s, layout) (database_group_entries f groups) \/
      database_slot_member next prepared f s layout.
Proof.
  induction prepared as [| [g block] rest IH]; intros next groups f s layout.
  - cbn [database_slot_groups]. unfold database_slot_member. split.
    + intro Hin. now left.
    + intros [Hin | [n [Hentry _]]]; [exact Hin | destruct n; discriminate].
  - cbn [database_slot_groups]. fold (database_group_entries g groups).
    rewrite IH, database_group_add_member, database_slot_member_cons. tauto.
Qed.

(** A prepared function group contains exactly the declared slots at their global numbers. *)
Lemma database_prepared_group_member : forall sl f s layout,
  In (s, layout) (database_group_entries f
    (database_slot_groups 0 (prepare_slot_layouts sl) PTrieCode.empty)) <->
  exists perm, nth_error sl (N.to_nat s) = Some (f, perm) /\
    layout = prepare_slot_layout perm.
Proof.
  intros sl f s layout. rewrite database_slot_groups_member.
  unfold database_slot_member, prepare_slot_layouts.
  unfold database_group_entries at 1. rewrite PTrie.get_empty. cbn [In]. split.
  - intros [Hfalse | [n [Hentry Hslot]]]; [contradiction |].
    rewrite nth_error_map in Hentry.
    destruct (nth_error sl n) as [[g perm] |] eqn:Hnth; [| discriminate].
    cbn [option_map fst snd] in Hentry. injection Hentry as Hfunction Hlayout.
    subst g. exists perm. split; [| congruence].
    replace s with (N.of_nat n) by lia. now rewrite Nat2N.id.
  - intros [perm [Hentry ->]]. right. exists (N.to_nat s). split.
    + rewrite nth_error_map, Hentry. reflexivity.
    + rewrite N2Nat.id. lia.
Qed.

(** Existing group numbers are distinct and lie below the next number to allocate. *)
Definition database_groups_bounded (next : N)
    (groups : PTrieCode.t (list (N * database_slot_layout))) : Prop :=
  forall f, NoDup (map fst (database_group_entries f groups)) /\
    (forall s, In s (map fst (database_group_entries f groups)) -> (s < next)%N).

(** Numbering one fresh slot preserves distinctness in every function group. *)
Lemma database_groups_bounded_add : forall next groups g block,
  database_groups_bounded next groups ->
  database_groups_bounded (N.succ next)
    (PTrieCode.set g ((next, block) :: database_group_entries g groups) groups).
Proof.
  intros next groups g block Hbounded f. destruct (Pos.eq_dec f g) as [-> | Hdifferent].
  - destruct (Hbounded g) as [Hdistinct Hbelow].
    unfold database_group_entries at 1 3. rewrite !PTrie.get_set_same.
    cbn [map fst]. split.
    + constructor; [intro Hin; specialize (Hbelow next Hin); lia | exact Hdistinct].
    + intros s [-> | Hin]; [lia | specialize (Hbelow s Hin); lia].
  - destruct (Hbounded f) as [Hdistinct Hbelow].
    unfold database_group_entries at 1 3. rewrite !PTrie.get_set_other by exact Hdifferent.
    fold (database_group_entries f groups). split; [exact Hdistinct |].
    intros s Hin. specialize (Hbelow s Hin). lia.
Qed.

(** A complete group build preserves globally fresh slot numbering. *)
Lemma database_slot_groups_bounded : forall prepared next groups,
  database_groups_bounded next groups ->
  database_groups_bounded (next + N.of_nat (length prepared))
    (database_slot_groups next prepared groups).
Proof.
  induction prepared as [| [g block] rest IH]; intros next groups Hbounded.
  - cbn [database_slot_groups length]. now rewrite N.add_0_r.
  - cbn [database_slot_groups length]. fold (database_group_entries g groups).
    rewrite Nat2N.inj_succ.
    replace (next + N.succ (N.of_nat (length rest)))%N
      with (N.succ next + N.of_nat (length rest))%N by lia.
    apply IH. now apply database_groups_bounded_add.
Qed.

(** A function's prepared list visits each global slot number at most once. *)
Lemma database_prepared_group_nodup : forall sl f,
  NoDup (map fst (database_group_entries f
    (database_slot_groups 0 (prepare_slot_layouts sl) PTrieCode.empty))).
Proof.
  intros sl f. assert (Hempty : database_groups_bounded 0 PTrieCode.empty).
  { intro g. unfold database_group_entries. rewrite PTrie.get_empty.
    split; [constructor | intros s Hin; contradiction]. }
  exact (proj1 (database_slot_groups_bounded
    (prepare_slot_layouts sl) 0 PTrieCode.empty Hempty f)).
Qed.

Definition runtime_set_rows {C X} (rows : PTrieCode.t ((positive * list C) * option C))
    (state : database_runtime C X) : database_runtime C X :=
  DatabaseRuntime (runtime_allocated state) (runtime_changed state) (runtime_declarations state) (runtime_kinds state) rows
    (runtime_slots state) (runtime_equalities state) (runtime_queue state) (runtime_all_indexes state) (runtime_new_indexes state)
    (runtime_projection_counts state) (runtime_function_slots state) (runtime_max_name state) (runtime_slot_bound state).
TimeFun runtime_set_rows.

Definition runtime_set_changed {C X} (flag : bool)
    (state : database_runtime C X) : database_runtime C X :=
  DatabaseRuntime (runtime_allocated state) flag (runtime_declarations state) (runtime_kinds state) (runtime_rows state)
    (runtime_slots state) (runtime_equalities state) (runtime_queue state) (runtime_all_indexes state) (runtime_new_indexes state)
    (runtime_projection_counts state) (runtime_function_slots state) (runtime_max_name state) (runtime_slot_bound state).
TimeFun runtime_set_changed.

Definition runtime_set_allocated {C X} (allocated : N)
    (state : database_runtime C X) : database_runtime C X :=
  DatabaseRuntime allocated (runtime_changed state) (runtime_declarations state) (runtime_kinds state) (runtime_rows state)
    (runtime_slots state) (runtime_equalities state) (runtime_queue state) (runtime_all_indexes state) (runtime_new_indexes state)
    (runtime_projection_counts state) (runtime_function_slots state) (runtime_max_name state) (runtime_slot_bound state).
TimeFun runtime_set_allocated.

Definition runtime_set_union {C X} (flag : bool) (equalities : list (positive * positive)) (queue : list positive)
    (state : database_runtime C X) : database_runtime C X :=
  DatabaseRuntime (runtime_allocated state) flag (runtime_declarations state) (runtime_kinds state) (runtime_rows state)
    (runtime_slots state) equalities queue (runtime_all_indexes state) (runtime_new_indexes state)
    (runtime_projection_counts state) (runtime_function_slots state) (runtime_max_name state) (runtime_slot_bound state).
TimeFun runtime_set_union.

Definition runtime_set_indexes {C X} (all_indexes new_indexes : PTrieCode.t X) (counts : PTrieCode.t (PTrieCode.t (list C * N)))
    (state : database_runtime C X) : database_runtime C X :=
  DatabaseRuntime (runtime_allocated state) (runtime_changed state) (runtime_declarations state) (runtime_kinds state) (runtime_rows state)
    (runtime_slots state) (runtime_equalities state) (runtime_queue state) all_indexes new_indexes
    counts (runtime_function_slots state) (runtime_max_name state) (runtime_slot_bound state).
TimeFun runtime_set_indexes.

Definition database_set_runtime {C X} (state : database_runtime C X)
    (db : database_state C X) : database_state C X :=
  DatabaseState (db_forest db) (db_nuses db) (db_npending db) (db_wmark db)
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) state.
TimeFun database_set_runtime.

Definition database_set_forest {C X} (forest : UnionFindCode.t)
    (db : database_state C X) : database_state C X :=
  DatabaseState forest (db_nuses db) (db_npending db) (db_wmark db)
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) (db_runtime db).
TimeFun database_set_forest.

Definition database_set_pending {C X} (pending : N)
    (db : database_state C X) : database_state C X :=
  DatabaseState (db_forest db) (db_nuses db) pending (db_wmark db)
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) (db_runtime db).
TimeFun database_set_pending.

Module DatabaseCode (V : VALUE_OPS) (I : INDEX_OPS V) <: DATABASE_OPS V I.
  Definition t := database_state (cell V.t) I.t.

  Definition db_cell_code (c : cell V.t) : positive :=
    match c with Id i => xO i | Val v => xI (V.encode v) end.
  Definition db_cell_eqb (c d : cell V.t) : bool :=
    match c, d with
    | Id i, Id j => Pos.eqb i j
    | Val v, Val w => V.eqb v w
    | _, _ => false
    end.
  Definition db_tuple_code := list_code db_cell_code.
  Definition db_row_code (f : positive) (k : list (cell V.t)) : positive :=
    pair_code (fun p => p) db_tuple_code (f, k).
  Definition row_get (f : positive) (k : list (cell V.t)) (db : t)
      : option (option (cell V.t)) :=
    option_map snd (PTrieCode.get (db_row_code f k) (runtime_rows (db_runtime db))).
  Definition kind_get (f : positive) (db : t) : option output :=
    PTrieCode.get f (runtime_kinds (db_runtime db)).
  Definition normal_cell (db : t) (c : cell V.t) : cell V.t :=
    match c with
    | Id i => Id (fst (UnionFindCode.find i (db_forest db)))
    | Val v => Val v
    end.
  Definition normal_key (db : t) (k : list (cell V.t)) : list (cell V.t) :=
    map (normal_cell db) k.
  Definition output_eqb (a b : option (cell V.t)) : bool :=
    match a, b with
    | None, None => true
    | Some c, Some d => db_cell_eqb c d
    | _, _ => false
    end.
  Definition combine_output (db : t) (f : positive)
      (previous : option (option (cell V.t))) (o : option (cell V.t)) : option (cell V.t) :=
    match previous, kind_get f db, o with
    | Some (Some (Val a)), Some (OLat m), Some (Val b) => Some (Val (V.merge m a b))
    | Some old, _, _ => old
    | None, _, _ => o
    end.

  Definition slot_index_get (s : positive) (indexes : PTrieCode.t I.t) : I.t :=
    match PTrieCode.get s indexes with Some ix => ix | None => I.empty end.
  Definition projection_table_get (s : positive)
      (counts : PTrieCode.t (PTrieCode.t (list (cell V.t) * N))) :=
    match PTrieCode.get s counts with Some table => table | None => PTrieCode.empty end.

  (** Projection counts keep a shared tuple until its last contributing row is removed. *)
  Definition slot_update_one (add : bool) (s : N) (u : list (cell V.t))
      (state : database_runtime (cell V.t) I.t) :=
    let code := N.succ_pos s in
    let tuple_code := db_tuple_code u in
    let table := projection_table_get code (runtime_projection_counts state) in
    let count := match PTrieCode.get tuple_code table with
      | Some (_, n) => n | None => 0%N end in
    let all := slot_index_get code (runtime_all_indexes state) in
    let new := slot_index_get code (runtime_new_indexes state) in
    if add then
      runtime_set_indexes
        (PTrieCode.set code (I.insert u all) (runtime_all_indexes state))
        (PTrieCode.set code (I.insert u new) (runtime_new_indexes state))
        (PTrieCode.set code (PTrieCode.set tuple_code (u, N.succ count) table)
          (runtime_projection_counts state)) state
    else match count with
      | N0 => state
      | Npos xH =>
        runtime_set_indexes
          (PTrieCode.set code (I.remove u all) (runtime_all_indexes state))
          (PTrieCode.set code (I.remove u new) (runtime_new_indexes state))
          (PTrieCode.set code (PTrieCode.remove tuple_code table)
            (runtime_projection_counts state)) state
      | _ =>
        runtime_set_indexes (runtime_all_indexes state) (runtime_new_indexes state)
          (PTrieCode.set code (PTrieCode.set tuple_code (u, N.pred count) table)
            (runtime_projection_counts state)) state
      end.

  Fixpoint slot_update_many (add : bool) (u : list (cell V.t))
      (layouts : list (N * database_slot_layout))
      (state : database_runtime (cell V.t) I.t) :=
    match layouts with
    | [] => state
    | (s, layout) :: rest =>
      slot_update_many add u rest
        (slot_update_one add s (project_slot_layout layout u) state)
    end.

  Definition slots_update (add : bool) (f : positive) (u : list (cell V.t)) (db : t)
      : t :=
    match PTrieCode.get f (runtime_function_slots (db_runtime db)) with
    | None => db
    | Some layouts => database_set_runtime (slot_update_many add u layouts (db_runtime db)) db
    end.

  Definition row_write (f : positive) (k : list (cell V.t)) (o : option (cell V.t))
      (db : t) : t :=
    database_set_runtime
      (runtime_set_rows
        (PTrieCode.set (db_row_code f k) ((f, k), o) (runtime_rows (db_runtime db)))
        (runtime_set_changed true (db_runtime db))) db.

  Definition row_replace (f : positive) (k : list (cell V.t))
      (previous : option (option (cell V.t))) (o : option (cell V.t)) (db : t) : t :=
    let without := match previous with
      | None => db
      | Some before => slots_update false f (k ++ option_list before) db
      end in
    row_write f k o (slots_update true f (k ++ option_list o) without).
  (** Initialization stores declarations, slots, empty rows and index caches. *)
  (* STUB-CODE *)
  Definition init (ds : list decl) (sl : list (positive * list nat)) : t :=
    let prepared := prepare_slot_layouts sl in
    let bound := N.of_nat (length sl) in
    DatabaseState UnionFindCode.empty 0%N 0%N
      (N.max (Npos (database_max_name ds)) (N.succ bound)) []
      (match sl with [] => [1%positive] | _ => [1%positive; N.succ_pos bound] end)
      {| row_history := []; row_links := []; row_weights := []; row_keys := [];
         row_fresh := 1 |}
      {| prepared_slots := prepared;
         slot_positions := []; function_groups := []; slot_groups := [];
         projection_counts := [] |}
      (DatabaseRuntime 0%N false ds (database_kinds ds) PTrieCode.empty sl [] []
        PTrieCode.empty PTrieCode.empty PTrieCode.empty
        (database_slot_groups 0 prepared PTrieCode.empty) (database_max_name ds) bound).
  Definition find (i : positive) (db : t) : positive * t :=
    let result := UnionFindCode.find i (db_forest db) in
    (fst result, database_set_forest (snd result) db).
  Definition lookup (f : positive) (k : list (cell V.t)) (db : t)
      : option (option (cell V.t)) * t :=
    match Pos.compare (runtime_max_name (db_runtime db)) f with
    | Lt => (None, db)
    | _ => (row_get f (normal_key db k) db, db)
    end.
  Definition union (i j : positive) (db : t) :=
    let result := UnionFindCode.union i j (db_forest db) in
    let next := database_set_forest (snd result) db in
    match fst result with
    | None => next
    | Some (_, loser) =>
      database_set_pending (N.succ (db_npending db))
        (database_set_runtime
          (runtime_set_union true ((i, j) :: runtime_equalities (db_runtime db))
            (loser :: runtime_queue (db_runtime db)) (db_runtime db)) next)
    end.
  Definition allocate_id (i : positive) (db : t) : t :=
    database_set_forest (UnionFindCode.add i (db_forest db))
      (database_set_runtime
        (runtime_set_allocated (Npos i) (runtime_set_changed true (db_runtime db))) db).
  Definition make (f : positive) (k : list (cell V.t)) (db : t) : positive * t :=
    let ck := normal_key db k in
    let previous := row_get f ck db in
    match previous with
    | Some (Some (Id j)) => (fst (UnionFindCode.find j (db_forest db)), db)
    | _ =>
      let i := N.succ_pos (runtime_allocated (db_runtime db)) in
      let fresh := allocate_id i db in
      let next := match kind_get f db with
        | Some OId => row_replace f ck previous (Some (Id i)) fresh
        | _ => fresh
        end in
      (i, next)
    end.
  Definition put (f : positive) (k : list (cell V.t)) (o : option (cell V.t))
      (db : t) : t :=
    let ck := normal_key db k in
    let co := option_map (normal_cell db) o in
    let previous := row_get f ck db in
    let updated := combine_output db f previous co in
    let next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end in
    match previous with
    | Some before =>
      if output_eqb before updated then next else row_replace f ck previous updated next
    | None => row_replace f ck previous updated next
    end.
  (* STUB-CODE *)
  Definition db_rstep (s : t * list (positive * list (cell V.t)))
      : (t * list (positive * list (cell V.t))) + t := inr (fst s).
  Definition db_rebuild_fuel (db : t) : N :=
    ((N.size (runtime_allocated (db_runtime db)) + 2) * (db_nuses db + 1) + db_npending db + 1)%N.
  Definition rebuild (db : t) :=
    match loopN db_rstep (db_rebuild_fuel db) (db, []) with
    | inl s => fst s
    | inr result => result
    end.
  Definition index (s : N) (new : bool) (db : t) : I.t :=
    match N.compare (runtime_slot_bound (db_runtime db)) s with
    | Gt =>
      let indexes := if new then runtime_new_indexes (db_runtime db)
        else runtime_all_indexes (db_runtime db) in
      match PTrieCode.get (N.succ_pos s) indexes with Some ix => ix | None => I.empty end
    | _ => I.empty
    end.
  Definition advance (db : t) :=
    database_set_runtime
      (runtime_set_changed false
        (runtime_set_indexes (runtime_all_indexes (db_runtime db)) PTrieCode.empty
          (runtime_projection_counts (db_runtime db)) (db_runtime db))) db.
  Definition changed (db : t) := runtime_changed (db_runtime db).
  Definition ids (db : t) : N := runtime_allocated (db_runtime db).
  (* STUB-CODE *)
  Definition locate (_ : positive) (_ : list (cell V.t)) (_ : t)
      : option (list (cell V.t)) := None.
  (* STUB-CODE *)
  Definition rank_slots (_ : list decl) (_ : list (positive * list nat))
      : list (bool * N * N) := [].
End DatabaseCode.

Module Database (V : VALUE) (I : INDEX V) <: DATABASE V I.
  Include DatabaseCode V I.
  Include DATABASE_SPEC V I.
  (* spec: wf view repr pending old slots *)
  Definition view (db : t) : Model.view (V := V.t) :=
    {| row := fun f k o => row_get f k db = Some o;
       same := equality_log (runtime_equalities (db_runtime db));
       kind := fun f => kind_get f db |}.
  Definition repr (db : t) : positive -> positive := UnionFind.repr (db_forest db).
  Definition pending (db : t) : nat := length (runtime_queue (db_runtime db)).
  Definition old (db : t) (f : positive) (k : list (cell V.t)) := row_get f k db.
  Definition slots (db : t) : list (positive * list nat) := runtime_slots (db_runtime db).
  Definition canon (db : t) (c : cell V.t) : cell V.t :=
    match c with
    | Id i => Id (repr db i)
    | Val v => Val v
    end.
  Definition canonical (db : t) : Prop :=
    forall f k o, row (view db) f k o ->
    forall i, In (Id i) (k ++ option_list o) -> repr db i = i.
  Definition cong (db : t) := fd_congruence (view db).
  Definition combine (db : t) (f : positive) (previous : option (option (cell V.t)))
      (o : option (cell V.t)) : option (cell V.t) :=
    match previous, kind (view db) f, o with
    | Some (Some (Val a)), Some (OLat m), Some (Val b) => Some (Val (V.merge m a b))
    | Some old, _, _ => old
    | None, _, _ => o
    end.
  Definition allocated (db : t) (i : positive) : Prop := (Npos i <= ids db)%N.
  (** Slot permutations contain distinct positions within the supplied tuple. *)
  Definition slots_fit (db : t) (f : positive) (n : nat) : Prop :=
    forall perm, In (f, perm) (slots db) -> NoDup perm /\ Forall (fun i => i < n) perm.
  Definition kind_ok (db : t) (f : positive) (k : list (cell V.t))
      (o : option (cell V.t)) : Prop :=
    (forall i, In (Id i) (k ++ option_list o) -> allocated db i) /\
    slots_fit db f (length (k ++ option_list o)) /\
    match kind (view db) f, o with
    | Some ORel, None => True
    | Some OId, Some (Id _) => True
    | Some (OLat _), Some (Val _) => True
    | _, _ => False
    end.
  Definition conflict (db : t) (f : positive) (k : list (cell V.t))
      (o : option (cell V.t)) (a b : positive) : Prop :=
    old db f (map (canon db) k) = Some (Some (Id a)) /\
    option_map (canon db) o = Some (Id b).
  Definition fresh_id (db : t) (i : positive) : Prop := i = N.succ_pos (ids db).
  Definition extends_by (db db' : t) (f : positive) (k : list (cell V.t))
      (i : positive) : Prop :=
    ids db' = Npos i /\ kind (view db') = kind (view db) /\
    (forall a b, same (view db') a b <-> same (view db) a b \/ (a = i /\ b = i)) /\
    (forall f' k' o', row (view db') f' k' o' <->
      row (view db) f' k' o' \/ (f' = f /\ k' = map (canon db) k /\ o' = Some (Id i))).
  Definition slot_of (db : t) (s : N) : option (positive * list nat) :=
    nth_error (slots db) (N.to_nat s).
  Definition permute (perm : list nat) (u : list (cell V.t)) : list (cell V.t) :=
    flat_map (fun i => option_list (nth_error u i)) perm.
  Definition merged (db : t) (f : positive) (os : list (option (cell V.t)))
      : option (cell V.t) :=
    match map (option_map (canon db)) os with
    | [] => None
    | o :: rest => fold_left (fun acc o' => combine db f (Some acc) o') rest o
    end.

  Definition out_le (db : t) (f : positive) (a b : option (cell V.t)) : Prop :=
    match a, b with
    | None, _ => True
    | Some c, Some d => cell_le V.merge (view db) f c d
    | _, _ => False
    end.
  Definition present_put (w : Model.view (V := V.t)) (f : positive)
      (k : list (cell V.t)) (o : option (cell V.t)) : Prop :=
    exists d, row w f k d /\
      match o, d with
      | None, _ => True
      | Some a, Some b => cell_le V.merge w f a b
      | _, _ => False
      end.

  Module Cells := CellKey V.
  Module Tuples := ListKey Cells.
  Module RowKeys := PairKey PosKey Tuples.
  Module RowMap := TrieMap RowKeys.
  Module RowFacts := FiniteMapFacts RowKeys RowMap.
  Module ForestFacts := UnionFindFacts UnionFind.

  (** A cached projection count records how many stored rows contribute its tuple. *)
  Definition stored_projection_count (db : t) (s : N) (u : list (cell V.t)) : N :=
    match PTrieCode.get (db_tuple_code u)
      (projection_table_get (N.succ_pos s) (runtime_projection_counts (db_runtime db))) with
    | Some (_, n) => n
    | None => 0%N
    end.

  (** Counts refer to the actual finite row map, including distinct rows with one projection. *)
  Definition projection_counts_ok (db : t) : Prop :=
    forall s f perm u, slot_of db s = Some (f, perm) ->
    exists rs, NoDup rs /\
      (forall r, In r rs <->
        In r (RowMap.elements (runtime_rows (db_runtime db))) /\ fst (fst r) = f /\
        permute perm (snd (fst r) ++ option_list (snd r)) = u) /\
      N.to_nat (stored_projection_count db s u) = length rs.

  (** Stored facts agree with the forest, allocated identifiers and declared row kinds. *)
  Definition database_wf (db : t) : Prop :=
    (UnionFind.wf (db_forest db)) /\
    (forall i, UnionFind.mem (db_forest db) i <-> allocated db i) /\
    (count (db_forest db) = ids db) /\
    (UnionFind.width (db_forest db) <= N.size_nat (ids db)) /\
    (forall i j, same (view db) i j <-> repr db i = repr db j) /\
    (Forall (fun edge => allocated db (fst edge) /\ allocated db (snd edge))
      (runtime_equalities (db_runtime db))) /\
    (RowMap.wf (runtime_rows (db_runtime db))) /\
    (forall f k o, row (view db) f k o ->
      match kind (view db) f, o with
      | Some ORel, None | Some OId, Some (Id _) | Some (OLat _), Some (Val _) => True
      | _, _ => False
      end) /\
    (forall f k o i, row (view db) f k o ->
      In (Id i) (k ++ option_list o) -> allocated db i) /\
    (forall f k o, row (view db) f k o ->
      slots_fit db f (length (k ++ option_list o))) /\
    (forall f output, kind (view db) f = Some output ->
      (f <= runtime_max_name (db_runtime db))%positive) /\
    (runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db))) /\
    (db_npending db = N.of_nat (pending db)) /\
    (Forall (allocated db) (runtime_queue (db_runtime db))) /\
    (pending db = 0 -> canonical db) /\
    (forall s new u, I.mem (index s new db) u ->
      exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
        u = permute perm (k ++ option_list o)) /\
    (forall s f perm k o, slot_of db s = Some (f, perm) ->
      row (view db) f k o -> I.mem (index s false db) (permute perm (k ++ option_list o))) /\
    (forall s new f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s new db)) /\
    (runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty) /\
    projection_counts_ok db.

  (** The stored invariant supplies forest. *)
  Lemma wf_forest : forall db, database_wf db -> UnionFind.wf (db_forest db).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies forest members. *)
  Lemma wf_forest_members : forall db, database_wf db -> forall i, UnionFind.mem (db_forest db) i <-> allocated db i.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies forest count. *)
  Lemma wf_forest_count : forall db, database_wf db -> count (db_forest db) = ids db.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies forest width. *)
  Lemma wf_forest_width : forall db, database_wf db -> UnionFind.width (db_forest db) <= N.size_nat (ids db).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies equalities. *)
  Lemma wf_equalities : forall db, database_wf db -> forall i j, same (view db) i j <-> repr db i = repr db j.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies log allocated. *)
  Lemma wf_log_allocated : forall db, database_wf db -> Forall (fun edge => allocated db (fst edge) /\ allocated db (snd edge))
      (runtime_equalities (db_runtime db)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies row map. *)
  Lemma wf_row_map : forall db, database_wf db -> RowMap.wf (runtime_rows (db_runtime db)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies row kind. *)
  Lemma wf_row_kind : forall db, database_wf db -> forall f k o, row (view db) f k o ->
      match kind (view db) f, o with
      | Some ORel, None | Some OId, Some (Id _) | Some (OLat _), Some (Val _) => True
      | _, _ => False
      end.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies row ids. *)
  Lemma wf_row_ids : forall db, database_wf db -> forall f k o i, row (view db) f k o ->
      In (Id i) (k ++ option_list o) -> allocated db i.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies row slots. *)
  Lemma wf_row_slots : forall db, database_wf db -> forall f k o, row (view db) f k o ->
      slots_fit db f (length (k ++ option_list o)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies kind bound. *)
  Lemma wf_kind_bound : forall db, database_wf db -> forall f output, kind (view db) f = Some output ->
      (f <= runtime_max_name (db_runtime db))%positive.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies slot bound. *)
  Lemma wf_slot_bound : forall db, database_wf db -> runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies pending count. *)
  Lemma wf_pending_count : forall db, database_wf db -> db_npending db = N.of_nat (pending db).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies queue allocated. *)
  Lemma wf_queue_allocated : forall db, database_wf db -> Forall (allocated db) (runtime_queue (db_runtime db)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies quiet canonical. *)
  Lemma wf_quiet_canonical : forall db, database_wf db -> pending db = 0 -> canonical db.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies index sound. *)
  Lemma wf_index_sound : forall db, database_wf db -> forall s new u, I.mem (index s new db) u ->
      exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
        u = permute perm (k ++ option_list o).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies index complete. *)
  Lemma wf_index_complete : forall db, database_wf db -> forall s f perm k o, slot_of db s = Some (f, perm) ->
      row (view db) f k o -> I.mem (index s false db) (permute perm (k ++ option_list o)).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant supplies index arity. *)
  Lemma wf_index_arity : forall db, database_wf db -> forall s new f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s new db).
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The function table contains exactly the prepared layouts of the stored slot list. *)
  Lemma wf_group_table : forall db, database_wf db ->
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The invariant ties cached projection counts to the actual row map. *)
  Lemma wf_projection_counts : forall db, database_wf db -> projection_counts_ok db.
  Proof.
    unfold database_wf. tauto.
  Qed.
  Definition wf : t -> Prop := database_wf.

  (** Executable cell normalization returns the public representative-based cell. *)
  Lemma normal_cell_correct : forall db c, wf db -> normal_cell db c = canon db c.
  Proof.
    intros db [i | v] Hwf; cbn [normal_cell canon repr].
    - f_equal. apply UnionFind.find_repr. exact (wf_forest db Hwf).
    - reflexivity.
  Qed.

  (** Executable key normalization agrees with the public canonical key. *)
  Lemma normal_key_correct : forall db k, wf db ->
    normal_key db k = map (canon db) k.
  Proof.
    intros db k Hwf. unfold normal_key. apply map_ext.
    intro c. exact (normal_cell_correct db c Hwf).
  Qed.

  (** Executable output normalization agrees with the public canonical output. *)
  Lemma normal_output_correct : forall db o, wf db ->
    option_map (normal_cell db) o = option_map (canon db) o.
  Proof.
    intros db [c |] Hwf; cbn [option_map].
    - now rewrite (normal_cell_correct db c Hwf).
    - reflexivity.
  Qed.

  (** A slot update preserves every observation independent of the three index caches. *)
  Lemma slot_update_one_preserves : forall (A : Type)
      (observe : database_runtime (cell V.t) I.t -> A),
    (forall all new counts state,
      observe (runtime_set_indexes all new counts state) = observe state) ->
    forall b s u state, observe (slot_update_one b s u state) = observe state.
  Proof.
    intros A observe Hkeep b s u state. unfold slot_update_one.
    destruct b; [apply Hkeep |].
    destruct (PTrieCode.get (db_tuple_code u)
      (projection_table_get (N.succ_pos s) (runtime_projection_counts state)))
      as [[tuple n] |]; [| reflexivity].
    destruct n as [| p]; [reflexivity |]. destruct p; apply Hkeep.
  Qed.

  (** Updating a function's prepared layouts preserves the same non-index observations. *)
  Lemma slot_update_many_preserves : forall (A : Type)
      (observe : database_runtime (cell V.t) I.t -> A),
    (forall all new counts state,
      observe (runtime_set_indexes all new counts state) = observe state) ->
    forall b u layouts state, observe (slot_update_many b u layouts state) = observe state.
  Proof.
    intros A observe Hkeep b u layouts.
    induction layouts as [| [s layout] rest IH]; intro state; cbn [slot_update_many].
    - reflexivity.
    - rewrite IH. apply slot_update_one_preserves. exact Hkeep.
  Qed.

  (** The database wrapper exposes exactly the preserved runtime observation. *)
  Lemma slots_update_preserves : forall (A : Type)
      (observe : database_runtime (cell V.t) I.t -> A),
    (forall all new counts state,
      observe (runtime_set_indexes all new counts state) = observe state) ->
    forall b f u db,
      observe (db_runtime (slots_update b f u db)) = observe (db_runtime db).
  Proof.
    intros A observe Hkeep b f u db. unfold slots_update.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db))) as [layouts |].
    - apply slot_update_many_preserves. exact Hkeep.
    - reflexivity.
  Qed.

  (** Index maintenance keeps the complete model view unchanged. *)
  Lemma slots_update_view : forall b f u db, view (slots_update b f u db) = view db.
  Proof.
    intros b f u db.
    exact (slots_update_preserves _
      (fun state =>
        {| row := fun g k o =>
             option_map snd (PTrieCode.get (db_row_code g k) (runtime_rows state)) = Some o;
           same := equality_log (runtime_equalities state);
           kind := fun g => PTrieCode.get g (runtime_kinds state) |})
      (fun all new counts state => eq_refl) b f u db).
  Qed.

  (** Index maintenance leaves the identifier forest in place. *)
  Lemma slots_update_forest : forall b f u db,
    db_forest (slots_update b f u db) = db_forest db.
  Proof.
    intros b f u db. unfold slots_update.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db))); reflexivity.
  Qed.

  (** Index maintenance preserves the allocated interval. *)
  Lemma slots_update_ids : forall b f u db, ids (slots_update b f u db) = ids db.
  Proof.
    intros b f u db. apply slots_update_preserves. intros. reflexivity.
  Qed.

  (** Index maintenance preserves the pending equality queue. *)
  Lemma slots_update_pending : forall b f u db,
    pending (slots_update b f u db) = pending db.
  Proof.
    intros b f u db.
    exact (slots_update_preserves _ (fun state => length (runtime_queue state))
      (fun all new counts state => eq_refl) b f u db).
  Qed.

  (** Index maintenance retains the requested slot layout. *)
  Lemma slots_update_slots : forall b f u db, slots (slots_update b f u db) = slots db.
  Proof.
    intros b f u db. apply slots_update_preserves. intros. reflexivity.
  Qed.

  (** A direct row write replaces one map binding and leaves all other bindings intact. *)
  Lemma row_write_binding : forall f k o db g args output,
    row (view (row_write f k o db)) g args output <->
      (row (view db) g args output /\ (g, args) <> (f, k)) \/
      ((g, args) = (f, k) /\ output = o).
  Proof.
    intros f k o db g args output.
    change (RowMap.get (g, args)
      (RowMap.set (f, k) o (runtime_rows (db_runtime db))) = Some output <->
      (RowMap.get (g, args) (runtime_rows (db_runtime db)) = Some output /\
        (g, args) <> (f, k)) \/ ((g, args) = (f, k) /\ output = o)).
    apply RowFacts.set_binding_iff.
  Qed.

  (** Maintaining the index caches does not change the row-write specification. *)
  Lemma row_replace_binding : forall f k previous o db g args output,
    row (view (row_replace f k previous o db)) g args output <->
      (row (view db) g args output /\ (g, args) <> (f, k)) \/
      ((g, args) = (f, k) /\ output = o).
  Proof.
    intros f k [before |] o db g args output; unfold row_replace;
      rewrite row_write_binding, !slots_update_view; reflexivity.
  Qed.

  (** Row replacement exposes the function, key and output equalities separately. *)
  Lemma row_replace_rows : forall f k previous o db g args output,
    row (view (row_replace f k previous o db)) g args output <->
      (row (view db) g args output /\ (g, args) <> (f, k)) \/
      (g = f /\ args = k /\ o = output).
  Proof.
    intros f k previous o db g args output. rewrite row_replace_binding. split.
    - intros [Hold | [Hkey Houtput]]; [now left |].
      right. injection Hkey as -> ->. repeat split; congruence.
    - intros [Hold | [-> [-> Houtput]]]; [now left |].
      right. split; congruence.
  Qed.

  (** Retaining an existing row satisfies the same replacement equation at that key. *)
  Lemma row_unchanged_binding : forall db f k o, old db f k = Some o ->
    forall g args output, row (view db) g args output <->
      (row (view db) g args output /\ (g, args) <> (f, k)) \/
      (g = f /\ args = k /\ o = output).
  Proof.
    intros db f k o Hbinding g args output.
    destruct (RowKeys.eqb_spec (g, args) (f, k)) as [Hkey | Hneq].
    - injection Hkey as -> ->. split.
      + intro Hrow. right. repeat split.
        change (old db f k = Some output) in Hrow. congruence.
      + intros [[_ Hfalse] | [_ [_ Heq]]]; [contradiction |].
        subst output. exact Hbinding.
    - split.
      + intro Hrow. left. split; assumption.
      + intros [[Hrow _] | [-> [-> _]]]; [exact Hrow | contradiction].
  Qed.

  (** The executable optional-cell equality test reflects exact output equality. *)
  Lemma output_eqb_spec : forall a b, reflect (a = b) (output_eqb a b).
  Proof.
    intros [c |] [d |].
    - change (reflect (Some c = Some d) (Cells.eqb c d)).
      destruct (Cells.eqb_spec c d); constructor; congruence.
    - constructor. discriminate.
    - constructor. discriminate.
    - constructor. reflexivity.
  Qed.

  (** Every optional output compares equal to itself. *)
  Lemma output_eqb_refl : forall o, output_eqb o o = true.
  Proof.
    intro o. destruct (output_eqb_spec o o); [reflexivity | congruence].
  Qed.

  (** Every row after a replacement is either an old row or the requested binding. *)
  Lemma row_replace_sources : forall f k previous o db g args output,
    row (view (row_replace f k previous o db)) g args output ->
      row (view db) g args output \/ (g = f /\ args = k /\ output = o).
  Proof.
    intros f k previous o db g args output Hrow.
    apply row_replace_binding in Hrow as [[Hrow _] | [Hkey Houtput]].
    - now left.
    - right. injection Hkey as -> ->. repeat split; assumption.
  Qed.

  (** Replacing an absent key adds one row and preserves every old row. *)
  Lemma row_replace_fresh : forall f k previous o db, old db f k = None ->
    forall g args output, row (view (row_replace f k previous o db)) g args output <->
      row (view db) g args output \/ (g = f /\ args = k /\ output = o).
  Proof.
    intros f k previous o db Habsent g args output. rewrite row_replace_binding.
    split.
    - intros [[Hrow _] | [Hkey Houtput]].
      + now left.
      + right. injection Hkey as -> ->. repeat split; assumption.
    - intros [Hrow | [-> [-> ->]]].
      + left. split; [exact Hrow |]. intro Hkey. injection Hkey as -> ->.
        change (old db f k = Some output) in Hrow. congruence.
      + right. split; reflexivity.
  Qed.

  (** A row-table write retains the declaration table. *)
  Lemma row_write_kind : forall f k o db,
    kind (view (row_write f k o db)) = kind (view db).
  Proof.
    reflexivity.
  Qed.

  (** A row-table write retains the equality log. *)
  Lemma row_write_same : forall f k o db,
    same (view (row_write f k o db)) = same (view db).
  Proof.
    reflexivity.
  Qed.

  (** A row-table write retains the allocation counter. *)
  Lemma row_write_ids : forall f k o db, ids (row_write f k o db) = ids db.
  Proof.
    reflexivity.
  Qed.

  (** A row-table write retains the pending queue. *)
  Lemma row_write_pending : forall f k o db, pending (row_write f k o db) = pending db.
  Proof.
    reflexivity.
  Qed.

  (** A row-table write retains the slot list. *)
  Lemma row_write_slots : forall f k o db, slots (row_write f k o db) = slots db.
  Proof.
    reflexivity.
  Qed.

  (** A row-table write retains the identifier forest. *)
  Lemma row_write_forest : forall f k o db, db_forest (row_write f k o db) = db_forest db.
  Proof.
    reflexivity.
  Qed.

  (** A replacement leaves the declared function kinds unchanged. *)
  Lemma row_replace_kind : forall f k previous o db,
    kind (view (row_replace f k previous o db)) = kind (view db).
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_kind, !slots_update_view; reflexivity.
  Qed.

  (** A replacement leaves the recorded equality relation unchanged. *)
  Lemma row_replace_same : forall f k previous o db,
    same (view (row_replace f k previous o db)) = same (view db).
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_same, !slots_update_view; reflexivity.
  Qed.

  (** Replacing a row does not allocate identifiers. *)
  Lemma row_replace_ids : forall f k previous o db,
    ids (row_replace f k previous o db) = ids db.
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_ids, !slots_update_ids; reflexivity.
  Qed.

  (** Replacing a row does not enqueue equality work. *)
  Lemma row_replace_pending : forall f k previous o db,
    pending (row_replace f k previous o db) = pending db.
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_pending, !slots_update_pending; reflexivity.
  Qed.

  (** Replacing a row preserves its slot layout. *)
  Lemma row_replace_slots : forall f k previous o db,
    slots (row_replace f k previous o db) = slots db.
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_slots, !slots_update_slots; reflexivity.
  Qed.

  (** Replacing a row leaves the identifier forest untouched. *)
  Lemma row_replace_forest : forall f k previous o db,
    db_forest (row_replace f k previous o db) = db_forest db.
  Proof.
    intros f k [before |] o db; unfold row_replace;
      rewrite row_write_forest, !slots_update_forest; reflexivity.
  Qed.

  (** A row replacement records a new fact by raising the change flag. *)
  Lemma row_replace_changed : forall f k previous o db,
    changed (row_replace f k previous o db) = true.
  Proof.
    reflexivity.
  Qed.

  (** Allocating a forest member leaves the stored rows, kinds and equality log unchanged. *)
  Lemma allocate_id_view : forall i db, view (allocate_id i db) = view db.
  Proof.
    reflexivity.
  Qed.

  (** The allocation wrapper stores the supplied identifier as its new allocation bound. *)
  Lemma allocate_id_ids : forall i db, ids (allocate_id i db) = Npos i.
  Proof.
    reflexivity.
  Qed.

  (** Allocation preserves the slot layout. *)
  Lemma allocate_id_slots : forall i db, slots (allocate_id i db) = slots db.
  Proof.
    reflexivity.
  Qed.

  (** Allocation does not enqueue equality work. *)
  Lemma allocate_id_pending : forall i db, pending (allocate_id i db) = pending db.
  Proof.
    reflexivity.
  Qed.

  (** Allocating the next positive identifier increases the interval bound by one. *)
  Lemma allocate_next_ids : forall db,
    ids (allocate_id (N.succ_pos (ids db)) db) = N.succ (ids db).
  Proof.
    intro db. rewrite allocate_id_ids. apply N.succ_pos_spec.
  Qed.

  (** Every previously allocated identifier remains allocated after a fresh allocation. *)
  Lemma allocate_next_monotone : forall db i, allocated db i ->
    allocated (allocate_id (N.succ_pos (ids db)) db) i.
  Proof.
    intros db i Hi. unfold allocated in *. rewrite allocate_next_ids. lia.
  Qed.

  (** The next interval endpoint is absent from the current well-formed forest. *)
  Lemma allocate_next_absent : forall db, wf db ->
    ~ UnionFind.mem (db_forest db) (N.succ_pos (ids db)).
  Proof.
    intros db Hwf Hmember. apply (proj1 (wf_forest_members db Hwf _)) in Hmember.
    unfold allocated in Hmember. rewrite N.succ_pos_spec in Hmember. lia.
  Qed.

  (** Fresh allocation extends exact forest membership to the new interval endpoint. *)
  Lemma allocate_next_members : forall db, wf db -> forall i,
    UnionFind.mem (db_forest (allocate_id (N.succ_pos (ids db)) db)) i <->
      allocated (allocate_id (N.succ_pos (ids db)) db) i.
  Proof.
    intros db Hwf i.
    change (UnionFind.mem (UnionFindCode.add (N.succ_pos (ids db)) (db_forest db)) i <->
      (Npos i <= Npos (N.succ_pos (ids db)))%N).
    rewrite N.succ_pos_spec.
    exact (UnionFindCodeFacts.members_add_next (db_forest db) (ids db)
      (wf_forest db Hwf) (wf_forest_members db Hwf) i).
  Qed.

  (** Fresh allocation increments the stored forest count and allocation bound together. *)
  Lemma allocate_next_count : forall db, wf db ->
    count (db_forest (allocate_id (N.succ_pos (ids db)) db)) =
      ids (allocate_id (N.succ_pos (ids db)) db).
  Proof.
    intros db Hwf. rewrite allocate_next_ids.
    change (count (UnionFindCode.add (N.succ_pos (ids db)) (db_forest db)) =
      N.succ (ids db)).
    rewrite UnionFindCodeFacts.count_add_absent by now apply allocate_next_absent.
    now rewrite (wf_forest_count db Hwf).
  Qed.

  (** Adding the fresh singleton preserves every old representative. *)
  Lemma allocate_next_repr : forall db, wf db -> forall i,
    repr (allocate_id (N.succ_pos (ids db)) db) i = repr db i.
  Proof.
    intros db Hwf i. apply UnionFind.repr_add. exact (wf_forest db Hwf).
  Qed.

  (** Fresh allocation preserves the log-to-representative agreement. *)
  Lemma allocate_next_equalities : forall db, wf db -> forall i j,
    same (view (allocate_id (N.succ_pos (ids db)) db)) i j <->
      repr (allocate_id (N.succ_pos (ids db)) db) i =
      repr (allocate_id (N.succ_pos (ids db)) db) j.
  Proof.
    intros db Hwf i j. rewrite allocate_id_view.
    rewrite (allocate_next_repr db Hwf i), (allocate_next_repr db Hwf j).
    exact (wf_equalities db Hwf i j).
  Qed.

  (** Every logged endpoint stays inside the enlarged allocation interval. *)
  Lemma allocate_next_log : forall db, wf db ->
    Forall (fun edge => allocated (allocate_id (N.succ_pos (ids db)) db) (fst edge) /\
      allocated (allocate_id (N.succ_pos (ids db)) db) (snd edge))
      (runtime_equalities (db_runtime (allocate_id (N.succ_pos (ids db)) db))).
  Proof.
    intros db Hwf. eapply Forall_impl; [| exact (wf_log_allocated db Hwf)].
    intros [i j] [Hi Hj]. split; apply allocate_next_monotone; assumption.
  Qed.

  (** The unchanged pending queue remains allocated after a fresh singleton is added. *)
  Lemma allocate_next_queue : forall db, wf db ->
    Forall (allocated (allocate_id (N.succ_pos (ids db)) db))
      (runtime_queue (db_runtime (allocate_id (N.succ_pos (ids db)) db))).
  Proof.
    intros db Hwf. eapply Forall_impl; [| exact (wf_queue_allocated db Hwf)].
    intros i Hi. now apply allocate_next_monotone.
  Qed.

  (** Identifiers in unchanged rows remain allocated after the interval grows. *)
  Lemma allocate_next_row_ids : forall db, wf db -> forall f k o i,
    row (view (allocate_id (N.succ_pos (ids db)) db)) f k o ->
    In (Id i) (k ++ option_list o) -> allocated (allocate_id (N.succ_pos (ids db)) db) i.
  Proof.
    intros db Hwf f k o i Hrow Hin. apply allocate_next_monotone.
    exact (wf_row_ids db Hwf f k o i Hrow Hin).
  Qed.

  (** Fresh singleton allocation preserves canonicality whenever the queue is empty. *)
  Lemma allocate_next_canonical : forall db, wf db ->
    pending (allocate_id (N.succ_pos (ids db)) db) = 0 ->
    canonical (allocate_id (N.succ_pos (ids db)) db).
  Proof.
    intros db Hwf Hquiet f k o Hrow i Hin.
    rewrite (allocate_next_repr db Hwf i).
    exact (wf_quiet_canonical db Hwf Hquiet f k o Hrow i Hin).
  Qed.

  (** Adding the next singleton preserves the complete database invariant. *)
  Lemma wf_allocate_next : forall db, wf db -> wf (allocate_id (N.succ_pos (ids db)) db).
  Proof.
    intros db Hwf.
    assert (Hforest : UnionFind.wf (db_forest (allocate_id (N.succ_pos (ids db)) db))).
    { apply UnionFind.wf_add. exact (wf_forest db Hwf). }
    pose proof (allocate_next_members db Hwf) as Hmembers.
    pose proof (allocate_next_count db Hwf) as Hcount.
    assert (Hwidth : UnionFind.width (db_forest (allocate_id (N.succ_pos (ids db)) db)) <=
      N.size_nat (ids (allocate_id (N.succ_pos (ids db)) db))).
    { apply UnionFindCodeFacts.width_allocated. intros i Hi. exact (proj1 (Hmembers i) Hi). }
    pose proof (allocate_next_equalities db Hwf) as Hequalities.
    pose proof (allocate_next_log db Hwf) as Hlog.
    pose proof (allocate_next_row_ids db Hwf) as Hrowids.
    pose proof (allocate_next_queue db Hwf) as Hqueue.
    pose proof (allocate_next_canonical db Hwf) as Hcanonical.
    unfold wf, database_wf in Hwf |- *. unfold allocate_id in *.
    cbn [database_set_forest database_set_runtime runtime_set_allocated runtime_set_changed
      db_forest db_runtime db_npending runtime_allocated runtime_rows runtime_kinds
      runtime_slots runtime_equalities runtime_queue runtime_all_indexes runtime_new_indexes
      runtime_projection_counts runtime_function_slots runtime_max_name runtime_slot_bound
      view row same kind row_get kind_get repr allocated ids pending slots slot_of
      index canonical slots_fit projection_counts_ok stored_projection_count] in *; tauto.
  Qed.

  (** Every fresh make branch has the required layout and allocation observations. *)
  Lemma fresh_make_layout : forall db f k previous,
    let i := N.succ_pos (ids db) in
    let fresh := allocate_id i db in
    let next := match kind_get f db with
      | Some OId => row_replace f k previous (Some (Id i)) fresh | _ => fresh end in
    kind (view next) = kind (view db) /\ slots next = slots db /\
    (ids next <= N.succ (ids db))%N /\ allocated next i /\ pending next = pending db.
  Proof.
    intros db f k previous. cbn zeta. unfold allocated.
    assert (Hnext : Npos (N.succ_pos (ids db)) = N.succ (ids db)).
    { destruct (ids db); reflexivity. }
    destruct (kind_get f db) as [[| |m] |];
      try rewrite row_replace_kind, row_replace_slots, !row_replace_ids, row_replace_pending;
      rewrite allocate_id_view, allocate_id_slots, !allocate_id_ids, allocate_id_pending;
      rewrite Hnext; repeat split; lia.
  Qed.

  (** Every stored output of a declared constructor is an identifier. *)
  Lemma constructor_old : forall db f k o, wf db -> kind (view db) f = Some OId ->
    old db f k = Some o -> exists i, o = Some (Id i).
  Proof.
    intros db f k o Hwf Hkind Hrow.
    pose proof (wf_row_kind db Hwf f k o Hrow) as Houtput.
    rewrite Hkind in Houtput. destruct o as [[i | v] |]; try contradiction.
    exists i. reflexivity.
  Qed.

  (** Writing a constructor at an absent key has exactly the public extension shape. *)
  Lemma fresh_constructor_extension : forall db f k i,
    old db f (map (canon db) k) = None ->
    extends_by db
      (row_replace f (map (canon db) k) None (Some (Id i)) (allocate_id i db)) f k i.
  Proof.
    intros db f k i Habsent. unfold extends_by.
    rewrite row_replace_ids, allocate_id_ids. split; [reflexivity |].
    rewrite row_replace_kind, allocate_id_view. split; [reflexivity |]. split.
    - intros a b. rewrite row_replace_same, allocate_id_view. split.
      + intro Hsame. now left.
      + intros [Hsame | [-> ->]]; [exact Hsame | apply equality_log_refl].
    - intros g args output. rewrite row_replace_fresh by exact Habsent.
      now rewrite allocate_id_view.
  Qed.
  (** Identifier equality is equality of representatives. *)
  Lemma same_repr : forall db i j, wf db ->
    (same (view db) i j <-> repr db i = repr db j).
  Proof.
    intros db i j Hwf. exact (wf_equalities db Hwf i j).
  Qed.
  (** Every representative represents itself. *)
  Lemma repr_idem : forall db i, wf db -> repr db (repr db i) = repr db i.
  Proof.
    intros db i Hwf. apply UnionFind.repr_idem. exact (wf_forest db Hwf).
  Qed.

  (** Every initial slot query reads an empty index. *)
  Lemma index_init_empty : forall ds sl s new, index s new (init ds sl) = I.empty.
  Proof.
    intros ds sl s new. unfold index. destruct new;
      cbn [init db_runtime runtime_slot_bound runtime_all_indexes runtime_new_indexes];
      destruct (N.compare (N.of_nat (length sl)) s); try reflexivity;
      now rewrite PTrie.get_empty.
  Qed.

  (** Initialization has no stored row of any kind. *)
  Lemma init_rows_empty : forall ds sl f k o, ~ row (view (init ds sl)) f k o.
  Proof.
    intros ds sl f k o Hrow.
    change (row_get f k (init ds sl) = Some o) in Hrow.
    unfold row_get in Hrow. cbn [init db_runtime runtime_rows] in Hrow.
    rewrite PTrie.get_empty in Hrow. discriminate.
  Qed.

  (** Every declared function fits the maximum name recorded by initialization. *)
  Lemma init_kind_bound : forall ds sl f output,
    kind (view (init ds sl)) f = Some output ->
    (f <= runtime_max_name (db_runtime (init ds sl)))%positive.
  Proof.
    intros ds sl f output Hkind.
    change (PTrieCode.get f (database_kinds ds) = Some output) in Hkind.
    unfold database_kinds in Hkind. rewrite declaration_trie_lookup in Hkind.
    exact (lookup_kind_name_bound ds f output Hkind).
  Qed.

  (** Empty row and count tries give every initial projection multiplicity zero. *)
  Lemma init_projection_counts : forall ds sl, projection_counts_ok (init ds sl).
  Proof.
    intros ds sl s f perm u _. exists []. split; [constructor |]. split.
    - intro r.
      assert (Hempty : RowMap.elements (runtime_rows (db_runtime (init ds sl))) = [])
        by reflexivity.
      rewrite Hempty. cbn [In]. tauto.
    - unfold stored_projection_count, projection_table_get.
      cbn [init db_runtime runtime_projection_counts].
      rewrite PTrie.get_empty. cbn. rewrite PTrie.get_empty. reflexivity.
  Qed.

  (** Initialization creates a well-formed database. *)
  Lemma wf_init : forall ds sl, wf (init ds sl).
  Proof.
    intros ds sl. unfold wf, database_wf.
    split; [apply UnionFind.wf_empty |].
    split.
    { intro i. change (PTrieCode.get i (@PTrieCode.empty positive) <> None <->
        (Npos i <= 0)%N). rewrite PTrie.get_empty. split; intro H; [contradiction | lia]. }
    split; [reflexivity |].
    split; [change (0 <= 0); lia |].
    split; [intros i j; apply equality_log_empty |].
    split; [constructor |].
    split; [apply RowMap.wf_empty |].
    split; [intros f k o Hrow; exfalso; exact (init_rows_empty ds sl f k o Hrow) |].
    split; [intros f k o i Hrow; exfalso; exact (init_rows_empty ds sl f k o Hrow) |].
    split; [intros f k o Hrow; exfalso; exact (init_rows_empty ds sl f k o Hrow) |].
    split; [exact (init_kind_bound ds sl) |].
    split; [reflexivity |]. split; [reflexivity |]. split; [constructor |].
    split.
    { intros _ f k o Hrow. exfalso. exact (init_rows_empty ds sl f k o Hrow). }
    split.
    { intros s new u Hmem. rewrite index_init_empty in Hmem.
      exfalso. exact (I.mem_empty u Hmem). }
    split.
    { intros s f perm k o _ Hrow. exfalso. exact (init_rows_empty ds sl f k o Hrow). }
    split.
    { intros s new f perm _. rewrite index_init_empty. apply I.wf_empty. }
    split; [reflexivity |]. apply init_projection_counts.
  Qed.

  (** Kind-correct insertion keeps the database well formed. *)
  Lemma wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Proof. Admitted. (* STUB *)

  (** Constructor allocation keeps the database well formed. *)
  Lemma wf_make : forall f k db, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    wf (snd (make f k db)).
  Proof. Admitted. (* STUB *)

  (** Rebuilding keeps the database well formed. *)
  Lemma wf_rebuild : forall db, wf db -> wf (rebuild db).
  Proof. Admitted. (* STUB *)

  (** Advancing preserves every full slot index exactly. *)
  Lemma index_advance_all : forall s db, index s false (advance db) = index s false db.
  Proof.
    reflexivity.
  Qed.

  (** Advancing clears every delta slot index, including out-of-range queries. *)
  Lemma index_advance_new : forall s db, index s true (advance db) = I.empty.
  Proof.
    intros s db.
    change ((match N.compare (runtime_slot_bound (db_runtime db)) s with
      | Gt => match PTrieCode.get (N.succ_pos s) (@PTrieCode.empty I.t) with
        | Some ix => ix
        | None => I.empty
        end
      | _ => I.empty
      end) = I.empty).
    destruct (N.compare (runtime_slot_bound (db_runtime db)) s); try reflexivity.
    now rewrite PTrie.get_empty.
  Qed.

  (** Advancing clears the change flag without changing the view. *)
  Lemma wf_advance : forall db, wf db ->
    wf (advance db) /\ view (advance db) = view db /\ changed (advance db) = false.
  Proof.
    intros db Hwf. split.
    - unfold wf, database_wf in Hwf |- *.
      destruct Hwf as (Hforest & Hmembers & Hcount & Hwidth & Hequalities & Hlog &
        Hrows & Hkind & Hrowids & Hslots & Hbound & Hslotbound & Hpending & Hqueue &
        Hcanonical & Hsound & Hcomplete & Harity & Hgroups & Hcounts).
      do 15 (split; [assumption |]).
      split.
      + intros s new u Hmem. destruct new.
        * rewrite index_advance_new in Hmem. exfalso. exact (I.mem_empty u Hmem).
        * rewrite index_advance_all in Hmem. exact (Hsound s false u Hmem).
      + split.
        * intros s f perm k o Hslot Hrow. rewrite index_advance_all.
          exact (Hcomplete s f perm k o Hslot Hrow).
        * split.
          -- intros s new f perm Hslot. destruct new.
             ++ rewrite index_advance_new. apply I.wf_empty.
             ++ rewrite index_advance_all. exact (Harity s false f perm Hslot).
          -- split; assumption.
    - split; reflexivity.
  Qed.

  (** Find returns the representative without changing the view. *)
  Lemma find_spec : forall i db, wf db ->
    fst (find i db) = repr db i /\ view (snd (find i db)) = view db.
  Proof.
    intros i db Hwf. split.
    - apply UnionFind.find_repr. exact (wf_forest db Hwf).
    - reflexivity.
  Qed.

  (** Each function key has one output. *)
  Lemma row_functional : forall db f k o1 o2, wf db ->
    row (view db) f k o1 -> row (view db) f k o2 -> o1 = o2.
  Proof.
    intros db f k o1 o2 _ Hfirst Hsecond.
    change (row_get f k db = Some o1) in Hfirst.
    change (row_get f k db = Some o2) in Hsecond. congruence.
  Qed.

  (** A raised change flag stays raised until the database advances. *)
  Lemma changed_put : forall f k o db, changed db = true -> changed (put f k o db) = true.
  Proof.
    intros f k o db Hchanged. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hnext : changed next = true).
    { unfold next. destruct previous as [[[a | v] |] |];
        destruct co as [[b | w] |]; try exact Hchanged.
      unfold union. destruct (UnionFindCode.union a b (db_forest db)) as [roots forest].
      destruct roots as [[winner loser] |]; [reflexivity | exact Hchanged]. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hnext | apply row_replace_changed].
    - apply row_replace_changed.
  Qed.
  Lemma changed_make : forall f k db,
    changed db = true -> changed (snd (make f k db)) = true.
  Proof.
    intros f k db Hchanged. unfold make.
    destruct (row_get f (normal_key db k) db) as [[[j | v] |] |]; try exact Hchanged;
      destruct (kind_get f db) as [[| |m] |]; reflexivity.
  Qed.
  Lemma changed_union : forall i j db, changed db = true -> changed (union i j db) = true.
  Proof.
    intros i j db Hchanged. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; [reflexivity | exact Hchanged].
  Qed.
  Lemma changed_rebuild : forall db, changed db = true -> changed (rebuild db) = true.
  Proof. Admitted. (* STUB *)
  (** Find and lookup leave the change flag alone. *)
  Lemma changed_find : forall i db, changed (snd (find i db)) = changed db.
  Proof.
    reflexivity.
  Qed.
  Lemma changed_lookup : forall f k db, changed (snd (lookup f k db)) = changed db.
  Proof.
    intros f k db. unfold lookup.
    destruct (Pos.compare (runtime_max_name (db_runtime db)) f); reflexivity.
  Qed.
  (** A union raises the flag only when it adds an equality. *)
  Lemma union_changed : forall i j db, wf db -> changed db = false ->
    changed (union i j db) = true -> ~ same (view db) i j.
  Proof.
    intros i j db Hwf Hquiet Hchanged Hsame. unfold union in Hchanged.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    destruct roots as [[winner loser] |].
    - destruct (UnionFind.union_some i j (db_forest db) winner loser forest
        (wf_forest db Hwf) Hunion) as [Hdifferent _].
      apply Hdifferent. exact (proj1 (same_repr db i j Hwf) Hsame).
    - change (changed db = true) in Hchanged. congruence.
  Qed.
  (** A make raises the flag only when it allocates. *)
  Lemma make_changed : forall f k db, wf db -> changed db = false ->
    changed (snd (make f k db)) = true ->
    ~ exists j, row (view db) f (map (canon db) k) (Some (Id j)).
  Proof.
    intros f k db Hwf Hquiet Hchanged [j Hrow]. unfold make in Hchanged.
    rewrite (normal_key_correct db k Hwf) in Hchanged.
    change (row_get f (map (canon db) k) db = Some (Some (Id j))) in Hrow.
    rewrite Hrow in Hchanged. change (changed db = true) in Hchanged. congruence.
  Qed.
  (** Rebuilding a canonical database that is closed under congruence leaves the flag alone. *)
  Lemma rebuild_quiet : forall db, wf db -> canonical db ->
    (forall i j, cong db i j -> same (view db) i j) -> changed (rebuild db) = changed db.
  Proof. Admitted. (* STUB *)

  (** Make reuses a canonical constructor output or allocates a fresh identifier. *)
  Lemma make_spec : forall f k db, wf db -> kind (view db) f = Some OId ->
    let '(i, db') := make f k db in
    (exists j, row (view db) f (map (canon db) k) (Some (Id j)) /\
      i = repr db j /\ db' = db) \/
    (fresh_id db i /\ row (view db') f (map (canon db) k) (Some (Id i)) /\
      extends_by db db' f k i).
  Proof.
    intros f k db Hwf Hkind. unfold make.
    rewrite (normal_key_correct db k Hwf). fold (old db f (map (canon db) k)).
    remember (old db f (map (canon db) k)) as previous eqn:Hprevious.
    destruct previous as [before |].
    - destruct (constructor_old db f (map (canon db) k) before Hwf Hkind
        (eq_sym Hprevious)) as [j ->].
      left. exists j. split; [exact (eq_sym Hprevious) |]. split; [| reflexivity].
      apply UnionFind.find_repr. exact (wf_forest db Hwf).
    - change (kind_get f db = Some OId) in Hkind. rewrite Hkind.
      right. split; [reflexivity |]. split.
      + apply row_replace_binding. right. split; reflexivity.
      + apply fresh_constructor_extension. exact (eq_sym Hprevious).
  Qed.

  (** Union adds precisely the requested equality closure. *)
  Lemma union_same : forall i j db k l, wf db ->
    (same (view (union i j db)) k l <->
      clos_refl_sym_trans positive (fun a b => same (view db) a b \/ (a, b) = (i, j)) k l).
  Proof.
    intros i j db k l Hwf. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    destruct roots as [[winner loser] |].
    - apply equality_log_cons.
    - change (equality_log (runtime_equalities (db_runtime db)) k l <->
        clos_refl_sym_trans positive
          (fun a b => equality_log (runtime_equalities (db_runtime db)) a b \/
            (a, b) = (i, j)) k l).
      rewrite <- equality_log_cons. symmetry. apply equality_log_redundant.
      apply (proj2 (same_repr db i j Hwf)).
      exact (proj1 (UnionFind.union_none i j (db_forest db) forest
        (wf_forest db Hwf) Hunion)).
  Qed.

  (** Union queues equality work without changing rows. *)
  Lemma union_rows : forall i j db, wf db ->
    row (view (union i j db)) = row (view db).
  Proof.
    intros i j db _. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Database union retains exactly the forest returned by the concrete union operation. *)
  Lemma union_forest : forall i j db,
    db_forest (union i j db) = snd (UnionFindCode.union i j (db_forest db)).
  Proof.
    intros i j db. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Union never changes the database allocation interval. *)
  Lemma union_ids : forall i j db, ids (union i j db) = ids db.
  Proof.
    intros i j db. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Union of allocated endpoints keeps the forest's exact membership interval. *)
  Lemma union_forest_members : forall i j db, wf db -> allocated db i -> allocated db j ->
    forall x, UnionFind.mem (db_forest (union i j db)) x <-> allocated (union i j db) x.
  Proof.
    intros i j db Hwf Hi Hj x. rewrite union_forest.
    unfold allocated. rewrite union_ids.
    apply UnionFindCodeFacts.members_union_present.
    - exact (wf_forest db Hwf).
    - exact (wf_forest_members db Hwf).
    - exact Hi.
    - exact Hj.
  Qed.

  (** Already allocated union endpoints add no forest members or counter charge. *)
  Lemma union_forest_count : forall i j db, wf db -> allocated db i -> allocated db j ->
    count (db_forest (union i j db)) = ids (union i j db).
  Proof.
    intros i j db Hwf Hi Hj. rewrite union_forest, union_ids.
    rewrite UnionFindCodeFacts.count_union_present.
    - exact (wf_forest_count db Hwf).
    - exact (proj2 (wf_forest_members db Hwf i) Hi).
    - exact (proj2 (wf_forest_members db Hwf j) Hj).
  Qed.

  (** The preserved allocation interval bounds all forest keys after union. *)
  Lemma union_forest_width : forall i j db, wf db -> allocated db i -> allocated db j ->
    UnionFind.width (db_forest (union i j db)) <= N.size_nat (ids (union i j db)).
  Proof.
    intros i j db Hwf Hi Hj. apply UnionFindCodeFacts.width_allocated.
    intros x Hmember. exact (proj1 (union_forest_members i j db Hwf Hi Hj x) Hmember).
  Qed.

  (** The updated equality log describes exactly the updated forest classes. *)
  Lemma union_equalities : forall i j db, wf db -> forall a b,
    same (view (union i j db)) a b <-> repr (union i j db) a = repr (union i j db) b.
  Proof.
    intros i j db Hwf a b. rewrite (union_same i j db a b Hwf).
    unfold repr. rewrite union_forest.
    rewrite (ForestFacts.union_same_closure i j (db_forest db) a b (wf_forest db Hwf)).
    apply equality_closure_equiv. intros x y. rewrite (same_repr db x y Hwf). tauto.
  Qed.

  (** A recorded union adds only its two allocated endpoints to the equality log. *)
  Lemma union_log_allocated : forall i j db, wf db -> allocated db i -> allocated db j ->
    Forall (fun edge => allocated (union i j db) (fst edge) /\
      allocated (union i j db) (snd edge)) (runtime_equalities (db_runtime (union i j db))).
  Proof.
    intros i j db Hwf Hi Hj. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |].
    - change (Forall (fun edge => allocated db (fst edge) /\ allocated db (snd edge))
        ((i, j) :: runtime_equalities (db_runtime db))).
      constructor; [now split | exact (wf_log_allocated db Hwf)].
    - exact (wf_log_allocated db Hwf).
  Qed.

  (** The losing representative queued by union is allocated. *)
  Lemma union_queue_allocated : forall i j db, wf db -> allocated db i -> allocated db j ->
    Forall (allocated (union i j db)) (runtime_queue (db_runtime (union i j db))).
  Proof.
    intros i j db Hwf Hi Hj.
    pose proof (UnionFindCodeFacts.repr_allocated (db_forest db) (ids db)
      (wf_forest db Hwf) (wf_forest_members db Hwf)) as Hrepresentative.
    unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    destruct roots as [[winner loser] |].
    - change (Forall (allocated db) (loser :: runtime_queue (db_runtime db))).
      constructor.
      + destruct (UnionFind.union_some i j (db_forest db) winner loser forest
          (wf_forest db Hwf) Hunion) as [_ [Hroots _]].
        destruct Hroots as [[_ Hloser] | [_ Hloser]]; rewrite Hloser.
        * exact (Hrepresentative j Hj).
        * exact (Hrepresentative i Hi).
      + exact (wf_queue_allocated db Hwf).
    - exact (wf_queue_allocated db Hwf).
  Qed.

  (** The stored pending counter follows exactly the optional queue insertion. *)
  Lemma union_pending_count : forall i j db, wf db ->
    db_npending (union i j db) = N.of_nat (pending (union i j db)).
  Proof.
    intros i j db Hwf. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |].
    - change (N.succ (db_npending db) = N.of_nat (S (pending db))).
      now rewrite Nat2N.inj_succ, (wf_pending_count db Hwf).
    - exact (wf_pending_count db Hwf).
  Qed.

  (** A union with an empty resulting queue has changed no representative. *)
  Lemma union_quiet_canonical : forall i j db, wf db ->
    pending (union i j db) = 0 -> canonical (union i j db).
  Proof.
    intros i j db Hwf Hquiet. unfold union in Hquiet |- *.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    destruct roots as [[winner loser] |].
    - change (S (pending db) = 0) in Hquiet. discriminate.
    - change (pending db = 0) in Hquiet. intros f k o Hrow x Hin.
      change (UnionFind.repr forest x = x).
      rewrite (proj2 (UnionFind.union_none i j (db_forest db) forest
        (wf_forest db Hwf) Hunion) x).
      exact (wf_quiet_canonical db Hwf Hquiet f k o Hrow x Hin).
  Qed.

  (** Equality insertion keeps the database well formed. *)
  Lemma wf_union : forall i j db, wf db -> allocated db i -> allocated db j ->
    wf (union i j db).
  Proof.
    intros i j db Hwf Hi Hj.
    assert (Hforest : UnionFind.wf (db_forest (union i j db))).
    { rewrite union_forest. apply UnionFind.wf_union. exact (wf_forest db Hwf). }
    pose proof (union_forest_members i j db Hwf Hi Hj) as Hmembers.
    pose proof (union_forest_count i j db Hwf Hi Hj) as Hcount.
    pose proof (union_forest_width i j db Hwf Hi Hj) as Hwidth.
    pose proof (union_equalities i j db Hwf) as Hequalities.
    pose proof (union_log_allocated i j db Hwf Hi Hj) as Hlog.
    pose proof (union_pending_count i j db Hwf) as Hpending.
    pose proof (union_queue_allocated i j db Hwf Hi Hj) as Hqueue.
    pose proof (union_quiet_canonical i j db Hwf) as Hcanonical.
    unfold wf, database_wf in Hwf |- *. unfold union in *.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |];
      cbn [fst snd database_set_forest database_set_runtime database_set_pending
        runtime_set_union db_forest db_runtime db_npending runtime_allocated
        runtime_rows runtime_kinds runtime_slots runtime_equalities runtime_queue
        runtime_all_indexes runtime_new_indexes runtime_projection_counts
        runtime_function_slots runtime_max_name runtime_slot_bound
        view row same kind row_get kind_get repr allocated ids pending slots slot_of
        index canonical slots_fit projection_counts_ok stored_projection_count] in *; tauto.
  Qed.

  (** Rebuilding canonicalizes every row and empties pending work. *)
  Lemma rebuild_canonical : forall db, wf db ->
    canonical (rebuild db) /\ pending (rebuild db) = 0.
  Proof. Admitted. (* STUB *)

  (** Rebuilding computes functional-dependency congruence. *)
  Lemma rebuild_same : forall db i j, wf db ->
    (same (view (rebuild db)) i j <-> cong db i j).
  Proof. Admitted. (* STUB *)

  (** Every old row survives canonicalization and output merging. *)
  Lemma rebuild_keeps : forall db f k o, wf db -> row (view db) f k o ->
    exists o', row (view (rebuild db)) f (map (canon (rebuild db)) k) o' /\
      out_le (rebuild db) f (option_map (canon (rebuild db)) o) o'.
  Proof. Admitted. (* STUB *)

  (** Every rebuilt row comes from a nonempty group of old rows. *)
  Lemma rebuild_from : forall db f k' o', wf db -> row (view (rebuild db)) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view db) f (fst ko) (snd ko) /\
        map (canon (rebuild db)) (fst ko) = k') srcs /\
      o' = merged (rebuild db) f (map snd srcs).
  Proof. Admitted. (* STUB *)

  (** Canonical databases without pending work rebuild to themselves. *)
  Lemma rebuild_idle : forall db, wf db -> canonical db -> pending db = 0 -> rebuild db = db.
  Proof. Admitted. (* STUB *)

  (** Related keys whose identifiers are already representatives are equal cell by cell. *)
  Lemma canonical_keys_equal : forall db (k1 k2 : list (cell V.t)), wf db ->
    (forall i, In (Id i) k1 -> repr db i = i) ->
    (forall i, In (Id i) k2 -> repr db i = i) ->
    Forall2 (cell_rel (same (view db))) k1 k2 -> k1 = k2.
  Proof.
    intros db k1 k2 Hwf Hleft Hright Hrelated. revert Hleft Hright.
    induction Hrelated as [| c d left right Hcell Htail IH]; intros Hleft Hright.
    - reflexivity.
    - f_equal.
      + destruct Hcell as [i j Hsame | v]; [| reflexivity].
        f_equal. apply (proj1 (same_repr db i j Hwf)) in Hsame.
        rewrite (Hleft i), (Hright j) in Hsame by now left. exact Hsame.
      + apply IH.
        * intros i Hin. apply Hleft. now right.
        * intros i Hin. apply Hright. now right.
  Qed.

  (** A database without pending work respects constructor congruence. *)
  Lemma rebuild_congruent : forall db f k1 k2 i j, wf db -> pending db = 0 ->
    row (view db) f k1 (Some (Id i)) -> row (view db) f k2 (Some (Id j)) ->
    Forall2 (cell_rel (same (view db))) k1 k2 -> same (view db) i j.
  Proof.
    intros db f k1 k2 i j Hwf Hquiet Hrow1 Hrow2 Hrelated.
    pose proof (wf_quiet_canonical db Hwf Hquiet) as Hcanonical.
    assert (Hkeys : k1 = k2).
    { eapply canonical_keys_equal; [exact Hwf | | | exact Hrelated].
      - intros x Hin. apply (Hcanonical f k1 (Some (Id i)) Hrow1 x).
        apply in_or_app. now left.
      - intros x Hin. apply (Hcanonical f k2 (Some (Id j)) Hrow2 x).
        apply in_or_app. now left. }
    subst k2.
    pose proof (row_functional db f k1 (Some (Id i)) (Some (Id j)) Hwf Hrow1 Hrow2)
      as Houtputs.
    injection Houtputs as ->. apply (proj2 (same_repr db j j Hwf)). reflexivity.
  Qed.

  (** Every indexed tuple comes from a row in its declared slot. *)
  Lemma index_all : forall db s new u, wf db -> I.mem (index s new db) u ->
    exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
      u = permute perm (k ++ option_list o).
  Proof.
    intros db s new u Hwf. exact (wf_index_sound db Hwf s new u).
  Qed.

  (** The full index contains every row in its slot. *)
  Lemma index_all_complete : forall db s f perm k o, wf db ->
    slot_of db s = Some (f, perm) -> row (view db) f k o ->
    I.mem (index s false db) (permute perm (k ++ option_list o)).
  Proof.
    intros db s f perm k o Hwf. exact (wf_index_complete db Hwf s f perm k o).
  Qed.

  (** Slot indexes have the declared permutation arity. *)
  Lemma index_wf : forall db s new f perm, wf db -> slot_of db s = Some (f, perm) ->
    I.wf (length perm) (index s new db).
  Proof.
    intros db s new f perm Hwf. exact (wf_index_arity db Hwf s new f perm).
  Qed.

  (** Stored lookup agrees with the public row observation. *)
  Lemma old_row : forall db f k o, wf db ->
    (old db f k = Some o <-> row (view db) f k o).
  Proof.
    intros db f k o _. reflexivity.
  Qed.

  (** Every stored row has a declared function within the stored name bound. *)
  Lemma row_name_bound : forall db f k o, wf db -> row (view db) f k o ->
    (f <= runtime_max_name (db_runtime db))%positive.
  Proof.
    intros db f k o Hwf Hrow.
    destruct (kind (view db) f) as [output |] eqn:Hkind.
    - exact (wf_kind_bound db Hwf f output Hkind).
    - pose proof (wf_row_kind db Hwf f k o Hrow) as Hshape.
      rewrite Hkind in Hshape. destruct o as [[i | v] |]; contradiction.
  Qed.

  (** A function above the stored name bound cannot have a row. *)
  Lemma row_get_outside : forall db f k, wf db ->
    (runtime_max_name (db_runtime db) < f)%positive -> row_get f k db = None.
  Proof.
    intros db f k Hwf Houtside.
    destruct (row_get f k db) as [o |] eqn:Hrow; [| reflexivity].
    pose proof (row_name_bound db f k o Hwf Hrow) as Hbound. exfalso. lia.
  Qed.

  (** Lookup canonicalizes its query and keeps the view and invariant. *)
  Lemma lookup_spec : forall f k db, wf db ->
    fst (lookup f k db) = old db f (map (canon db) k) /\
    view (snd (lookup f k db)) = view db /\ wf (snd (lookup f k db)).
  Proof.
    intros f k db Hwf. unfold lookup, old.
    rewrite (normal_key_correct db k Hwf).
    destruct (Pos.compare (runtime_max_name (db_runtime db)) f) eqn:Hcompare;
      cbn [fst snd].
    - split; [reflexivity |]. split; [reflexivity | exact Hwf].
    - split.
      + apply Pos.compare_lt_iff in Hcompare. symmetry.
        exact (row_get_outside db f (map (canon db) k) Hwf Hcompare).
      + split; [reflexivity | exact Hwf].
    - split; [reflexivity |]. split; [reflexivity | exact Hwf].
  Qed.

  (** Initialization records declarations and slots and starts empty. *)
  Lemma init_view : forall ds sl f k o i j,
    (row (view (init ds sl)) f k o <-> False) /\
    (same (view (init ds sl)) i j <-> i = j) /\
    kind (view (init ds sl)) f = lookup_kind ds f /\
    slots (init ds sl) = sl /\ ids (init ds sl) = 0%N /\ pending (init ds sl) = 0.
  Proof.
    intros ds sl f k o i j. split.
    - change (row_get f k (init ds sl) = Some o <-> False).
      unfold row_get. cbn [init db_runtime runtime_rows].
      rewrite PTrie.get_empty. cbn. split; [discriminate | contradiction].
    - split; [apply equality_log_empty |]. split.
      + change (PTrieCode.get f (database_kinds ds) = lookup_kind ds f).
        unfold database_kinds. apply declaration_trie_lookup.
      + repeat split; reflexivity.
  Qed.

  (** Make keeps layout and returns an allocated identifier. *)
  Lemma layout_make : forall f k db, wf db ->
    kind (view (snd (make f k db))) = kind (view db) /\
    slots (snd (make f k db)) = slots db /\
    (ids (snd (make f k db)) <= N.succ (ids db))%N /\
    allocated (snd (make f k db)) (fst (make f k db)) /\
    pending (snd (make f k db)) = pending db.
  Proof.
    intros f k db Hwf. unfold make. rewrite (normal_key_correct db k Hwf).
    destruct (row_get f (map (canon db) k) db) as [[[j | v] |] |] eqn:Hrow;
      try apply fresh_make_layout.
    cbn [fst snd]. split; [reflexivity |]. split; [reflexivity |].
    split; [lia |]. split; [| reflexivity].
    rewrite (UnionFind.find_repr j (db_forest db) (wf_forest db Hwf)).
    unfold allocated. eapply UnionFindCodeFacts.repr_allocated.
    - exact (wf_forest db Hwf).
    - intro i. exact (wf_forest_members db Hwf i).
    - eapply (wf_row_ids db Hwf f (map (canon db) k) (Some (Id j)) j).
      + exact Hrow.
      + apply in_or_app. right. now left.
  Qed.

  (** Union keeps layout and allocation and queues at most one loser. *)
  Lemma layout_union : forall i j db, wf db ->
    kind (view (union i j db)) = kind (view db) /\ slots (union i j db) = slots db /\
    ids (union i j db) = ids db /\ pending (union i j db) <= pending db + 1.
  Proof.
    intros i j db _. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |].
    - split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      change (S (pending db) <= pending db + 1). lia.
    - split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      change (pending db <= pending db + 1). lia.
  Qed.

  (** Rebuilding keeps layout and allocation. *)
  Lemma layout_rebuild : forall db, wf db ->
    kind (view (rebuild db)) = kind (view db) /\ slots (rebuild db) = slots db /\
    ids (rebuild db) = ids db.
  Proof. Admitted. (* STUB *)

  (** Advancing keeps the slot layout. *)
  Lemma layout_advance : forall db, slots (advance db) = slots db.
  Proof.
    reflexivity.
  Qed.
  (** Advancing keeps allocation, pending work and representatives. *)
  Lemma advance_keeps : forall db, wf db ->
    ids (advance db) = ids db /\ pending (advance db) = pending db /\
    repr (advance db) = repr db.
  Proof.
    intros db _. repeat split; reflexivity.
  Qed.

  (** A quiet union already holds in the old view. *)
  Lemma union_quiet : forall i j db, wf db -> changed db = false ->
    changed (union i j db) = false -> same (view db) i j.
  Proof.
    intros i j db Hwf _ Hquiet. unfold union in Hquiet.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    destruct roots as [[winner loser] |].
    - discriminate Hquiet.
    - apply (proj2 (same_repr db i j Hwf)).
      exact (proj1 (UnionFind.union_none i j (db_forest db) forest
        (wf_forest db Hwf) Hunion)).
  Qed.

  (** A quiet make reuses a constructor row. *)
  Lemma make_quiet : forall f k db, wf db -> changed db = false ->
    changed (snd (make f k db)) = false ->
    exists j, row (view db) f (map (canon db) k) (Some (Id j)).
  Proof.
    intros f k db Hwf _ Hquiet. unfold make in Hquiet.
    rewrite (normal_key_correct db k Hwf) in Hquiet.
    destruct (row_get f (map (canon db) k) db) as [[[j | v] |] |] eqn:Hrow.
    - exists j. exact Hrow.
    - destruct (kind_get f db) as [[| |m] |]; discriminate Hquiet.
    - destruct (kind_get f db) as [[| |m] |]; discriminate Hquiet.
    - destruct (kind_get f db) as [[| |m] |]; discriminate Hquiet.
  Qed.

  (** Every row identifier is allocated. *)
  Lemma row_allocated : forall db f k o i, wf db -> row (view db) f k o ->
    In (Id i) (k ++ option_list o) -> allocated db i.
  Proof.
    intros db f k o i Hwf. exact (wf_row_ids db Hwf f k o i).
  Qed.

  (** Rebuilding keeps every satisfying model and identifier interpretation. *)
  Lemma rebuild_sat : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> sat V.merge M nu (view (rebuild db)).
  Proof. Admitted. (* STUB *)

  (** The executable output merge is the frozen public combination operation. *)
  Lemma combine_output_correct : forall db f previous o,
    combine_output db f previous o = combine db f previous o.
  Proof.
    reflexivity.
  Qed.

  (** Resolving an output conflict retains every stored row. *)
  Lemma output_conflict_rows : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)), wf db ->
    row (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) = row (view db).
  Proof.
    intros db previous co Hwf.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
      try reflexivity; apply union_rows; exact Hwf.
  Qed.

  (** Resolving an output conflict retains the declared function kinds. *)
  Lemma output_conflict_kind : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)), wf db ->
    kind (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) = kind (view db).
  Proof.
    intros db previous co Hwf.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |]; try reflexivity.
    exact (proj1 (layout_union a b db Hwf)).
  Qed.

  (** Conflict resolution preserves layout and allocation and queues at most one loser. *)
  Lemma output_conflict_layout : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)), wf db ->
    let next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end in
    kind (view next) = kind (view db) /\ slots next = slots db /\ ids next = ids db /\
    pending next <= pending db + 1.
  Proof.
    intros db previous co Hwf.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
      try solve [repeat split; lia].
    exact (layout_union a b db Hwf).
  Qed.

  (** A union with a clear result flag leaves the complete model view unchanged. *)
  Lemma union_quiet_view : forall i j db, changed (union i j db) = false ->
    view (union i j db) = view db.
  Proof.
    intros i j db Hquiet. unfold union in Hquiet |- *.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; [discriminate Hquiet | reflexivity].
  Qed.

  (** Quiet output-conflict resolution preserves the model view. *)
  Lemma output_conflict_quiet_view : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)),
    let next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end in
    changed next = false -> view next = view db.
  Proof.
    intros db previous co. cbn zeta. intro Hquiet.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |]; try reflexivity.
    exact (union_quiet_view a b db Hquiet).
  Qed.

  (** Every equality from an output conflict follows from the old relation and that conflict. *)
  Lemma output_conflict_same_sources : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)), wf db -> forall i j,
    same (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) i j ->
    clos_refl_sym_trans positive
      (fun x y => same (view db) x y \/
        (previous = Some (Some (Id x)) /\ co = Some (Id y))) i j.
  Proof.
    intros db previous co Hwf i j Hsame.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
      try solve [apply rst_step; now left].
    pose proof (proj1 (union_same a b db i j Hwf) Hsame) as Hclosure.
    eapply equality_closure_mono; [| exact Hclosure].
    intros x y [Hold | Hpair]; [now left |].
    right. injection Hpair as -> ->. split; reflexivity.
  Qed.

  (** The logged equality relation is closed under equivalence reasoning. *)
  Lemma same_closed : forall db R,
    (forall a b, R a b -> same (view db) a b) ->
    forall i j, clos_refl_sym_trans positive R i j -> same (view db) i j.
  Proof.
    intros db R Hgenerators i j Hclosure.
    induction Hclosure as [i j Hstep | i | i j Hstep IH | i j k Hleft IHleft Hright IHright].
    - exact (Hgenerators i j Hstep).
    - apply equality_log_refl.
    - now apply equality_log_sym.
    - eapply equality_log_trans; eassumption.
  Qed.

  (** An output conflict adds exactly the equivalence closure of its two outputs. *)
  Lemma output_conflict_same : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)), wf db -> forall i j,
    same (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) i j <->
    clos_refl_sym_trans positive
      (fun x y => same (view db) x y \/
        (previous = Some (Some (Id x)) /\ co = Some (Id y))) i j.
  Proof.
    intros db previous co Hwf i j. split.
    - apply output_conflict_same_sources. exact Hwf.
    - intro Hclosure.
      destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
        try solve [refine (same_closed db _ _ i j Hclosure);
          intros x y [Hold | [Ha Hb]]; [exact Hold | congruence]].
      apply (proj2 (union_same a b db i j Hwf)).
      eapply equality_closure_mono; [| exact Hclosure].
      intros x y [Hold | [Ha Hb]]; [now left |].
      right. injection Ha as ->. injection Hb as ->. reflexivity.
  Qed.

  (** Insertion retains the declaration table through conflicts and row replacement. *)
  Lemma put_kind_effect : forall db f k o, wf db ->
    kind (view (put f k o db)) = kind (view db).
  Proof.
    intros db f k o Hwf. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hkind : kind (view next) = kind (view db)).
    { apply output_conflict_kind. exact Hwf. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hkind |].
      now rewrite row_replace_kind.
    - now rewrite row_replace_kind.
  Qed.

  (** The only inserted row is the canonical key with its combined output. *)
  Lemma put_row_sources : forall db f k o, wf db -> forall g args output,
    row (view (put f k o db)) g args output ->
      row (view db) g args output \/
      (g = f /\ args = map (canon db) k /\
        output = combine db f (old db f (map (canon db) k)) (option_map (canon db) o)).
  Proof.
    intros db f k o Hwf g args output. unfold put.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    rewrite combine_output_correct. fold (old db f (map (canon db) k)).
    remember (old db f (map (canon db) k)) as previous.
    remember (option_map (canon db) o) as co.
    set (updated := combine db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hrows : row (view next) = row (view db)).
    { apply output_conflict_rows. exact Hwf. }
    intro Hrow. destruct previous as [before |].
    - destruct (output_eqb before updated).
      + left. now rewrite <- Hrows.
      + apply row_replace_sources in Hrow as [Hold | Hnew].
        * left. now rewrite <- Hrows.
        * now right.
    - apply row_replace_sources in Hrow as [Hold | Hnew].
      + left. now rewrite <- Hrows.
      + now right.
  Qed.

  (** Insertion only adds equality consequences justified by the old and requested outputs. *)
  Lemma put_same_sources : forall db f k o, wf db -> forall i j,
    same (view (put f k o db)) i j ->
    clos_refl_sym_trans positive
      (fun x y => same (view db) x y \/ conflict db f k o x y) i j.
  Proof.
    intros db f k o Hwf i j. unfold put, conflict.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    fold (old db f (map (canon db) k)).
    remember (old db f (map (canon db) k)) as previous.
    remember (option_map (canon db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hsame : forall a b, same (view next) a b ->
      clos_refl_sym_trans positive
        (fun x y => same (view db) x y \/
          (previous = Some (Some (Id x)) /\ co = Some (Id y))) a b).
    { apply output_conflict_same_sources. exact Hwf. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [apply Hsame |].
      rewrite row_replace_same. apply Hsame.
    - rewrite row_replace_same. apply Hsame.
  Qed.

  (** Insertion changes precisely the canonical key and combines its output. *)
  Lemma put_rows : forall f k o db, wf db -> kind_ok db f k o ->
    let ck := map (canon db) k in let co := option_map (canon db) o in
    forall f' k' o', row (view (put f k o db)) f' k' o' <->
      (row (view db) f' k' o' /\ (f', k') <> (f, ck)) \/
      (f' = f /\ k' = ck /\ combine db f (old db f ck) co = o').
  Proof.
    intros f k o db Hwf _. cbn zeta. intros g args output. unfold put.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    rewrite combine_output_correct. fold (old db f (map (canon db) k)).
    remember (old db f (map (canon db) k)) as previous eqn:Hprevious.
    remember (option_map (canon db) o) as co.
    set (updated := combine db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hrows : row (view next) = row (view db)).
    { apply output_conflict_rows. exact Hwf. }
    destruct previous as [before |].
    - destruct (output_eqb_spec before updated) as [Hequal | Hdifferent].
      + rewrite Hrows, <- Hequal. apply row_unchanged_binding. exact (eq_sym Hprevious).
      + now rewrite row_replace_rows, Hrows.
    - now rewrite row_replace_rows, Hrows.
  Qed.

  (** Identifier output conflicts add precisely their equality closure. *)
  Lemma put_same : forall f k o db i j, wf db -> kind_ok db f k o ->
    (same (view (put f k o db)) i j <->
      clos_refl_sym_trans positive
        (fun a b => same (view db) a b \/ conflict db f k o a b) i j).
  Proof.
    intros f k o db i j Hwf _. unfold put, conflict.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    fold (old db f (map (canon db) k)).
    remember (old db f (map (canon db) k)) as previous.
    remember (option_map (canon db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hsame : same (view next) i j <->
      clos_refl_sym_trans positive
        (fun x y => same (view db) x y \/
          (previous = Some (Some (Id x)) /\ co = Some (Id y))) i j).
    { apply output_conflict_same. exact Hwf. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hsame |].
      now rewrite row_replace_same.
    - now rewrite row_replace_same.
  Qed.

  (** Insertion keeps layout and allocation and queues at most one loser. *)
  Lemma layout_put : forall f k o db, wf db ->
    kind (view (put f k o db)) = kind (view db) /\ slots (put f k o db) = slots db /\
    ids (put f k o db) = ids db /\ pending (put f k o db) <= pending db + 1.
  Proof.
    intros f k o db Hwf. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hlayout : kind (view next) = kind (view db) /\ slots next = slots db /\
      ids next = ids db /\ pending next <= pending db + 1).
    { apply output_conflict_layout. exact Hwf. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hlayout |].
      now rewrite row_replace_kind, row_replace_slots, row_replace_ids, row_replace_pending.
    - now rewrite row_replace_kind, row_replace_slots, row_replace_ids, row_replace_pending.
  Qed.

  (** Combining an already represented output leaves the stored output unchanged. *)
  Lemma combine_out_le : forall db f o before, out_le db f o before ->
    combine db f (Some before) (option_map (canon db) o) = before.
  Proof.
    intros db f o before Hle.
    destruct o as [[i | v] |]; destruct before as [[j | w] |];
      cbn [out_le cell_le option_map canon] in Hle; try contradiction; try reflexivity;
      try solve [unfold combine; destruct (kind (view db) f) as [[| |m] |]; reflexivity].
    destruct Hle as [m [Hkind Hmerge]]. unfold combine. rewrite Hkind.
    cbn [option_map canon]. rewrite V.merge_comm, Hmerge. reflexivity.
  Qed.

  (** A represented insertion only performs its possible identifier conflict union. *)
  Lemma put_present_operation : forall db f k o before, wf db ->
    row (view db) f (map (canon db) k) before -> out_le db f o before ->
    put f k o db =
      match before, option_map (canon db) o with
      | Some (Id a), Some (Id b) => union a b db | _, _ => db end.
  Proof.
    intros db f k o before Hwf Hrow Hle. unfold put.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    change (row_get f (map (canon db) k) db = Some before) in Hrow. rewrite Hrow.
    rewrite combine_output_correct, (combine_out_le db f o before Hle), output_eqb_refl.
    reflexivity.
  Qed.

  (** An insertion raises the flag only when its row was not represented. *)
  Lemma put_changed : forall f k o db, wf db -> kind_ok db f k o -> changed db = false ->
    changed (put f k o db) = true -> ~ present_put (view db) f (map (canon db) k) o.
  Proof.
    intros f k o db Hwf _ Hquiet Hchanged [before [Hrow Hle]].
    rewrite (put_present_operation db f k o before Hwf Hrow Hle) in Hchanged.
    destruct o as [[i | v] |]; destruct before as [[j | w] |];
      try solve [change (changed db = true) in Hchanged; congruence].
    change (changed (union j (repr db i) db) = true) in Hchanged.
    apply (union_changed j (repr db i) db Hwf Hquiet Hchanged).
    apply (proj2 (same_repr db j (repr db i) Hwf)).
    rewrite (repr_idem db i Hwf). symmetry.
    exact (proj1 (same_repr db i j Hwf) Hle).
  Qed.

  (** A quiet, unchanged output already contains the kind-correct requested output. *)
  Lemma quiet_output_le : forall db f k o before, wf db -> kind_ok db f k o ->
    old db f (map (canon db) k) = Some before ->
    before = combine db f (Some before) (option_map (canon db) o) ->
    changed db = false ->
    changed (match before, option_map (canon db) o with
      | Some (Id a), Some (Id b) => union a b db | _, _ => db end) = false ->
    out_le db f o before.
  Proof.
    intros db f k o before Hwf [_ [_ Hshape]] Hprevious Hequal Hquiet Hnext.
    pose proof (wf_row_kind db Hwf f (map (canon db) k) before Hprevious) as Hbefore.
    destruct (kind (view db) f) as [[| |m] |] eqn:Hkind in Hshape, Hbefore;
      destruct o as [[i | v] |]; destruct before as [[j | w] |];
      cbn in Hshape, Hbefore; try contradiction.
    - exact I.
    - change (changed (union j (repr db i) db) = false) in Hnext.
      pose proof (union_quiet j (repr db i) db Hwf Hquiet Hnext) as Hsame.
      apply (proj2 (same_repr db i j Hwf)).
      pose proof (proj1 (same_repr db j (repr db i) Hwf) Hsame) as Hrepr.
      rewrite (repr_idem db i Hwf) in Hrepr. symmetry. exact Hrepr.
    - exists m. split; [exact Hkind |].
      unfold combine in Hequal. rewrite Hkind in Hequal. cbn [option_map canon] in Hequal.
      injection Hequal as Hequal. rewrite V.merge_comm. symmetry. exact Hequal.
  Qed.

  (** A quiet insertion already has its requested row represented. *)
  Lemma put_quiet : forall f k o db, wf db -> kind_ok db f k o ->
    changed db = false -> changed (put f k o db) = false ->
    view (put f k o db) = view db /\ present_put (view db) f (map (canon db) k) o.
  Proof.
    intros f k o db Hwf Hkind Hquiet Hnew. unfold put in Hnew |- *.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf) in Hnew |- *.
    rewrite combine_output_correct in Hnew |- *. fold (old db f (map (canon db) k)) in Hnew |- *.
    remember (old db f (map (canon db) k)) as previous eqn:Hprevious in Hnew |- *.
    set (co := option_map (canon db) o) in Hnew |- *.
    set (updated := combine db f previous co) in Hnew |- *.
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end) in Hnew |- *.
    destruct previous as [before |].
    - destruct (output_eqb_spec before updated) as [Hequal | Hdifferent].
      + split.
        * exact (output_conflict_quiet_view db (Some before) co Hnew).
        * exists before. split; [exact (eq_sym Hprevious) |].
          exact (quiet_output_le db f k o before Hwf Hkind (eq_sym Hprevious)
            Hequal Hquiet Hnew).
      + rewrite row_replace_changed in Hnew. discriminate Hnew.
    - rewrite row_replace_changed in Hnew. discriminate Hnew.
  Qed.

  (** Canonicalization preserves every cell's denotation in a satisfying model. *)
  Lemma canon_den : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> forall c, den nu (canon db c) = den nu c.
  Proof.
    intros M nu db Hwf Hsat [i | v]; cbn [canon den]; [| reflexivity].
    f_equal.
    apply (sat_same V.merge M nu (view db) (repr db i) i Hsat).
    apply (proj2 (same_repr db (repr db i) i Hwf)).
    apply repr_idem. exact Hwf.
  Qed.

  (** Canonicalizing a tuple preserves all of its interpreted arguments. *)
  Lemma canon_key_den : forall (M : model (V := V.t)) nu db k, wf db ->
    sat V.merge M nu (view db) -> map (den nu) (map (canon db) k) = map (den nu) k.
  Proof.
    intros M nu db k Hwf Hsat. rewrite map_map. apply map_ext.
    intro c. exact (canon_den M nu db Hwf Hsat c).
  Qed.

  (** Canonicalizing an optional output preserves its interpreted value. *)
  Lemma canon_output_den : forall (M : model (V := V.t)) nu db o, wf db ->
    sat V.merge M nu (view db) ->
    option_map (den nu) (option_map (canon db) o) = option_map (den nu) o.
  Proof.
    intros M nu db [c |] Hwf Hsat; cbn [option_map]; [| reflexivity].
    now rewrite (canon_den M nu db Hwf Hsat c).
  Qed.

  (** Inserting a true, kind-correct row keeps the model. *)
  Lemma put_sat : forall (M : model (V := V.t)) nu db f k o, wf db -> kind_ok db f k o ->
    sat V.merge M nu (view db) -> holds M nu (view db) f k o ->
    sat V.merge M nu (view (put f k o db)).
  Proof.
    intros M nu db f k o Hwf _ Hsat Hholds.
    eapply (@sat_put_view V.t V.merge M nu (view db) (view (put f k o db)) f k o
      (map (canon db) k) (option_map (canon db) o) (old db f (map (canon db) k))).
    - exact Hsat.
    - exact (put_kind_effect db f k o Hwf).
    - intros previous Hprevious. exact Hprevious.
    - exact (canon_key_den M nu db k Hwf Hsat).
    - exact (canon_output_den M nu db o Hwf Hsat).
    - exact Hholds.
    - exact (put_row_sources db f k o Hwf).
    - exact (put_same_sources db f k o Hwf).
  Qed.

  (** A justified identifier union keeps the model. *)
  Lemma union_sat : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> nu i = nu j ->
    sat V.merge M nu (view (union i j db)).
  Proof.
    intros M nu db i j Hwf Hsat Hequal.
    eapply sat_union_view with (w := view db) (i := i) (j := j).
    - exact (proj1 (layout_union i j db Hwf)).
    - exact (union_rows i j db Hwf).
    - intros a b Hsame.
      pose proof (proj1 (union_same i j db a b Hwf) Hsame) as Hclosure.
      eapply equality_closure_mono; [| exact Hclosure].
      intros x y [Hold | Hpair].
      + now left.
      + right. now injection Hpair as -> ->.
    - exact Hsat.
    - exact Hequal.
  Qed.

  (** The next positive identifier is outside the current allocation interval. *)
  Lemma fresh_id_unallocated : forall db i, fresh_id db i -> ~ allocated db i.
  Proof.
    intros db i Hfresh. unfold fresh_id in Hfresh. subst i. unfold allocated.
    assert (Hnext : Npos (N.succ_pos (ids db)) = N.succ (ids db)).
    { destruct (ids db); reflexivity. }
    rewrite Hnext. lia.
  Qed.

  (** A representative of an allocated identifier is still allocated. *)
  Lemma repr_allocated : forall db i, wf db -> allocated db i -> allocated db (repr db i).
  Proof.
    intros db i Hwf Hi. unfold allocated, repr.
    eapply UnionFindCodeFacts.repr_allocated.
    - exact (wf_forest db Hwf).
    - intro j. exact (wf_forest_members db Hwf j).
    - exact Hi.
  Qed.

  (** Canonicalizing an allocated tuple does not introduce an unallocated identifier. *)
  Lemma canon_key_allocated : forall db k, wf db ->
    (forall j, In (Id j) k -> allocated db j) ->
    forall i, In (Id i) (map (canon db) k) -> allocated db i.
  Proof.
    intros db k Hwf Hargs i Hin.
    apply in_map_iff in Hin as [c [Hcell Hin]].
    destruct c as [j | v]; cbn [canon] in Hcell; [| discriminate Hcell].
    injection Hcell as <-. apply repr_allocated; [exact Hwf | exact (Hargs j Hin)].
  Qed.

  (** A satisfying interpretation gives each identifier and its representative one meaning. *)
  Lemma repr_den : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> forall i, nu (repr db i) = nu i.
  Proof.
    intros M nu db Hwf Hsat i.
    apply (sat_same V.merge M nu (view db) (repr db i) i Hsat).
    apply (proj2 (same_repr db (repr db i) i Hwf)).
    apply repr_idem. exact Hwf.
  Qed.

  (** A fresh constructor extension preserves the model after assigning its new output. *)
  Lemma fresh_extension_sat : forall (M : model (V := V.t)) nu db db' f k i,
    wf db -> fresh_id db i -> extends_by db db' f k i ->
    kind (view db) f = Some OId ->
    (forall j, In (Id j) k -> allocated db j) -> sat V.merge M nu (view db) ->
    exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con M f (map (den nu) k) /\ sat V.merge M nu' (view db').
  Proof.
    intros M nu db db' f k i Hwf Hfresh [_ [Hkinds [Hsame Hrows]]] Hkind Hargs Hsat.
    pose proof (fresh_id_unallocated db i Hfresh) as Hnot.
    assert (Hmodel : exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con M f (map (den nu) (map (canon db) k)) /\ sat V.merge M nu' (view db')).
    { eapply (@sat_fresh_constructor_view V.t V.merge M nu (view db) (view db')
        f (map (canon db) k) i).
      - exact Hsat.
      - exact Hkinds.
      - intros g args output Hrow Hin. apply Hnot.
        exact (wf_row_ids db Hwf g args output i Hrow Hin).
      - exact (equality_log_fresh_occurs (runtime_equalities (db_runtime db))
          (allocated db) (wf_log_allocated db Hwf) i Hnot).
      - exact Hsame.
      - exact Hrows.
      - exact Hkind.
      - intro Hin. apply Hnot. exact (canon_key_allocated db k Hwf Hargs i Hin). }
    destruct Hmodel as [nu' [Hkeep [Hmeaning Hsat']]].
    exists nu'. split; [exact Hkeep |]. split; [| exact Hsat'].
    now rewrite (canon_key_den M nu db k Hwf Hsat) in Hmeaning.
  Qed.

  (** Make updates its output meaning and keeps every other identifier meaning. *)
  Lemma make_sat : forall (M : model (V := V.t)) nu db f k, wf db ->
    kind (view db) f = Some OId ->
    (forall j, In (Id j) k -> allocated db j) ->
    sat V.merge M nu (view db) ->
    let '(i, db') := make f k db in
    exists nu', (forall j, j <> i -> nu' j = nu j) /\
      nu' i = con M f (map (den nu) k) /\ sat V.merge M nu' (view db').
  Proof.
    intros M nu db f k Hwf Hkind Hargs Hsat.
    remember (make f k db) as result eqn:Hmake. destruct result as [i db'].
    pose proof (make_spec f k db Hwf Hkind) as Hspec. rewrite <- Hmake in Hspec.
    destruct Hspec as [[j [Hrow [Hi Hdb]]] | [Hfresh [_ Hextension]]].
    - subst db' i. exists nu. split; [reflexivity |]. split; [| exact Hsat].
      rewrite (repr_den M nu db Hwf Hsat j). symmetry.
      pose proof (sat_constructor V.merge M nu (view db) f (map (canon db) k) j Hsat Hrow)
        as Hconstructor.
      now rewrite (canon_key_den M nu db k Hwf Hsat) in Hconstructor.
    - exact (fresh_extension_sat M nu db db' f k i Hwf Hfresh Hextension Hkind Hargs Hsat).
  Qed.

End Database.

Module DatabaseT (V : VALUE_T) (I : INDEX_T V) <: DATABASE_ALL V I.
  Include Database V I.
  (* spec: wmark potential *)
  (* STUB-CODE *)
  Definition wmark (db : t) : N := db_wmark db.
  Definition unit (db : t) : nat :=
    (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Definition slots_of (db : t) (f : positive) : nat :=
    length (filter (fun s => Pos.eqb (fst s) f) (slots db)).
  (* STUB-CODE *)
  Definition potential (_ : N) (_ : t) : N := 0%N.
  Definition num_slots (db : t) : nat := length (slots db).
  TimeFun db_cell_code db_cell_eqb db_tuple_code db_row_code row_get kind_get.
  TimeFun normal_cell normal_key output_eqb combine_output.
  TimeFun slot_index_get projection_table_get slot_update_one slot_update_many.
  TimeFun slots_update row_write row_replace.
  TimeFun init.
  TimeFun find.
  TimeFun lookup.
  TimeFun union.
  TimeFun allocate_id.
  TimeFun make.
  TimeFun put.
  TimeFun db_rstep.
  TimeFun db_rebuild_fuel.
  TimeFun rebuild.
  TimeFun index.
  TimeFun advance.
  TimeFun changed.
  TimeFun ids.
  Definition c_db : N := 1. (* STUB *)
  (** Initialization starts without amortized debt. *)
  Lemma potential_init : forall B ds sl, (potential B (init ds sl) = 0)%N.
  Proof. Admitted. (* STUB *)

  (** Insertion pays for all slots and the logarithmic identifier budget. *)
  Lemma T_put_amort : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * potential B (put f k o db) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Constructor allocation has the same amortized budget as insertion. *)
  Lemma T_make_amort : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * potential B (snd (make f k db)) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Union transfers the deferred work to potential. *)
  Lemma T_union_amort : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * potential B (union i j db) <=
      N.of_nat (unit (union i j db)) * (c_db + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Rebuilding spends potential on pending union work. *)
  Lemma T_rebuild_amort : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild db + N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** Slot lookup pays for the slot code. *)
  Lemma T_index_le : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Advancing visits every slot. *)
  Lemma T_advance_le : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The high-water mark covers every stored cell encoding. *)
  Lemma wmark_cells : forall db f k o c, wf db -> row (view db) f k o ->
    In c (k ++ option_list o) -> cell_bits V.encode c <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** The high-water mark covers every declared function name. *)
  Lemma wmark_names : forall db f, wf db -> kind (view db) f <> None ->
    Pos.size_nat f <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** The high-water mark covers every slot index. *)
  Lemma wmark_index : forall db s new, wf db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** Insertion never reduces the spending unit. *)
  Lemma unit_mono_put : forall f k o db, wf db -> unit db <= unit (put f k o db).
  Proof. Admitted. (* STUB *)

  (** Make never reduces the spending unit. *)
  Lemma unit_mono_make : forall f k db, wf db -> unit db <= unit (snd (make f k db)).
  Proof. Admitted. (* STUB *)

  (** Union never reduces the spending unit. *)
  Lemma unit_mono_union : forall i j db, wf db -> unit db <= unit (union i j db).
  Proof. Admitted. (* STUB *)

  (** Rebuilding never reduces the spending unit. *)
  Lemma unit_mono_rebuild : forall db, wf db -> unit db <= unit (rebuild db).
  Proof. Admitted. (* STUB *)
  (** Advancing keeps the watermark and the amortized credit. *)
  Lemma advance_credit : forall B db, wf db ->
    wmark (advance db) = wmark db /\ (potential B (advance db) = potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** Initialization pays for declarations and slot permutations. *)
  Lemma T_init_le : forall ds sl,
    (T_init ds sl <= c_db * N.of_nat (length ds + length sl + layout_work sl + 1) *
      N.of_nat ((fold_right (fun s n => length (snd s) + n) 0 sl + 1)%nat) +
      c_db * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** Find traverses allocated identifiers at the database unit. *)
  Lemma T_find_le : forall i db, wf db -> allocated db i ->
    (T_find i db <= c_db * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (** Lookup charges the stored unit and query cell encodings. *)
  Lemma T_lookup_le : forall f k db, wf db ->
    (T_lookup f k db <= c_db * N.of_nat (length k + 1) * N.of_nat (unit db) +
      c_db * N.of_nat ((fold_right (fun c n => cell_bits V.encode c + n) 0 k)%nat))%N.
  Proof. Admitted. (* STUB *)

  (** The change flag is stored. *)
  Lemma T_changed_le : forall db, (T_changed db <= c_db)%N.
  Proof. Admitted. (* STUB *)

  (** The allocation counter is stored. *)
  Lemma T_ids_le : forall db, (T_ids db <= c_db)%N.
  Proof. Admitted. (* STUB *)

  Definition use_entry := (positive * list (cell V.t))%type.
  Definition stored_row := (use_entry * option (cell V.t))%type.
  Definition repair_state := (t * list use_entry)%type.

  (* spec: rows uses_entries queue next_id forest_ok class_size uf_state
     index_counters written_cells *)
  (* STUB-CODE *)
  Definition rows : t -> list stored_row := fun _ => [].
  (* STUB-CODE *)
  Definition uses_entries : t -> list (positive * use_entry) := fun _ => [].
  (* STUB-CODE *)
  Definition queue : t -> list positive := fun _ => [].
  (* STUB-CODE *)
  Definition next_id : t -> positive := fun _ => 1%positive.
  (* STUB-CODE *)
  Definition uf_state (db : t) : UnionFind.t := db_forest db.
  (* STUB-CODE *)
  Definition class_size (db : t) (x : positive) : N :=
    N.of_nat (UnionFind.size_of (uf_state db) x).
  (** A historical row key resolves to its current stored key. *)
  (* STUB-CODE *)
  Definition located (_ : t) (_ : positive) (_ : list (cell V.t))
      : option (list (cell V.t)) := None.
  (** Located keys resolve to stored rows of declared functions. *)
  Definition forest_ok (db : t) : Prop :=
    forall f k0 k, located db f k0 = Some k ->
      exists o, In ((f, k), o) (rows db) /\ kind (view db) f <> None.
  Definition k_credit : N := 1. (* STUB *)
  Definition k_loop : N := 1. (* STUB *)
  Definition k_active : N := 1. (* STUB *)
  Definition k_queue : N := 1. (* STUB *)
  Definition k_stop : N := 1. (* STUB *)
  Definition k_driver : N := 1. (* STUB *)

  Definition uses (db : t) (x : positive) (e : use_entry) : Prop :=
    In (x, e) (uses_entries db).
  Definition scheduled (db : t) (work : list use_entry) (e : use_entry) : Prop :=
    In e work \/ exists x, In x (queue db) /\ uses db x e.
  Definition row_ids (k : list (cell V.t)) (o : option (cell V.t)) (i : positive) : Prop :=
    In (Id i) (k ++ option_list o).

  (** Located historical keys resolve to stored rows of declared functions. *)
  Lemma F_forest_located : forall db f k0 k, forest_ok db -> located db f k0 = Some k ->
    exists o, In ((f, k), o) (rows db) /\ kind (view db) f <> None.
  Proof.
    intros db f k0 k Hforest Hlocated. exact (Hforest f k0 k Hlocated).
  Qed.

  (** Active entries retain coverage after their loser has left the queue. *)
  Definition inv_on (db : t) (work : list use_entry) : Prop :=
    (forall f k o, In ((f, k), o) (rows db) <-> row (view db) f k o) /\
    NoDup (map fst (rows db)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i ->
      exists x k0, repr db x = repr db i /\ uses db x (f, k0) /\
        located db f k0 = Some k /\ (x = repr db i \/ In x (queue db))) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i -> repr db i <> i ->
      exists k0, scheduled db work (f, k0) /\ located db f k0 = Some k) /\
    (forall s f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s false db) /\
      I.wf (length perm) (index s true db) /\
      (forall u, I.mem (index s false db) u <->
        exists k o, row (view db) f k o /\ u = permute perm (k ++ option_list o)) /\
      (forall u, I.mem (index s true db) u -> I.mem (index s false db) u)) /\
    (forall f k o i, row (view db) f k o -> row_ids k o i ->
      (i < next_id db)%positive) /\
    (forall e, In e work -> exists x, uses db x e) /\
    forest_ok db /\
    (forall f k o, row (view db) f k o -> kind_ok db f k o) /\
    NoDup (queue db) /\ pending db = length (queue db) /\
    (forall x, In x (queue db) -> allocated db x).
  Definition output_equiv (db : t) (a b : option (cell V.t)) : Prop :=
    match a, b with
    | None, None => True
    | Some c, Some d => cell_rel (same (view db)) c d
    | _, _ => False
    end.
  Definition inv (db : t) : Prop := inv_on db [].
  Definition state_inv (s : repair_state) : Prop := inv_on (fst s) (snd s).

  Definition entry_weight (db : t) (e : use_entry) : nat :=
    (length (snd e) + 1) * (slots_of db (fst e) + 1).
  Definition bucket (db : t) (x : positive) : list use_entry :=
    map snd (filter (fun xe => Pos.eqb (fst xe) x) (uses_entries db)).
  Definition use_credit (B : N) (db : t) (xe : positive * use_entry) : nat :=
    N.to_nat (N.log2 B - N.log2 (class_size db (repr db (fst xe)))) *
        entry_weight db (snd xe).
  Definition work_weight (db : t) (work : list use_entry) : nat :=
    fold_right (fun e n => entry_weight db e + n) 0 work.
  Definition queue_weight (db : t) : nat :=
    fold_right (fun x n => work_weight db (bucket db x) + 1 + n) 0 (queue db).
  Definition rebuild_potential (B : N) (db : t) : N :=
    (k_credit * N.of_nat (fold_right (fun xe n => (use_credit B db xe + n)%nat) 0%nat
      (uses_entries db)) + k_queue * N.of_nat (queue_weight db))%N.
  Definition state_potential (B : N) (s : repair_state) : N :=
    (rebuild_potential B (fst s) +
      k_active * N.of_nat (work_weight (fst s) (snd s)))%N.
  (* STUB-CODE *)
  Definition nuses (db : t) : N := db_nuses db.
  (* STUB-CODE *)
  Definition npending (db : t) : N := db_npending db.
  (* STUB-CODE *)
  Definition index_counters (db : t) : list positive := db_index_counters db.
  (* STUB-CODE *)
  Definition written_cells (db : t) : list (cell V.t) := db_written_cells db.
  (* STUB-CODE *)
  Definition decl_names (_ : t) : list positive := [].
  (* STUB-CODE *)
  Definition get_uses : positive -> t -> list use_entry := fun _ _ => [].
  TimeFun get_uses.
  (* STUB-CODE *)
  Definition pop_loser : t -> option (positive * t) := fun _ => None.
  TimeFun pop_loser.
  (* STUB-CODE *)
  Definition repair_entry : use_entry -> t -> t := fun _ db => db.
  TimeFun repair_entry.
  (* STUB-CODE *)
  Definition rstep (s : repair_state) : repair_state + t := db_rstep s.
  TimeFun rstep.
  (* STUB-CODE *)
  Definition rebuild_fuel (db : t) : N := db_rebuild_fuel db.
  TimeFun rebuild_fuel.

  TimeFun locate.
  TimeFun rank_slots.
  Definition k_locate : N := 1. (* STUB *)
  Definition k_repair : N := 1. (* STUB *)
  Definition k_pop : N := 1. (* STUB *)
  Definition k_rstep : N := 1. (* STUB *)
  Definition k_slots : N := 1. (* STUB *)
  Definition k_layout : N := 1. (* STUB *)

  (* spec: row_id row_parent row_size row_current next_row *)
  (* STUB-CODE *)
  Definition row_id (_ : t) (_ : positive) (_ : list (cell V.t)) : option positive := None.
  (* STUB-CODE *)
  Definition row_parent (_ : t) (r : positive) : positive := r.
  (* STUB-CODE *)
  Definition row_size (_ : t) (_ : positive) : N := 1%N.
  (* STUB-CODE *)
  Definition row_current (_ : t) (_ : positive) : option (list (cell V.t)) := None.
  (* STUB-CODE *)
  Definition next_row (_ : t) : positive := 1%positive.
  (** Following the merge parent of a row identifier [n] times. *)
  Definition row_up (db : t) (n : nat) (r : positive) : positive :=
    Nat.iter n (row_parent db) r.
  (** A historical key resolves through a merge chain of logarithmic depth. *)
  Lemma F_row_locate : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    exists d, d <= length k * (N.to_nat (N.log2 (ids db)) + 1) /\
      row_parent db (row_up db d r) = row_up db d r /\
      located db f k = row_current db (row_up db d r).
  Proof. Admitted. (* STUB *)
  (** A key without a row identifier has no current row. *)
  Lemma F_row_absent : forall db work f k, inv_on db work -> row_id db f k = None ->
    located db f k = None.
  Proof. Admitted. (* STUB *)
  (** The executable resolution agrees with the observation. *)
  Lemma F_locate : forall db work f k, inv_on db work -> locate f k db = located db f k.
  Proof. Admitted. (* STUB *)
  (** Merged row groups at least double the losing group. *)
  Lemma F_row_by_size : forall db work r, inv_on db work -> row_parent db r <> r ->
    (1 <= row_size db r)%N /\ (2 * row_size db r <= row_size db (row_parent db r))%N.
  Proof. Admitted. (* STUB *)
  (** A row group holds at most one row per assignment of its identifier positions. *)
  Lemma F_row_group : forall db work f k r d, inv_on db work -> row_id db f k = Some r ->
    row_parent db (row_up db d r) = row_up db d r ->
    (row_size db (row_up db d r) <= (ids db + 1) ^ N.of_nat (length k))%N.
  Proof. Admitted. (* STUB *)
  (** Row identifiers stay below a counter that the watermark covers. *)
  Lemma F_row_counter : forall db work f k r, inv_on db work -> row_id db f k = Some r ->
    (r < next_row db)%positive /\ (row_parent db r < next_row db)%positive /\
    In (next_row db) (index_counters db).
  Proof. Admitted. (* STUB *)
  (** The keys of use entries are written cells. *)
  Lemma F_entry_cells : forall db work x f k c, inv_on db work -> uses db x (f, k) ->
    In c k -> In c (written_cells db).
  Proof. Admitted. (* STUB *)
  (** Resolution reads the key once and follows the chain at the stored width. *)
  Lemma T_locate_le : forall db work x f k, inv_on db work -> uses db x (f, k) ->
    (T_locate f k db <= k_locate * N.of_nat (length k + 1) * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** A repair, with its resolution, rekeying, slot updates and collision, pays its entry weight. *)
  Lemma T_repair_entry_le : forall db e rest, inv_on db (e :: rest) ->
    (T_repair_entry e db <= k_repair * N.of_nat (entry_weight db e) *
      N.of_nat (unit (repair_entry e db)))%N.
  Proof. Admitted. (* STUB *)

  (* spec: slot_place group_of group_slots proj_count slots_ok *)
  (* STUB-CODE *)
  Definition slot_place (_ : t) (_ : N) : option (bool * N * N) := None.
  (* STUB-CODE *)
  Definition group_of (_ : t) (_ : positive) : option N := None.
  (* STUB-CODE *)
  Definition group_slots (_ : t) (_ : bool) (_ : N) : list N := [].
  (** Slot facts survive changes to the row store between projection updates. *)
  Definition slots_ok (db : t) : Prop :=
    (forall s f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s false db) /\
      I.wf (length perm) (index s true db) /\
      exists d g j, slot_place db s = Some (d, g, j) /\ (g <= s)%N /\ (j <= s)%N /\
        nth_error (group_slots db d g) (N.to_nat j) = Some s /\
        (d = true <-> kind (view db) f <> None) /\
        (d = true -> group_of db f = Some g /\ (g < wmark db)%N)) /\
    (forall f g, group_of db f = Some g ->
      NoDup (group_slots db true g) /\
      forall s, In s (group_slots db true g) <-> exists perm, slot_of db s = Some (f, perm)) /\
    (forall s f perm new, slot_of db s = Some (f, perm) ->
      (Npos (I.next (index s new db)) <= wmark db)%N).
  (** Every slot has a place whose group rank and offset do not exceed the slot number. *)
  Lemma F_slot_place : forall db work s f perm, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists d g j, slot_place db s = Some (d, g, j) /\ (g <= s)%N /\ (j <= s)%N /\
      nth_error (group_slots db d g) (N.to_nat j) = Some s /\
      (d = true <-> kind (view db) f <> None) /\
      (d = true -> group_of db f = Some g /\ (g < wmark db)%N).
  Proof. Admitted. (* STUB *)
  (** A declared group lists precisely the slots of its function, once each. *)
  Lemma F_group_slots : forall db work f g, inv_on db work -> group_of db f = Some g ->
    NoDup (group_slots db true g) /\
    forall s, In s (group_slots db true g) <-> exists perm, slot_of db s = Some (f, perm).
  Proof. Admitted. (* STUB *)
  (** Initialization stores the ranking of its slot list. *)
  Lemma F_init_place : forall ds sl s,
    slot_place (init ds sl) s = nth_error (rank_slots ds sl) (N.to_nat s).
  Proof. Admitted. (* STUB *)
  (** Ranking pays for slot positions and the bits of function names. *)
  Lemma T_rank_slots_le : forall ds sl,
    (T_rank_slots ds sl <= k_layout * N.of_nat (length ds + length sl + layout_work sl + 1) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0%nat sl)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Initialization adds the ranking to one pass over declarations and permutations. *)
  Lemma T_init_split : forall ds sl,
    (T_init ds sl <= T_rank_slots ds sl +
      k_layout * N.of_nat (length ds + length sl + layout_work sl + 1) *
        N.of_nat ((fold_right (fun s n => length (snd s) + n) 0%nat sl + 1)%nat) +
      k_layout * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0%nat ds)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** One update of every slot of a declared function walks its group once. *)
  Lemma T_slots_update_le : forall db b f u, slots_ok db ->
    kind (view db) f <> None -> slots_fit db f (length u) ->
    (forall c, In c u -> cell_bits V.encode c <= N.size_nat (wmark (slots_update b f u db))) ->
    (T_slots_update b f u db <= k_slots * N.of_nat (slots_of db f + 1) *
      N.of_nat (length u + 1) *
      N.of_nat (unit (slots_update b f u db)))%N.
  Proof. Admitted. (* STUB *)

  (** A union finds both roots and links only distinct ones. *)
  Lemma F_union_roots : forall i j db, inv db -> allocated db i -> allocated db j ->
    let '(ri, u1) := UnionFind.find i (uf_state db) in
    let '(rj, u2) := UnionFind.find j u1 in
    uf_state (union i j db) =
      if Pos.eqb ri rj then u2 else snd (UnionFind.union ri rj u2).
  Proof. Admitted. (* STUB *)
  (** Membership and key width stay within allocation. *)
  Lemma F_uf_card : forall db work, inv_on db work ->
    UnionFind.card (uf_state db) <= 3 * N.to_nat (ids db) /\
    UnionFind.width (uf_state db) <= N.size_nat (ids db).
  Proof. Admitted. (* STUB *)

  Definition proj_count (db : t) (s : N) (u : list (cell V.t)) : N :=
    stored_projection_count db s u.
  (** The count of a projected tuple is the number of rows that project onto it. *)
  Lemma F_proj_count : forall db work s f perm u, inv_on db work ->
    slot_of db s = Some (f, perm) ->
    exists rs, NoDup rs /\
      (forall r, In r rs <-> In r (rows db) /\ fst (fst r) = f /\
        permute perm (snd (fst r) ++ option_list (snd r)) = u) /\
      N.to_nat (proj_count db s u) = length rs.
  Proof. Admitted. (* STUB *)

  (** The counter of the empty index is recorded. *)
  Lemma F_counter_one : forall db, inv db -> In 1%positive (index_counters db).
  Proof. Admitted. (* STUB *)

  (** The maintained invariant gives the slot facts that an update reads. *)
  Lemma F_slots_ok : forall db work, inv_on db work -> slots_ok db.
  Proof. Admitted. (* STUB *)
  (** A slot update keeps those facts. *)
  Lemma F_slots_ok_update : forall db b f u, slots_ok db ->
    slots_fit db f (length u) -> slots_ok (slots_update b f u db).
  Proof. Admitted. (* STUB *)

  (** A driver step costs its repair, or its pop and bucket read, plus a constant. *)
  Lemma T_rstep_split : forall db work,
    (T_rstep (db, work) <= k_rstep +
      match work with
      | e :: _ => T_repair_entry e db
      | [] => T_pop_loser db +
          match pop_loser db with
          | Some (x, _) => T_get_uses x db
          | None => 0
          end
      end)%N.
  Proof. Admitted. (* STUB *)
  (** A pop moves the selected bucket at one step per entry. *)
  Lemma T_pop_loser_le : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    (T_pop_loser db <= k_pop * N.of_nat (work_weight db (bucket db x) + 1) *
      N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** An empty pop reads the stored queue. *)
  Lemma T_pop_none_le : forall db, inv db -> pop_loser db = None ->
    (T_pop_loser db <= k_pop * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)
  (** A bucket is read by one keyed lookup. *)
  Lemma T_get_uses_le : forall db work x, inv_on db work -> allocated db x ->
    (T_get_uses x db <= k_pop * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (* STUB-CODE *)
  Definition rebuild_measure : repair_state -> nat := fun _ => 0.

  (** Public well-formedness is the maintained invariant at an empty active batch. *)
  Lemma F1_inv_wf : forall db, wf db <-> inv db.
  Proof. Admitted. (* STUB *)

  (** The public potential is the weighted occurrence credit. *)
  Lemma F2_potential : forall B db, (potential B db = k_loop * rebuild_potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** The unit charges identifier traversal and cell encoding widths. *)
  Lemma F3_unit : forall db,
    unit db = (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Proof. Admitted. (* STUB *)

  (** Direct bucket lookup agrees with the occurrence inventory. *)
  Lemma F4_bucket : forall db work x, inv_on db work -> get_uses x db = bucket db x.
  Proof. Admitted. (* STUB *)

  (** An empty pop detects an empty pending queue. *)
  Lemma F4_pop_none : forall db, inv db -> (pop_loser db = None <-> queue db = []).
  Proof. Admitted. (* STUB *)

  (** A pop transfers its selected bucket into the active work list. *)
  Lemma F4_pop : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    queue db = x :: queue db' /\ view db' = view db /\
    (forall y e, uses db' y e <->
      (uses db y e /\ y <> x) \/ (y = repr db x /\ uses db x e)) /\
    N.to_nat (nuses db') = length (uses_entries db') /\
    inv_on db' (bucket db x).
  Proof. Admitted. (* STUB *)

  (** The driver consumes one active entry or dequeues one loser. *)
  Lemma F5_rstep : forall db work,
    rstep (db, work) =
      match work with
      | e :: rest => inl (repair_entry e db, rest)
      | [] =>
        match pop_loser db with
        | None => inr db
        | Some (x, db') => inl (db', get_uses x db)
        end
      end.
  Proof. Admitted. (* STUB *)

  (** Entries without a current row are discarded without changing the database. *)
  Lemma F6_absent : forall db f k,
    located db f k = None -> repair_entry (f, k) db = db.
  Proof. Admitted. (* STUB *)

  (** Repair discharges one active occurrence and retains coverage of affected rows. *)
  Lemma F7_repair_inv : forall db e rest, inv_on db (e :: rest) ->
    inv_on (repair_entry e db) rest.
  Proof. Admitted. (* STUB *)

  (** Continuing steps retain the queue and active-batch invariant. *)
  Lemma F8_rstep_inv : forall s s', state_inv s -> rstep s = inl s' -> state_inv s'.
  Proof. Admitted. (* STUB *)

  (** Repair retains kinds and identifier allocation. *)
  Lemma F9_rstep_layout : forall s s', state_inv s -> rstep s = inl s' ->
    kind (view (fst s')) = kind (view (fst s)) /\ ids (fst s') = ids (fst s).
  Proof. Admitted. (* STUB *)

  (** Collision unions keep the same functional-dependency closure. *)
  Lemma F10_rstep_cong : forall s s' i j, state_inv s -> rstep s = inl s' ->
    (cong (fst s') i j <-> cong (fst s) i j).
  Proof. Admitted. (* STUB *)

  (** Every old row survives one step at an equivalent, possibly unfinished key. *)
  Lemma F11_rstep_keeps : forall s s' f k o, state_inv s -> rstep s = inl s' ->
    row (view (fst s)) f k o ->
    exists k' o', row (view (fst s')) f k' o' /\
      Forall2 (cell_rel (same (view (fst s')))) k k' /\
      out_le (fst s') f (option_map (canon (fst s')) o) o'.
  Proof. Admitted. (* STUB *)

  (** Every repaired row groups a nonempty list of rows from before the step. *)
  Lemma F12_rstep_from : forall s s' f k' o', state_inv s -> rstep s = inl s' ->
    row (view (fst s')) f k' o' ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view (fst s)) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view (fst s')))) (fst ko) k') srcs /\
      output_equiv (fst s') o' (merged (fst s') f (map snd srcs)).
  Proof. Admitted. (* STUB *)

  (** A stopped driver exposes canonical rows and constructor closure. *)
  Lemma F13_rstep_done : forall s r, state_inv s -> rstep s = inr r ->
    r = fst s /\ snd s = [] /\ inv r /\ canonical r /\ pending r = 0 /\
    (forall f k1 k2 i j, row (view r) f k1 (Some (Id i)) ->
      row (view r) f k2 (Some (Id j)) ->
      Forall2 (cell_rel (same (view r))) k1 k2 -> same (view r) i j).
  Proof. Admitted. (* STUB *)

  (** Continuing steps strictly decrease a measure that includes active work. *)
  Lemma F14_rstep_measure : forall s s', state_inv s -> rstep s = inl s' ->
    rebuild_measure s' < rebuild_measure s.
  Proof. Admitted. (* STUB *)

  (** Fuel budgets logarithmic relabelings of all stored use occurrences. *)
  Lemma F15_fuel_formula : forall db, rebuild_fuel db =
    ((N.size (ids db) + 2) * (nuses db + 1) + npending db + 1)%N.
  Proof.
    intro db. reflexivity.
  Qed.

  (** Computed fuel includes the final stop call. *)
  Lemma F15_fuel_enough : forall db, inv db ->
    (N.of_nat (rebuild_measure (db, [])) < rebuild_fuel db)%N.
  Proof. Admitted. (* STUB *)

  (** The rebuild operation runs the same step and fuel as the plan. *)
  Lemma F16_rebuild_run : forall db, wf db ->
    loopN rstep (rebuild_fuel db) (db, []) = inr (rebuild db).
  Proof. Admitted. (* STUB *)

  (** Congruent cells have equal denotations in every satisfying model. *)
  Lemma F17_cong_den : forall (M : model (V := V.t)) nu db i j, wf db ->
    sat V.merge M nu (view db) -> cong db i j -> nu i = nu j.
  Proof.
    intros M nu db i j _ Hsat Hcong.
    exact (fd_congruence_den V.merge M nu (view db) i j Hsat Hcong).
  Qed.

  (** Nonempty output groups keep their model meaning through the actual merge fold. *)
  Lemma F18_merged_holds : forall (M : model (V := V.t)) nu db f k os,
    wf db -> lat_closed V.merge M (view db) -> os <> [] -> (forall i, nu (repr db i) = nu i) ->
    Forall (holds M nu (view db) f k) os ->
    holds M nu (view db) f k (merged db f os).
  Proof.
    intros M nu db f k os _ Hlat Hnonempty Hrepr Hrows.
    assert (Hcanonical : Forall (holds M nu (view db) f k)
      (map (option_map (canon db)) os)).
    { apply Forall_map. eapply Forall_impl; [| exact Hrows].
      intros o Ho.
      exact (holds_output_rename M nu (repr db) Hrepr (view db) f k o Ho). }
    unfold merged.
    destruct (map (option_map (canon db)) os) as [| o rest] eqn:Houtputs.
    - destruct os; [contradiction | discriminate].
    - inversion Hcanonical as [| o0 rest0 Ho Hrest]; subst.
      clear Houtputs Hnonempty Hrows Hcanonical. revert o Ho.
      induction Hrest as [| next rest Hnext Hrest IH]; intros acc Hacc;
        cbn [fold_left].
      + exact Hacc.
      + apply IH. unfold combine.
        eapply (holds_combine V.merge M nu (view db) f k (Some acc) next Hlat).
        * intros previous Heq. inversion Heq; subst. exact Hacc.
        * exact Hnext.
  Qed.

  (** Repair preserves satisfaction through its collision, lattice and index branches. *)
  Lemma F19_rstep_sat : forall (M : model (V := V.t)) nu s s',
    state_inv s -> rstep s = inl s' -> sat V.merge M nu (view (fst s)) ->
    sat V.merge M nu (view (fst s')).
  Proof. Admitted. (* STUB *)

  (** Lineage retains original row groups throughout repeated deletion and reinsertion. *)
  Definition lineage (initial current : t) : Prop :=
    forall f k o, row (view current) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        Forall2 (cell_rel (same (view current))) (fst ko) k) srcs /\
      output_equiv current o (merged current f (map snd srcs)).
  (** Singleton source groups establish lineage before the first repair. *)
  Lemma F20_lineage_initial : forall db, inv db -> lineage db db.
  Proof. Admitted. (* STUB *)

  (** Actual repair flattens source groups through canonicalization and lattice merging. *)
  Lemma F21_lineage_step : forall initial s s', state_inv s ->
    rstep s = inl s' -> lineage initial (fst s) -> lineage initial (fst s').
  Proof. Admitted. (* STUB *)

  (** Stopped lineage gives the exact public output equation for each original group. *)
  Lemma F22_lineage_done : forall initial s r, inv initial -> state_inv s ->
    rstep s = inr r -> lineage initial r ->
    forall f k o, row (view r) f k o ->
    exists srcs, srcs <> [] /\
      Forall (fun ko => row (view initial) f (fst ko) (snd ko) /\
        map (canon r) (fst ko) = k) srcs /\ o = merged r f (map snd srcs).
  Proof. Admitted. (* STUB *)


  (** A losing root enters a class at least twice as large. *)
  Lemma T1_doubling : forall db i j x, inv db -> repr db x = x ->
    repr (union i j db) x <> x ->
    (2 * class_size db x <= class_size (union i j db) (repr (union i j db) x))%N.
  Proof. Admitted. (* STUB *)

  (** Initialization has no use-occurrence debt. *)
  Lemma T2_init_credit : forall B ds sl, (rebuild_potential B (init ds sl) = 0)%N.
  Proof. Admitted. (* STUB *)

  (** Insertion pays its executable work and new occurrence credit. *)
  Lemma T3_put_credit : forall B f k o db, wf db ->
    slots_fit db f (length (k ++ option_list o)) -> (ids (put f k o db) <= B)%N ->
    (T_put f k o db +
      N.of_nat (unit (put f k o db)) * (k_loop * rebuild_potential B (put f k o db)) <=
      N.of_nat (unit (put f k o db)) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Allocation pays new occurrences through the insertion budget. *)
  Lemma T4_make_credit : forall B f k db, wf db -> slots_fit db f (S (length k)) ->
    (ids (snd (make f k db)) <= B)%N ->
    (T_make f k db +
      N.of_nat (unit (snd (make f k db))) * (k_loop * rebuild_potential B (snd (make f k db))) <=
      N.of_nat (unit (snd (make f k db))) *
        (c_db * N.of_nat ((length k + 2) * (length k + 2)) *
          N.of_nat (slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Union pays its root link and queued repair credit. *)
  Lemma T5_union_credit : forall B i j db, wf db -> allocated db i -> allocated db j ->
    (ids db <= B)%N ->
    (T_union i j db +
      N.of_nat (unit (union i j db)) * (k_loop * rebuild_potential B (union i j db)) <=
      N.of_nat (unit (union i j db)) * (c_db + (k_loop * rebuild_potential B db)))%N.
  Proof. Admitted. (* STUB *)

  (** Continuing steps spend queued and active credit without a per-entry allowance. *)
  Lemma T6_rstep_go : forall B U s s', state_inv s -> (ids (fst s') <= B)%N ->
    unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + k_loop * N.of_nat U * state_potential B s' <
      k_loop * N.of_nat U * state_potential B s)%N.
  Proof. Admitted. (* STUB *)

  (** Stopping charges one unit of the final database. *)
  Lemma T7_rstep_stop : forall s r, state_inv s -> rstep s = inr r ->
    (T_rstep s <= k_stop * N.of_nat (unit (fst s)))%N.
  Proof. Admitted. (* STUB *)

  (** Continuing steps also pay the binary loop driver's per-step charge. *)
  Lemma T6a_rstep_credit : forall B U s s', state_inv s ->
    (ids (fst s') <= B)%N -> unit (fst s') <= U -> rstep s = inl s' ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * state_potential B s' <=
      k_loop * N.of_nat U * state_potential B s)%N.
  Proof. Admitted. (* STUB *)

  (** Stopping retains result credit and spends the reserved stop allowance. *)
  Lemma T7a_stop_credit : forall B U s r, state_inv s -> unit (fst s) <= U ->
    rstep s = inr r ->
    (T_rstep s + c_loopN + k_loop * N.of_nat U * rebuild_potential B r <=
      k_loop * N.of_nat U * state_potential B s + k_stop * N.of_nat U)%N.
  Proof. Admitted. (* STUB *)


  (** The actual loop must fit the public budget after all use-entry charges are summed. *)
  Lemma T8_rebuild_loop : forall B db, wf db -> (ids (rebuild db) <= B)%N ->
    (T_rebuild_fuel db + T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver +
      N.of_nat (unit (rebuild db)) * potential B (rebuild db) <=
      N.of_nat (unit (rebuild db)) *
        (c_db * N.of_nat (pending db + 1) + potential B db))%N.
  Proof. Admitted. (* STUB *)

  (** The wrapper exposes fuel construction and driver overhead. *)
  Lemma T9_rebuild_driver : forall db,
    (T_rebuild db <= T_rebuild_fuel db +
      T_loopN rstep T_rstep (rebuild_fuel db) (db, []) + k_driver)%N.
  Proof. Admitted. (* STUB *)

  (** Slot lookup charges its binary slot code. *)
  Lemma T10_index : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Advancing clears each maintained slot once. *)
  Lemma T11_advance : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Stored counters agree with the occurrence inventory and pending queue. *)
  Lemma F15_counts : forall db work, inv_on db work ->
    N.to_nat (nuses db) = length (uses_entries db) /\ N.of_nat (pending db) = npending db.
  Proof. Admitted. (* STUB *)

  (** The declaration inventory contains precisely the names with a kind. *)
  Lemma F_decl_names : forall db f, inv db ->
    (kind (view db) f <> None <-> In f (decl_names db)).
  Proof. Admitted. (* STUB *)

  (** The stored watermark is the exact historical maximum of written payloads and counters. *)
  Lemma F_wmark : forall db, inv db ->
    wmark db = fold_right N.max (N.max (nuses db) (ids db))
      (map Npos (index_counters db) ++ map Npos (decl_names db) ++
        map (fun c => match c with
          | Id i => Npos (xO i)
          | Val v => Npos (xI (V.encode v))
          end) (written_cells db)).
  Proof. Admitted. (* STUB *)

  (** Every slot index fits the stored counter and cell watermark. *)
  Lemma F_wmark_index : forall db s new, inv db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof. Admitted. (* STUB *)

  (** Class sizes come from the size-based union-find. *)
  Lemma F_uf_bridge : forall db work x, inv_on db work ->
    repr db x = UnionFind.repr (uf_state db) x /\
    class_size db x = N.of_nat (UnionFind.size_of (uf_state db) x) /\
    UnionFind.wf (uf_state db).
  Proof. Admitted. (* STUB *)

  (** Root classes are nonempty and bounded by allocation. *)
  Lemma F_class_size : forall db work x, inv_on db work ->
    (1 <= class_size db (repr db x))%N /\
    (class_size db (repr db x) <= N.max 1 (ids db))%N.
  Proof. Admitted. (* STUB *)

  (** Collision unions also double the losing class. *)
  Lemma F_rstep_doubling : forall s s' x, state_inv s -> rstep s = inl s' ->
    repr (fst s) x = x -> repr (fst s') x <> x ->
    (2 * class_size (fst s) x <= class_size (fst s') (repr (fst s') x))%N.
  Proof. Admitted. (* STUB *)

  (** Repair never reduces the spending unit. *)
  Lemma F9b_rstep_unit : forall s s', state_inv s -> rstep s = inl s' ->
    unit (fst s) <= unit (fst s').
  Proof. Admitted. (* STUB *)

  (** Loop credit includes the binary driver charge. *)
  Lemma k_loop_le : (c_loopN <= k_loop)%N.
  Proof. Admitted. (* STUB *)

  (** Fuel construction uses stored binary counters. *)
  Lemma T7b_fuel : forall db, inv db ->
    (T_rebuild_fuel db <= k_driver * N.of_nat (unit db))%N.
  Proof. Admitted. (* STUB *)

  (** The [T_loopN_amort] driver retains the final database credit. *)
  Lemma T8a_loop_final : forall B U db, inv db -> (ids (rebuild db) <= B)%N ->
    unit (rebuild db) <= U ->
    (T_loopN rstep T_rstep (rebuild_fuel db) (db, []) +
      k_loop * N.of_nat U * rebuild_potential B (rebuild db) <=
      k_loop * N.of_nat U * rebuild_potential B db + k_stop * N.of_nat U +
      c_loopN * N.of_nat (N.size_nat (rebuild_fuel db) + 1))%N.
  Proof. Admitted. (* STUB *)

End DatabaseT.
