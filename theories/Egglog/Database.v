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

(** Set bits pay for the carries performed by successive binary increments. *)
Fixpoint database_positive_credit (p : positive) : N :=
  match p with
  | xH => 1%N
  | xO q => database_positive_credit q
  | xI q => (1 + database_positive_credit q)%N
  end.

Definition database_counter_credit (n : N) : N :=
  match n with N0 => 0%N | Npos p => database_positive_credit p end.

(** A positive increment spends at most two units after releasing its carry credit. *)
Lemma database_positive_succ_amort : forall p,
  (Pos.T_succ p + database_positive_credit (Pos.succ p) <=
    2 + database_positive_credit p)%N.
Proof.
  intro p. induction p as [p IH | p IH |]; time_unfold Pos.T_succ;
    cbn [Pos.succ database_positive_credit]; lia.
Qed.

(** The natural-number wrapper adds one unit to a positive increment's amortized cost. *)
Lemma database_counter_succ_amort : forall n,
  (N.T_succ n + database_counter_credit (N.succ n) <=
    3 + database_counter_credit n)%N.
Proof.
  intros [|p]; time_unfold N.T_succ; cbn [N.succ database_counter_credit].
  - cbn [database_positive_credit]. lia.
  - pose proof (database_positive_succ_amort p). lia.
Qed.

(** Computing a binary size amortizes the carries in its binary result. *)
Lemma database_positive_size_amort : forall p,
  (Pos.T_size p + database_positive_credit (Pos.size p) <=
    4 * N.of_nat (Pos.size_nat p))%N.
Proof.
  intro p. induction p as [p IH | p IH |]; time_unfold Pos.T_size;
    cbn [Pos.size Pos.size_nat].
  - pose proof (database_positive_succ_amort (Pos.size p)). lia.
  - pose proof (database_positive_succ_amort (Pos.size p)). lia.
  - cbn [database_positive_credit]. lia.
Qed.

(** The natural wrapper for size adds a single constant call. *)
Lemma database_N_size_time : forall n,
  (N.T_size n <= 4 * N.of_nat (N.size_nat n) + 1)%N.
Proof.
  intros [| p]; time_unfold N.T_size; cbn [N.size_nat]; [lia |].
  pose proof (database_positive_size_amort p). lia.
Qed.

(** Binary multiplication pays the measured operand widths, retaining the actual clock. *)
Lemma database_N_mul_time : forall n m,
  (N.T_mul n m <= N.of_nat (N.size_nat n) *
    (N.of_nat (N.size_nat n) + 2 * N.of_nat (N.size_nat m) + 2) + 1)%N.
Proof.
  intros [| p] [| q]; time_unfold N.T_mul; cbn [N.size_nat]; try lia.
  pose proof (Pos.T_mul_le p q). lia.
Qed.

(** Unary conversion shares the same carry credit as dense slot numbering. *)
Lemma database_of_succ_nat_amort : forall n,
  (Pos.T_of_succ_nat n + database_positive_credit (Pos.of_succ_nat n) <=
    3 * N.of_nat n + 2)%N.
Proof.
  intro n. induction n as [|n IH]; time_unfold Pos.T_of_succ_nat.
  - reflexivity.
  - pose proof (database_positive_succ_amort (Pos.of_succ_nat n)) as Hcarry.
    cbn [Pos.of_succ_nat]. lia.
Qed.

(** Constructing a binary natural from a unary length has linear total carry cost. *)
Lemma T_database_of_nat_le : forall n,
  (N.T_of_nat n <= 3 * N.of_nat n + 2)%N.
Proof.
  intros [|n]; time_unfold N.T_of_nat; [lia |].
  pose proof (database_of_succ_nat_amort n). lia.
Qed.

(** A run of low one bits witnesses the carry cost of a binary multiplicity. *)
Fixpoint database_carry_value (n : nat) : positive :=
  match n with O => xH | S k => xI (database_carry_value k) end.

(** Incrementing an all-ones positive visits every bit. *)
Lemma database_carry_positive_time : forall n,
  Pos.T_succ (database_carry_value n) = (N.of_nat n + 1)%N.
Proof.
  intro n. induction n as [|n IH]; cbn [database_carry_value]; time_unfold Pos.T_succ.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** The natural-number increment retains the full carry cost. *)
Lemma database_carry_successor_time : forall n,
  N.T_succ (Npos (database_carry_value n)) = (N.of_nat n + 2)%N.
Proof.
  intro n. time_unfold N.T_succ. rewrite database_carry_positive_time. lia.
Qed.

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
  db_runtime : database_runtime C X;
  db_cache_updates : N
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
Arguments db_cache_updates {C X}.

TimeFun db_forest.
TimeFun db_nuses.
TimeFun db_npending.
TimeFun db_wmark.
TimeFun db_written_cells.
TimeFun db_index_counters.
TimeFun db_row_store.
TimeFun db_slot_store.
TimeFun db_runtime.
TimeFun db_cache_updates.

(** Earlier declarations override later declarations, as in [lookup_kind]. *)
Definition database_kinds (ds : list decl) : PTrieCode.t output :=
  fold_right (fun d kinds => PTrieCode.set (name d) (out d) kinds) PTrieCode.empty ds.
TimeFun database_kinds.

Definition database_max_name (ds : list decl) : positive :=
  fold_right (fun d bound => Pos.max (name d) bound) 1%positive ds.
TimeFun database_max_name.

(** Adding an earlier declaration preserves the presence of every already-declared name. *)
Lemma database_declaration_cons_nonempty : forall ds d f,
  lookup_kind ds f <> None -> lookup_kind (d :: ds) f <> None.
Proof.
  intros ds d f Hpresent. cbn [lookup_kind].
  destruct (Pos.eqb (name d) f); [discriminate | exact Hpresent].
Qed.

(** The stored name maximum is either the constant base or an actual declared name. *)
Lemma database_max_name_attained : forall ds,
  database_max_name ds = 1%positive \/ lookup_kind ds (database_max_name ds) <> None.
Proof.
  induction ds as [| d ds IH]; [now left |].
  assert (Htail : database_max_name ds = 1%positive \/
    lookup_kind (d :: ds) (database_max_name ds) <> None).
  { destruct IH as [Hbase | Hpresent]; [now left |].
    right. now apply database_declaration_cons_nonempty. }
  change (Pos.max (name d) (database_max_name ds) = 1%positive \/
    lookup_kind (d :: ds) (Pos.max (name d) (database_max_name ds)) <> None).
  unfold Pos.max. destruct (Pos.compare (name d) (database_max_name ds)); try exact Htail.
  right. cbn [lookup_kind]. rewrite Pos.eqb_refl. discriminate.
Qed.

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

(** A maximum comparison reads no more bits than its current declaration name. *)
Lemma T_database_positive_max_le : forall p q,
  (Pos.T_max p q <= N.of_nat (Pos.size_nat p) + 2)%N.
Proof.
  intros p q. time_step Pos.max.
Qed.

(** The declaration trie pays once for each declaration and each name bit. *)
Lemma T_database_kinds_le : forall ds,
  (T_database_kinds ds <= 8 * (PTrieT.c_trie + 1) *
    N.of_nat (length ds + fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds + 1))%N.
Proof.
  intro ds. induction ds as [|d ds IH].
  - time_step database_kinds; time_step.
  - pose proof (PTrieT.T_set_le output (name d) (out d) (database_kinds ds)) as Hset.
    unfold database_kinds in Hset. unfold T_database_kinds in IH.
    time_unfold T_database_kinds. time_unfold List.T_fold_right.
    revert IH. time_simpl. intro IH. time_cbn_all.
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost. nia.
Qed.

(** The declaration maximum charges the bit length of each name independently. *)
Lemma T_database_max_name_le : forall ds,
  (T_database_max_name ds <=
    8 * N.of_nat (length ds + fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds + 1))%N.
Proof.
  intro ds. induction ds as [|d ds IH].
  - time_step database_max_name; time_step.
  - pose proof (T_database_positive_max_le (name d) (database_max_name ds)) as Hmax.
    unfold database_max_name in Hmax. unfold T_database_max_name in IH.
    time_unfold T_database_max_name. time_unfold List.T_fold_right.
    revert IH. time_simpl. intro IH. time_cbn_all. lia.
Qed.

(** Dense grouping releases the carry credit accumulated by earlier slot numbers. *)
Lemma T_database_slot_groups_amort : forall prepared next groups,
  (T_database_slot_groups next prepared groups +
    database_counter_credit (next + N.of_nat (length prepared)) <=
    8 * (PTrieT.c_trie + 1) *
      N.of_nat (length prepared +
        fold_right (fun s n => (Pos.size_nat (fst s) + n)%nat) 0%nat prepared + 1) +
    database_counter_credit next)%N.
Proof.
  intro prepared. induction prepared as [|[f layout] rest IH]; intros next groups.
  - time_unfold T_database_slot_groups. cbn [length fold_right].
    rewrite !N.add_0_r. cbn [N.of_nat Nat.add]. rewrite N.mul_1_r.
    set (trie_cost := PTrieT.c_trie). clearbody trie_cost. lia.
  - set (previous := match PTrieCode.get f groups with Some slots => slots | None => [] end).
    pose proof (IH (N.succ next) (PTrieCode.set f ((next, layout) :: previous) groups)) as Htail.
    pose proof (PTrieT.T_get_le (list (N * database_slot_layout)) f groups) as Hget.
    pose proof (PTrieT.T_set_le (list (N * database_slot_layout)) f
      ((next, layout) :: previous) groups) as Hset.
    pose proof (database_counter_succ_amort next) as Hcarry.
    assert (Hfinish : (next + N.of_nat (length ((f, layout) :: rest)))%N =
      (N.succ next + N.of_nat (length rest))%N) by (cbn [length]; lia).
    rewrite Hfinish. time_unfold T_database_slot_groups. fold previous.
    cbn [length fold_right fst].
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost.
    time_cbn. nia.
Qed.

(** Numbering from zero has no initial carry debt. *)
Lemma T_database_slot_groups_le : forall prepared groups,
  (T_database_slot_groups 0 prepared groups <= 8 * (PTrieT.c_trie + 1) *
    N.of_nat (length prepared +
      fold_right (fun s n => (Pos.size_nat (fst s) + n)%nat) 0%nat prepared + 1))%N.
Proof.
  intros prepared groups. pose proof (T_database_slot_groups_amort prepared 0 groups).
  cbn [database_counter_credit] in H. lia.
Qed.

(** The largest declaration name fits within the sum of all name widths and the root bit. *)
Lemma database_max_name_bits : forall ds,
  Pos.size_nat (database_max_name ds) <=
    fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds + 1.
Proof.
  intro ds. induction ds as [|d ds IH]; [reflexivity |].
  change (Pos.size_nat (Pos.max (name d) (database_max_name ds)) <=
    Pos.size_nat (name d) + fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds + 1).
  unfold Pos.max. destruct (Pos.compare (name d) (database_max_name ds)); lia.
Qed.

(** A binary natural's bit width never exceeds its unary value. *)
Lemma database_counter_bits_value : forall n, N.size_nat n <= N.to_nat n.
Proof.
  intros [|p]; [reflexivity | apply slot_rank_bits_value].
Qed.

(** Binary maximum pays only the bit width of its first argument. *)
Lemma T_database_counter_max_le : forall n m,
  (N.T_max n m <= N.of_nat (N.size_nat n) + 3)%N.
Proof.
  intros n m. time_step N.max.
Qed.

(** Preparing layouts preserves both the slot count and the charged function-name bits. *)
Lemma database_prepared_sizes : forall sl,
  length (prepare_slot_layouts sl) = length sl /\
  fold_right (fun s n => Pos.size_nat (fst s) + n) 0 (prepare_slot_layouts sl) =
    fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl.
Proof.
  intro sl. split.
  - unfold prepare_slot_layouts. apply length_map.
  - unfold prepare_slot_layouts.
    induction sl as [|[f perm] sl IH]; cbn [map fold_right fst];
      [reflexivity | now rewrite IH].
Qed.

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

(** Adding one prepared entry increases exactly its function's group length. *)
Lemma database_group_add_length : forall groups f g s layout,
  length (database_group_entries f
    (PTrieCode.set g ((s, layout) :: database_group_entries g groups) groups)) =
  if Pos.eqb g f then S (length (database_group_entries f groups))
  else length (database_group_entries f groups).
Proof.
  intros groups f g s layout. destruct (Pos.eq_dec f g) as [-> | Hdifferent].
  - rewrite Pos.eqb_refl. unfold database_group_entries at 1.
    now rewrite PTrie.get_set_same.
  - assert (Htest : Pos.eqb g f = false) by (apply Pos.eqb_neq; congruence).
    rewrite Htest. unfold database_group_entries at 1.
    now rewrite PTrie.get_set_other by exact Hdifferent.
Qed.

(** A grouping pass adds one entry for each matching function in its input. *)
Lemma database_slot_groups_length : forall prepared next groups f,
  length (database_group_entries f (database_slot_groups next prepared groups)) =
  length (database_group_entries f groups) +
    length (filter (fun item => Pos.eqb (fst item) f) prepared).
Proof.
  intro prepared. induction prepared as [|[g layout] rest IH]; intros next groups f.
  - cbn [database_slot_groups filter length]. lia.
  - cbn [database_slot_groups filter fst]. fold (database_group_entries g groups).
    rewrite IH, database_group_add_length. destruct (Pos.eqb g f); cbn [length]; lia.
Qed.

(** Preparing layouts preserves the exact number of slots belonging to each function. *)
Lemma database_prepared_group_length : forall sl f,
  length (database_group_entries f
    (database_slot_groups 0 (prepare_slot_layouts sl) PTrieCode.empty)) =
  length (filter (fun item => Pos.eqb (fst item) f) sl).
Proof.
  intros sl f. rewrite database_slot_groups_length.
  unfold database_group_entries at 1. rewrite PTrie.get_empty. cbn [length Nat.add].
  unfold prepare_slot_layouts.
  induction sl as [|[g perm] rest IH]; [reflexivity |].
  cbn [map filter fst].
  destruct (Pos.eqb g f); cbn [length]; now rewrite IH.
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
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) state
    (db_cache_updates db).
TimeFun database_set_runtime.

Definition database_set_forest {C X} (forest : UnionFindCode.t)
    (db : database_state C X) : database_state C X :=
  DatabaseState forest (db_nuses db) (db_npending db) (db_wmark db)
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) (db_runtime db)
    (db_cache_updates db).
TimeFun database_set_forest.

Definition database_set_pending {C X} (pending : N)
    (db : database_state C X) : database_state C X :=
  DatabaseState (db_forest db) (db_nuses db) pending (db_wmark db)
    (db_written_cells db) (db_index_counters db) (db_row_store db) (db_slot_store db) (db_runtime db)
    (db_cache_updates db).
TimeFun database_set_pending.

(** Each cache call records its actual update counter, input rank, index counters and cells. *)
Definition database_record_cache {C X} (u : list C) (counters : list positive)
    (db : database_state C X) : database_state C X :=
  let next := N.succ_pos (db_cache_updates db) in
  let rank := Pos.of_succ_nat (length u) in
  DatabaseState (db_forest db) (db_nuses db) (db_npending db) (db_wmark db)
    (u ++ db_written_cells db)
    (next :: rank :: (counters ++ db_index_counters db))
    (db_row_store db) (db_slot_store db) (db_runtime db) (Npos next).
TimeFun database_record_cache.

(** Recording a cache call traverses only its new input and newly collected counters. *)
Lemma T_database_record_cache_le : forall C X (u : list C) counters (db : database_state C X),
  (T_database_record_cache u counters db <=
    32 + N.T_succ_pos (db_cache_updates db) +
      6 * N.of_nat (length u + 1) + N.of_nat (length counters + 1))%N.
Proof.
  intros C X u counters db.
  pose proof (database_of_succ_nat_amort (length u)) as Hrank.
  pose proof (Datatypes.T_length_le u) as Hlength.
  pose proof (Datatypes.T_app_le counters (db_index_counters db)) as Hcounters.
  pose proof (Datatypes.T_app_le u (db_written_cells db)) as Hcells.
  time_unfold @T_database_record_cache. time_simpl. time_cbn. lia.
Qed.

(** A ghost operation records whether a tuple was inserted or removed from an index. *)
Definition database_index_step {C X : Type} (insert remove : list C -> X -> X)
    (ix : X) (operation : bool * list C) : X :=
  if fst operation then insert (snd operation) ix else remove (snd operation) ix.

(** Cached indexes have finite construction histories over the recorded written cells. *)
Definition database_index_history {C X : Type} (empty : X)
    (insert remove : list C -> X -> X) (written : list C) (ix : X) : Prop :=
  exists operations : list (bool * list C),
    ix = fold_left (database_index_step insert remove) operations empty /\
    Forall (fun operation => fst operation = true -> incl (snd operation) written) operations.

(** The empty index has an empty construction history. *)
Lemma database_index_history_empty : forall C X (empty : X) insert remove (written : list C),
  database_index_history empty insert remove written empty.
Proof.
  intros C X empty insert remove written. exists []. split; [reflexivity | constructor].
Qed.

(** Recording more written cells retains every existing construction witness. *)
Lemma database_index_history_weaken : forall C X (empty : X) insert remove
  (before after : list C) ix,
  incl before after -> database_index_history empty insert remove before ix ->
  database_index_history empty insert remove after ix.
Proof.
  intros C X empty insert remove before after ix Hwritten [operations [Hix Hhistory]].
  exists operations. split; [exact Hix |].
  rewrite Forall_forall in Hhistory |- *. intros operation Hin Hinsert c Hcell.
  apply Hwritten. exact (Hhistory operation Hin Hinsert c Hcell).
Qed.

(** An insertion extends the ghost history when its tuple cells have been recorded. *)
Lemma database_index_history_insert : forall C X (empty : X) insert remove
  (written u : list C) ix,
  database_index_history empty insert remove written ix -> incl u written ->
  database_index_history empty insert remove written (insert u ix).
Proof.
  intros C X empty insert remove written u ix [operations [Hix Hhistory]] Hcells.
  exists (operations ++ [(true, u)]). split.
  - rewrite fold_left_app. cbn [fold_left database_index_step fst snd]. now rewrite Hix.
  - apply Forall_app. split; [exact Hhistory |]. constructor; [exact (fun _ => Hcells) | constructor].
Qed.

(** A removal extends the history without adding any written-cell requirement. *)
Lemma database_index_history_remove : forall C X (empty : X) insert remove
  (written u : list C) ix,
  database_index_history empty insert remove written ix ->
  database_index_history empty insert remove written (remove u ix).
Proof.
  intros C X empty insert remove written u ix [operations [Hix Hhistory]].
  exists (operations ++ [(false, u)]). split.
  - rewrite fold_left_app. cbn [fold_left database_index_step fst snd]. now rewrite Hix.
  - apply Forall_app. split; [exact Hhistory |]. constructor; [discriminate | constructor].
Qed.

(** Properties preserved by recorded insertions and removals hold for every ghost history. *)
Lemma database_index_history_induction : forall C X (empty : X) insert remove
  (written : list C) (P : X -> Prop),
  P empty ->
  (forall u ix, incl u written -> P ix -> P (insert u ix)) ->
  (forall u ix, P ix -> P (remove u ix)) ->
  forall ix, database_index_history empty insert remove written ix -> P ix.
Proof.
  intros C X empty insert remove written P Hempty Hinsert Hremove ix
    [operations [-> Hhistory]].
  assert (Hfold : forall operations current,
    Forall (fun operation => fst operation = true -> incl (snd operation) written) operations ->
    P current -> P (fold_left (database_index_step insert remove) operations current)).
  { intro history. induction history as [|[add u] rest IH]; intros current Hentries Hcurrent.
    - exact Hcurrent.
    - inversion Hentries as [|entry tail Hhead Htail]; subst entry tail.
      cbn [fold_left database_index_step fst snd]. apply IH; [exact Htail |].
      destruct add.
      + apply Hinsert; [exact (Hhead eq_refl) | exact Hcurrent].
      + apply Hremove. exact Hcurrent. }
  now apply Hfold.
Qed.

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
    | Id i =>
      match N.compare (runtime_allocated (db_runtime db)) (Npos i) with
      | Lt => Id i
      | _ => Id (fst (UnionFindCode.find i (db_forest db)))
      end
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

  (** A second group pass records the counters of the indexes produced by this cache call. *)
  Fixpoint slot_updated_counters (layouts : list (N * database_slot_layout))
      (state : database_runtime (cell V.t) I.t) : list positive :=
    match layouts with
    | [] => []
    | (s, _) :: rest =>
      let code := N.succ_pos s in
      I.next (slot_index_get code (runtime_all_indexes state)) ::
      I.next (slot_index_get code (runtime_new_indexes state)) ::
      slot_updated_counters rest state
    end.

  Definition slots_update (add : bool) (f : positive) (u : list (cell V.t)) (db : t)
      : t :=
    let layouts := match PTrieCode.get f (runtime_function_slots (db_runtime db)) with
      | None => [] | Some layouts => layouts end in
    let state := slot_update_many add u layouts (db_runtime db) in
    database_record_cache u (slot_updated_counters layouts state)
      (database_set_runtime state db).

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

  (** The row table is erased after its slot contributions have been removed. *)
  Definition row_erase (f : positive) (k : list (cell V.t)) (db : t) : t :=
    database_set_runtime
      (runtime_set_rows
        (PTrieCode.remove (db_row_code f k) (runtime_rows (db_runtime db))) (db_runtime db)) db.

  (** An absent row is unchanged; a present row releases each projected occurrence. *)
  Definition row_delete (f : positive) (k : list (cell V.t)) (db : t) : t :=
    match row_get f k db with
    | None => db
    | Some o => row_erase f k (slots_update false f (k ++ option_list o) db)
    end.
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
        (database_slot_groups 0 prepared PTrieCode.empty) (database_max_name ds) bound) 0%N.
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

  (** Repair one current row, discarding its old projections before inserting its normal form. *)
  Definition repair_current (f : positive) (k : list (cell V.t)) (db : t) : t :=
    match row_get f k db with
    | None => db
    | Some o =>
      let ck := normal_key db k in
      let co := option_map (normal_cell db) o in
      if andb (Pos.eqb (db_tuple_code ck) (db_tuple_code k)) (output_eqb co o)
      then db else put f ck co (row_delete f k db)
    end.
  (** Enumerate current rows that contain an occurrence of a queued loser. *)
  Definition db_get_uses (i : positive) (db : t) : list (positive * list (cell V.t)) :=
    fold_right (fun entry work =>
      let stored := snd entry in
      if existsb (fun c => match c with
          | Id j => Pos.eqb i j
          | Val _ => false
          end) (snd (fst stored) ++ option_list (snd stored))
      then fst stored :: work else work) []
      (PTrieCode.elements (runtime_rows (db_runtime db))).

  (** Popping the scheduling queue leaves the represented database view unchanged. *)
  Definition db_pop_loser (db : t) : option (positive * t) :=
    match runtime_queue (db_runtime db) with
    | [] => None
    | i :: rest => Some (i,
        database_set_pending (N.pred (db_npending db))
          (database_set_runtime
            (runtime_set_union (runtime_changed (db_runtime db))
              (runtime_equalities (db_runtime db)) rest (db_runtime db)) db))
    end.

  (** Repair active rows before taking the next pending equality. *)
  Definition db_rstep (s : t * list (positive * list (cell V.t)))
      : (t * list (positive * list (cell V.t))) + t :=
    match snd s with
    | (f, k) :: rest => inl (repair_current f k (fst s), rest)
    | [] =>
      match db_pop_loser (fst s) with
      | None => inr (fst s)
      | Some (i, db) => inl (db, db_get_uses i (fst s))
      end
    end.
  Definition db_rebuild_fuel (db : t) : N :=
    ((N.size (runtime_allocated (db_runtime db)) + 2) * (db_nuses db + 1) + db_npending db + 1)%N.
  Definition rebuild (db : t) :=
    match loopN db_rstep (db_rebuild_fuel db) (db, []) with
    | inl s => fst s
    | inr result => result
    end.
  Definition index (s : N) (new : bool) (db : t) : I.t :=
    match N.compare s (runtime_slot_bound (db_runtime db)) with
    | Lt =>
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

  (** A slot's proof observation consists of its count table and two index cache entries. *)
  Definition slot_snapshot (state : database_runtime (cell V.t) I.t) (s : N) :=
    (PTrieCode.get (N.succ_pos s) (runtime_projection_counts state),
     PTrieCode.get (N.succ_pos s) (runtime_all_indexes state),
     PTrieCode.get (N.succ_pos s) (runtime_new_indexes state)).

  (** A runtime count observation uses the same lookup as the public database count. *)
  Definition runtime_projection_count (state : database_runtime (cell V.t) I.t)
      (s : N) (u : list (cell V.t)) : N :=
    match PTrieCode.get (db_tuple_code u)
      (projection_table_get (N.succ_pos s) (runtime_projection_counts state)) with
    | Some (_, n) => n
    | None => 0%N
    end.

  (** A runtime index observation selects one of the two stored per-slot caches. *)
  Definition runtime_slot_index (state : database_runtime (cell V.t) I.t)
      (s : N) (new : bool) : I.t :=
    slot_index_get (N.succ_pos s)
      (if new then runtime_new_indexes state else runtime_all_indexes state).

  (** Metadata records cache activity and index construction independently of the row map. *)
  Definition metadata_ok (db : t) : Prop :=
    In 1%positive (db_index_counters db) /\
    In (N.succ_pos (N.of_nat (length (slots db)))) (db_index_counters db) /\
    (forall p, db_cache_updates db = Npos p -> In p (db_index_counters db)) /\
    (forall s new, In (I.next (runtime_slot_index (db_runtime db) s new))
      (db_index_counters db)) /\
    (forall s new, database_index_history I.empty I.insert I.remove (db_written_cells db)
      (runtime_slot_index (db_runtime db) s new)) /\
    (forall s u, (runtime_projection_count (db_runtime db) s u <= db_cache_updates db)%N) /\
    (runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty) /\
    runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db)).

  (** These observations determine metadata validity and omit the row store and forest. *)
  Definition metadata_snapshot (db : t) :=
    (db_cache_updates db, db_written_cells db, db_index_counters db,
     runtime_slots (db_runtime db), runtime_slot_bound (db_runtime db),
     runtime_function_slots (db_runtime db), runtime_all_indexes (db_runtime db),
     runtime_new_indexes (db_runtime db), runtime_projection_counts (db_runtime db)).

  (** Equal metadata observations transfer all construction and counter witnesses. *)
  Lemma metadata_snapshot_ok : forall db db',
    metadata_snapshot db = metadata_snapshot db' -> metadata_ok db -> metadata_ok db'.
  Proof.
    intros db db' Hsame Hmetadata. unfold metadata_snapshot in Hsame.
    injection Hsame as Hupdates Hwritten Hcounters Hslots Hbound Hgroups Hall Hnew Hcounts.
    unfold metadata_ok, slots, runtime_slot_index, runtime_projection_count in *.
    now rewrite <- Hupdates, <- Hwritten, <- Hcounters, <- Hslots, <- Hbound,
      <- Hgroups, <- Hall, <- Hnew, <- Hcounts.
  Qed.

  (** Each touched slot contributes both final index counters to the recorded list. *)
  Lemma slot_updated_counters_member : forall layouts state s layout,
    In (s, layout) layouts -> forall new,
    In (I.next (runtime_slot_index state s new)) (slot_updated_counters layouts state).
  Proof.
    intro layouts. induction layouts as [|[t block] rest IH]; intros state s layout Hin new.
    - contradiction.
    - destruct Hin as [Hequal | Hin].
      + injection Hequal as -> ->. cbn [slot_updated_counters runtime_slot_index].
        destruct new; [right; now left | now left].
      + cbn [slot_updated_counters]. right. right. now apply (IH state s layout).
  Qed.

  (** Initial caches have empty histories, zero counts and their root counter recorded. *)
  Lemma metadata_init : forall ds sl, metadata_ok (init ds sl).
  Proof.
    intros ds sl.
    assert (Hempty : forall s new,
      runtime_slot_index (db_runtime (init ds sl)) s new = I.empty).
    { intros s new. unfold runtime_slot_index, slot_index_get.
      cbn [init db_runtime runtime_new_indexes runtime_all_indexes].
      destruct new; now rewrite PTrie.get_empty. }
    unfold metadata_ok. split.
    - destruct sl; now left.
    - split.
      + destruct sl; [now left | right; now left].
      + split.
        * intros p Hzero. discriminate Hzero.
        * split.
          -- intros s new. rewrite Hempty, I.next_empty. destruct sl; now left.
          -- split.
             ++ intros s new. rewrite Hempty. apply database_index_history_empty.
             ++ split.
                ** intros s u. unfold runtime_projection_count, projection_table_get.
                   cbn [init db_runtime runtime_projection_counts db_cache_updates].
                   rewrite PTrie.get_empty. cbn. rewrite PTrie.get_empty. reflexivity.
                ** split; reflexivity.
  Qed.

  (** Changing only the forest preserves all cache metadata. *)
  Lemma metadata_set_forest : forall db forest, metadata_ok db ->
    metadata_ok (database_set_forest forest db).
  Proof.
    intros db forest. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** Changing only the pending counter preserves all cache metadata. *)
  Lemma metadata_set_pending : forall db count, metadata_ok db ->
    metadata_ok (database_set_pending count db).
  Proof.
    intros db count. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** Writing the row table leaves the independently maintained cache metadata intact. *)
  Lemma metadata_row_write : forall db f k o, metadata_ok db ->
    metadata_ok (row_write f k o db).
  Proof.
    intros db f k o. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** Erasing the row table also preserves the cache metadata observations. *)
  Lemma metadata_row_erase : forall db f k, metadata_ok db ->
    metadata_ok (row_erase f k db).
  Proof.
    intros db f k. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** Allocating an identifier does not alter the cache histories or counters. *)
  Lemma metadata_allocate_id : forall db i, metadata_ok db ->
    metadata_ok (allocate_id i db).
  Proof.
    intros db i. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** Forest compression changes none of the cache metadata observations. *)
  Lemma metadata_find : forall db i, metadata_ok db -> metadata_ok (snd (find i db)).
  Proof.
    intros db i. apply metadata_snapshot_ok. reflexivity.
  Qed.

  (** A union changes its forest and queue while retaining all cache metadata. *)
  Lemma metadata_union : forall db i j, metadata_ok db -> metadata_ok (union i j db).
  Proof.
    intros db i j Hmetadata. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [[pair |] forest].
    - destruct pair as [winner loser].
      eapply metadata_snapshot_ok; [reflexivity | exact Hmetadata].
    - eapply metadata_snapshot_ok; [reflexivity | exact Hmetadata].
  Qed.

  (** Advancing starts an empty delta history and retains every other metadata fact. *)
  Lemma metadata_advance : forall db, metadata_ok db -> metadata_ok (advance db).
  Proof.
    intros db (Hone & Hslots & Hcounter & Hnext & Hhistory & Hcount & Hgroups & Hbound).
    unfold metadata_ok.
    split; [exact Hone |]. split; [exact Hslots |]. split; [exact Hcounter |].
    split.
    - intros s new. destruct new; [| exact (Hnext s false)].
      unfold runtime_slot_index, slot_index_get.
      cbn [advance database_set_runtime runtime_set_changed runtime_set_indexes
        db_runtime runtime_new_indexes db_index_counters].
      rewrite PTrie.get_empty, I.next_empty. exact Hone.
    - split.
      + intros s new. destruct new; [| exact (Hhistory s false)].
        unfold runtime_slot_index, slot_index_get.
        cbn [advance database_set_runtime runtime_set_changed runtime_set_indexes
          db_runtime runtime_new_indexes db_written_cells].
        rewrite PTrie.get_empty. apply database_index_history_empty.
      + split; [exact Hcount |]. split; assumption.
  Qed.

  (** Every stored row cell occurs in the concrete write history. *)
  Definition recorded_rows (db : t) : Prop :=
    forall f k o c, row (view db) f k o -> In c (k ++ option_list o) ->
      In c (db_written_cells db).

  (** The history invariant combines cache construction with coverage of current rows. *)
  Definition database_history (db : t) : Prop := metadata_ok db /\ recorded_rows db.

  (** Retaining rows and extending their history preserves cell coverage. *)
  Lemma recorded_rows_transport : forall db db',
    (forall f k o, row (view db') f k o -> row (view db) f k o) ->
    incl (db_written_cells db) (db_written_cells db') ->
    recorded_rows db -> recorded_rows db'.
  Proof.
    intros db db' Hrows Hwritten Hrecorded f k o c Hrow Hin.
    apply Hwritten. exact (Hrecorded f k o c (Hrows f k o Hrow) Hin).
  Qed.

  (** Allocation changes neither the row cells nor the cache histories. *)
  Lemma database_history_allocate_id : forall db i, database_history db ->
    database_history (allocate_id i db).
  Proof.
    intros db i [Hmetadata Hrows]. split.
    - now apply metadata_allocate_id.
    - exact Hrows.
  Qed.

  (** Union preserves row cells and every independently maintained cache history. *)
  Lemma database_history_union : forall db i j, database_history db ->
    database_history (union i j db).
  Proof.
    intros db i j [Hmetadata Hrows]. split.
    - now apply metadata_union.
    - unfold union.
      destruct (UnionFindCode.union i j (db_forest db)) as [[pair |] forest].
      + destruct pair as [winner loser]. exact Hrows.
      + exact Hrows.
  Qed.

  (** Advancing clears delta membership while retaining all stored-cell coverage. *)
  Lemma database_history_advance : forall db, database_history db ->
    database_history (advance db).
  Proof.
    intros db [Hmetadata Hrows]. split; [now apply metadata_advance | exact Hrows].
  Qed.

  (** Both guarded index branches retain a recorded counter and a construction history. *)
  Lemma metadata_public_index : forall db s new, metadata_ok db ->
    In (I.next (index s new db)) (db_index_counters db) /\
    database_index_history I.empty I.insert I.remove (db_written_cells db) (index s new db).
  Proof.
    intros db s new (Hone & _ & _ & Hnext & Hhistory & _).
    unfold index. destruct (N.compare s (runtime_slot_bound (db_runtime db))).
    - rewrite I.next_empty. split; [exact Hone | apply database_index_history_empty].
    - change (In (I.next (runtime_slot_index (db_runtime db) s new)) (db_index_counters db) /\
        database_index_history I.empty I.insert I.remove (db_written_cells db)
          (runtime_slot_index (db_runtime db) s new)). split; [apply Hnext | apply Hhistory].
    - rewrite I.next_empty. split; [exact Hone | apply database_index_history_empty].
  Qed.

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
    projection_counts_ok db /\
    (runtime_max_name (db_runtime db) = 1%positive \/
      kind (view db) (runtime_max_name (db_runtime db)) <> None) /\
    database_history db.

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

  (** The comparison guard uses an attained declaration maximum or the constant base. *)
  Lemma wf_max_name_attained : forall db, database_wf db ->
    runtime_max_name (db_runtime db) = 1%positive \/
      kind (view db) (runtime_max_name (db_runtime db)) <> None.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** The stored invariant includes maintained cache histories and current-row coverage. *)
  Lemma wf_history : forall db, database_wf db -> database_history db.
  Proof.
    unfold database_wf. tauto.
  Qed.

  (** Well-formed databases have genuine cache construction and recorded counter bounds. *)
  Lemma wf_metadata : forall db, database_wf db -> metadata_ok db.
  Proof.
    intros db Hwf. exact (proj1 (wf_history db Hwf)).
  Qed.

  (** Every cell of a stored row is present in the write history. *)
  Lemma wf_recorded_rows : forall db, database_wf db -> recorded_rows db.
  Proof.
    intros db Hwf. exact (proj2 (wf_history db Hwf)).
  Qed.
  Definition wf : t -> Prop := database_wf.

  (** An in-range slot reads exactly its stored full or delta cache. *)
  Lemma index_runtime_slot : forall db s new,
    (s < runtime_slot_bound (db_runtime db))%N ->
    index s new db = runtime_slot_index (db_runtime db) s new.
  Proof.
    intros db s new Hinside. unfold index.
    apply N.compare_lt_iff in Hinside. rewrite Hinside.
    unfold runtime_slot_index, slot_index_get. destruct new; reflexivity.
  Qed.

  (** Out-of-range queries return the empty index without reading a slot trie. *)
  Lemma index_outside_bound : forall db s new,
    (runtime_slot_bound (db_runtime db) <= s)%N -> index s new db = I.empty.
  Proof.
    intros db s new Houtside. unfold index.
    destruct (N.compare s (runtime_slot_bound (db_runtime db))) eqn:Hcompare;
      try reflexivity.
    apply N.compare_lt_iff in Hcompare. exfalso. apply (N.lt_irrefl s).
    eapply N.lt_le_trans; eassumption.
  Qed.

  (** A declared slot number is below the stored bound in every well-formed database. *)
  Lemma slot_of_inside_bound : forall db s f perm, wf db ->
    slot_of db s = Some (f, perm) -> (s < runtime_slot_bound (db_runtime db))%N.
  Proof.
    intros db s f perm Hwf Hslot. rewrite (wf_slot_bound db Hwf).
    assert (Hinside : N.to_nat s < length (slots db)).
    { apply nth_error_Some. unfold slot_of in Hslot. congruence. }
    lia.
  Qed.

  (** Missing slot declarations are exactly the queries outside the allocated slot interval. *)
  Lemma slot_of_outside_bound : forall db s, wf db -> slot_of db s = None ->
    (runtime_slot_bound (db_runtime db) <= s)%N.
  Proof.
    intros db s Hwf Hslot. rewrite (wf_slot_bound db Hwf).
    unfold slot_of in Hslot. apply nth_error_None in Hslot. lia.
  Qed.

  (** Executable cell normalization returns the public representative-based cell. *)
  Lemma normal_cell_correct : forall db c, wf db -> normal_cell db c = canon db c.
  Proof.
    intros db [i | v] Hwf; cbn [normal_cell canon repr].
    - destruct (N.compare (runtime_allocated (db_runtime db)) (Npos i)) eqn:Hallocated.
      + f_equal. apply UnionFind.find_repr. exact (wf_forest db Hwf).
      + f_equal. symmetry. apply UnionFindCodeFacts.repr_absent.
        intro Hmember. apply (proj1 (wf_forest_members db Hwf i)) in Hmember.
        apply N.compare_lt_iff in Hallocated.
        change (Npos i <= runtime_allocated (db_runtime db))%N in Hmember.
        apply (N.lt_irrefl (Npos i)). eapply N.le_lt_trans; eassumption.
      + f_equal. apply UnionFind.find_repr. exact (wf_forest db Hwf).
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

  (** Distinct binary slot numbers have distinct positive trie keys. *)
  Lemma slot_code_injective : forall s t, N.succ_pos s = N.succ_pos t -> s = t.
  Proof.
    intros s t Hequal. apply (f_equal Npos) in Hequal.
    assert (Hs : Npos (N.succ_pos s) = N.succ s) by (destruct s; reflexivity).
    assert (Ht : Npos (N.succ_pos t) = N.succ t) by (destruct t; reflexivity).
    rewrite Hs, Ht in Hequal. lia.
  Qed.

  (** Updating one slot leaves every other slot's cached entries unchanged. *)
  Lemma slot_update_one_snapshot_other : forall b s u state t, t <> s ->
    slot_snapshot (slot_update_one b s u state) t = slot_snapshot state t.
  Proof.
    intros b s u state t Hdifferent.
    assert (Hcode : N.succ_pos t <> N.succ_pos s).
    { intro Hequal. apply Hdifferent. now apply slot_code_injective. }
    unfold slot_update_one. destruct b.
    - unfold slot_snapshot.
      cbn [runtime_set_indexes runtime_projection_counts runtime_all_indexes runtime_new_indexes].
      now rewrite !PTrie.get_set_other by exact Hcode.
    - destruct (PTrieCode.get (db_tuple_code u)
        (projection_table_get (N.succ_pos s) (runtime_projection_counts state)))
        as [[tuple n] |]; [| reflexivity].
      destruct n as [| p]; [reflexivity |]. destruct p; unfold slot_snapshot;
        cbn [runtime_set_indexes runtime_projection_counts runtime_all_indexes runtime_new_indexes];
        now rewrite !PTrie.get_set_other by exact Hcode.
  Qed.

  (** A slot update depends only on that slot's three cached entries. *)
  Lemma slot_update_one_snapshot_local : forall b s u first second,
    slot_snapshot first s = slot_snapshot second s ->
    slot_snapshot (slot_update_one b s u first) s =
      slot_snapshot (slot_update_one b s u second) s.
  Proof.
    intros b s u first second Hkeep.
    pose proof Hkeep as Hentries. unfold slot_snapshot in Hentries.
    injection Hentries as Hcounts Hall Hnew. destruct b.
    - unfold slot_update_one, slot_snapshot.
      cbn [runtime_set_indexes runtime_projection_counts runtime_all_indexes runtime_new_indexes].
      rewrite !PTrie.get_set_same. unfold projection_table_get, slot_index_get.
      now rewrite Hcounts, Hall, Hnew.
    - unfold slot_update_one, projection_table_get, slot_index_get.
      rewrite Hcounts, Hall, Hnew.
      fold (projection_table_get (N.succ_pos s) (runtime_projection_counts second)).
      destruct (PTrieCode.get (db_tuple_code u)
        (projection_table_get (N.succ_pos s) (runtime_projection_counts second)))
        as [[tuple n] |]; [| exact Hkeep].
      destruct n as [| p]; [exact Hkeep |]. destruct p; unfold slot_snapshot;
        cbn [runtime_set_indexes runtime_projection_counts runtime_all_indexes runtime_new_indexes];
        rewrite !PTrie.get_set_same; now rewrite ?Hcounts, ?Hall, ?Hnew.
  Qed.

  (** A function update leaves any slot absent from its prepared list unchanged. *)
  Lemma slot_update_many_snapshot_other : forall b u layouts state s,
    ~ In s (map fst layouts) ->
    slot_snapshot (slot_update_many b u layouts state) s = slot_snapshot state s.
  Proof.
    intros b u layouts. induction layouts as [| [t layout] rest IH];
      intros state s Hmissing; cbn [slot_update_many]; [reflexivity |].
    cbn [map fst] in Hmissing.
    rewrite IH by (intro Hin; apply Hmissing; now right).
    apply slot_update_one_snapshot_other. intro Hequal. subst s. apply Hmissing. now left.
  Qed.

  (** A duplicate-free prepared list updates each listed slot exactly once. *)
  Lemma slot_update_many_snapshot_member : forall b u layouts,
    NoDup (map fst layouts) -> forall state s layout, In (s, layout) layouts ->
    slot_snapshot (slot_update_many b u layouts state) s =
      slot_snapshot (slot_update_one b s (project_slot_layout layout u) state) s.
  Proof.
    intros b u layouts. induction layouts as [| [t first] rest IH];
      intros Hnodup state s layout Hmember; [contradiction |].
    cbn [map fst] in Hnodup. inversion Hnodup as [| key keys Hnot Htail]; subst.
    destruct Hmember as [Hequal | Hmember].
    - injection Hequal as -> ->. cbn [slot_update_many].
      now rewrite slot_update_many_snapshot_other by exact Hnot.
    - cbn [slot_update_many]. rewrite (IH Htail _ _ _ Hmember).
      apply slot_update_one_snapshot_local. apply slot_update_one_snapshot_other.
      intro Hequal. subst t. apply Hnot. exact (in_map fst rest (s, layout) Hmember).
  Qed.

  (** Equal cached slot entries yield equal tuple-count observations. *)
  Lemma slot_snapshot_count : forall first second s,
    slot_snapshot first s = slot_snapshot second s ->
    forall u, runtime_projection_count first s u = runtime_projection_count second s u.
  Proof.
    intros first second s Hequal u. unfold slot_snapshot in Hequal.
    injection Hequal as Hcounts Hall Hnew.
    unfold runtime_projection_count, projection_table_get. now rewrite Hcounts.
  Qed.

  (** Equal cached slot entries yield the same selected index. *)
  Lemma slot_snapshot_index : forall first second s,
    slot_snapshot first s = slot_snapshot second s ->
    forall new, runtime_slot_index first s new = runtime_slot_index second s new.
  Proof.
    intros first second s Hequal new. unfold slot_snapshot in Hequal.
    injection Hequal as Hcounts Hall Hnew.
    unfold runtime_slot_index, slot_index_get. destruct new; [now rewrite Hnew | now rewrite Hall].
  Qed.

  (** Adding or removing one contribution increments or decrements its exact tuple count. *)
  Lemma slot_update_one_count_same : forall b s u state,
    runtime_projection_count (slot_update_one b s u state) s u =
      if b then N.succ (runtime_projection_count state s u)
      else N.pred (runtime_projection_count state s u).
  Proof.
    intros b s u state. unfold slot_update_one.
    fold (runtime_projection_count state s u).
    remember (runtime_projection_count state s u) as n eqn:Hcount. destruct b.
    - unfold runtime_projection_count, projection_table_get.
      cbn [runtime_set_indexes runtime_projection_counts projection_table_get].
      now rewrite !PTrie.get_set_same.
    - destruct n as [| p]; [exact (eq_sym Hcount) |].
      destruct p; unfold runtime_projection_count, projection_table_get;
        cbn [runtime_set_indexes runtime_projection_counts projection_table_get];
        rewrite !PTrie.get_set_same; rewrite ?PTrie.get_remove_same; reflexivity.
  Qed.

  (** A contribution update leaves every different tuple's count unchanged. *)
  Lemma slot_update_one_count_other : forall b s u state v, v <> u ->
    runtime_projection_count (slot_update_one b s u state) s v =
      runtime_projection_count state s v.
  Proof.
    intros b s u state v Hdifferent.
    assert (Hcode : db_tuple_code v <> db_tuple_code u).
    { intro Hequal. apply Hdifferent. exact (Tuples.encode_inj v u Hequal). }
    unfold slot_update_one. fold (runtime_projection_count state s u). destruct b.
    - unfold runtime_projection_count, projection_table_get.
      cbn [runtime_set_indexes runtime_projection_counts projection_table_get].
      rewrite PTrie.get_set_same, PTrie.get_set_other by exact Hcode. reflexivity.
    - destruct (runtime_projection_count state s u) as [| p]; [reflexivity |].
      destruct p; unfold runtime_projection_count, projection_table_get;
        cbn [runtime_set_indexes runtime_projection_counts projection_table_get];
        rewrite PTrie.get_set_same;
        rewrite ?PTrie.get_set_other, ?PTrie.get_remove_other by exact Hcode; reflexivity.
  Qed.

  (** Removal touches the index only when the deleted contribution was the last one. *)
  Lemma slot_update_one_index : forall b s u state new,
    runtime_slot_index (slot_update_one b s u state) s new =
      if b then I.insert u (runtime_slot_index state s new)
      else match runtime_projection_count state s u with
        | Npos xH => I.remove u (runtime_slot_index state s new)
        | _ => runtime_slot_index state s new
        end.
  Proof.
    intros b s u state new. unfold slot_update_one.
    fold (runtime_projection_count state s u). destruct b.
    - unfold runtime_slot_index. destruct new;
        cbn [runtime_set_indexes runtime_all_indexes runtime_new_indexes];
        unfold slot_index_get; now rewrite PTrie.get_set_same.
    - destruct (runtime_projection_count state s u) as [| p]; [reflexivity |].
      destruct p; try reflexivity. unfold runtime_slot_index. destruct new;
        cbn [runtime_set_indexes runtime_all_indexes runtime_new_indexes];
        unfold slot_index_get; now rewrite PTrie.get_set_same.
  Qed.

  (** One contribution changes each count by at most one, including missing removals. *)
  Lemma slot_update_one_count_le : forall b s u state v,
    (runtime_projection_count (slot_update_one b s u state) s v <=
      N.succ (runtime_projection_count state s v))%N.
  Proof.
    intros b s u state v.
    destruct (Pos.eq_dec (db_tuple_code v) (db_tuple_code u)) as [Hequal | Hdifferent].
    - apply Tuples.encode_inj in Hequal. subst v. rewrite slot_update_one_count_same.
      destruct b; lia.
    - rewrite slot_update_one_count_other; [lia |].
      intro Hequal. subst v. contradiction.
  Qed.

  (** A duplicate-free group spends at most one count increment per slot. *)
  Lemma slot_update_many_count_le : forall b u layouts state limit,
    NoDup (map fst layouts) ->
    (forall s v, (runtime_projection_count state s v <= limit)%N) ->
    forall s v, (runtime_projection_count (slot_update_many b u layouts state) s v <=
      N.succ limit)%N.
  Proof.
    intros b u layouts state limit Hnodup Hcount s v.
    destruct (in_dec N.eq_dec s (map fst layouts)) as [Hin | Hmissing].
    - apply in_map_iff in Hin. destruct Hin as [[t layout] [Hequal Hmember]].
      cbn [fst] in Hequal. subst t.
      rewrite (slot_snapshot_count _ _ s
        (slot_update_many_snapshot_member b u layouts Hnodup state s layout Hmember)).
      pose proof (slot_update_one_count_le b s (project_slot_layout layout u) state v).
      specialize (Hcount s v). lia.
    - rewrite (slot_snapshot_count _ _ s
        (slot_update_many_snapshot_other b u layouts state s Hmissing)).
      specialize (Hcount s v). lia.
  Qed.

  (** A single slot update extends a history using only cells in the recorded set. *)
  Lemma slot_update_one_history : forall written b s u state,
    (b = true -> incl u written) ->
    (forall t new, database_index_history I.empty I.insert I.remove written
      (runtime_slot_index state t new)) ->
    forall t new, database_index_history I.empty I.insert I.remove written
      (runtime_slot_index (slot_update_one b s u state) t new).
  Proof.
    intros written b s u state Hcells Hhistory t new.
    destruct (N.eq_dec t s) as [Hequal | Hdifferent].
    - subst t. rewrite slot_update_one_index. destruct b.
      + apply database_index_history_insert; [apply Hhistory | apply Hcells; reflexivity].
      + destruct (runtime_projection_count state s u) as [|p]; [apply Hhistory |].
        destruct p; try apply Hhistory. apply database_index_history_remove. apply Hhistory.
    - rewrite (slot_snapshot_index _ _ t
        (slot_update_one_snapshot_other b s u state t Hdifferent)).
      apply Hhistory.
  Qed.

  (** A finite group update extends every affected construction history. *)
  Lemma slot_update_many_history : forall written b u layouts state,
    (b = true -> forall s layout, In (s, layout) layouts ->
      incl (project_slot_layout layout u) written) ->
    (forall s new, database_index_history I.empty I.insert I.remove written
      (runtime_slot_index state s new)) ->
    forall s new, database_index_history I.empty I.insert I.remove written
      (runtime_slot_index (slot_update_many b u layouts state) s new).
  Proof.
    intros written b u layouts. induction layouts as [|[s layout] rest IH];
      intros state Hcells Hhistory t new; cbn [slot_update_many].
    - apply Hhistory.
    - apply IH.
      + intros Hb q block Hin. apply (Hcells Hb q block). now right.
      + apply slot_update_one_history; [| exact Hhistory].
        intro Hb. apply (Hcells Hb s layout). now left.
  Qed.

  (** Recording a duplicate-free cache pass maintains honest histories and count bounds. *)
  Lemma metadata_record_group : forall db b u layouts,
    metadata_ok db -> NoDup (map fst layouts) ->
    (b = true -> forall s layout, In (s, layout) layouts ->
      incl (project_slot_layout layout u) u) ->
    metadata_ok
      (database_record_cache u
        (slot_updated_counters layouts (slot_update_many b u layouts (db_runtime db)))
        (database_set_runtime (slot_update_many b u layouts (db_runtime db)) db)).
  Proof.
    intros db b u layouts
      (Hone & Hslots & Hcounter & Hnext & Hhistory & Hcount & Hgroups & Hbound)
      Hnodup Hcells.
    set (state := slot_update_many b u layouts (db_runtime db)).
    assert (Hframe : (runtime_slots state, runtime_function_slots state, runtime_slot_bound state) =
      (runtime_slots (db_runtime db), runtime_function_slots (db_runtime db),
       runtime_slot_bound (db_runtime db))).
    { exact (slot_update_many_preserves _
        (fun current => (runtime_slots current, runtime_function_slots current, runtime_slot_bound current))
        (fun all new counts current => eq_refl) b u layouts (db_runtime db)). }
    injection Hframe as Hlayout Hfunctions Hlimit.
    assert (Hwritten : incl (db_written_cells db) (u ++ db_written_cells db)).
    { intros c Hin. apply in_or_app. now right. }
    unfold metadata_ok, slots.
    cbn [database_record_cache database_set_runtime db_cache_updates db_written_cells
      db_index_counters db_runtime slots].
    split.
    - right. right. apply in_or_app. now right.
    - split.
      + rewrite Hlayout. right. right. apply in_or_app. now right.
      + split.
        * intros p Hequal. injection Hequal as Hequal. subst p. now left.
        * split.
          -- intros s new. right. right. apply in_or_app.
             destruct (in_dec N.eq_dec s (map fst layouts)) as [Hin | Hmissing].
             ++ left. apply in_map_iff in Hin. destruct Hin as [[t layout] [Hequal Hmember]].
                cbn [fst] in Hequal. subst t.
                exact (slot_updated_counters_member layouts state s layout Hmember new).
             ++ right. unfold state.
                rewrite (slot_snapshot_index _ _ s
                  (slot_update_many_snapshot_other b u layouts (db_runtime db) s Hmissing)).
                apply Hnext.
          -- split.
             ++ apply slot_update_many_history.
                ** intros Hb s layout Hin c Hcell. apply in_or_app. left.
                   exact (Hcells Hb s layout Hin c Hcell).
                ** intros s new. eapply database_index_history_weaken;
                     [exact Hwritten | apply Hhistory].
             ++ split.
                ** intros s v. rewrite N.succ_pos_spec.
                   exact (slot_update_many_count_le b u layouts (db_runtime db)
                     (db_cache_updates db) Hnodup Hcount s v).
                ** split.
                   --- rewrite Hfunctions, Hlayout. exact Hgroups.
                   --- rewrite Hlimit, Hlayout. exact Hbound.
  Qed.

  (** A tuple's multiplicity counts distinct row contributions with the same projection. *)
  Definition tuple_multiplicity (u : list (cell V.t))
      (tuples : list (list (cell V.t))) : nat :=
    length (filter (Tuples.eqb u) tuples).

  (** Adding one contribution increments exactly the matching tuple's multiplicity. *)
  Lemma tuple_multiplicity_cons : forall u v tuples,
    tuple_multiplicity u (v :: tuples) =
      if Tuples.eqb u v then S (tuple_multiplicity u tuples)
      else tuple_multiplicity u tuples.
  Proof.
    intros u v tuples. unfold tuple_multiplicity. cbn [filter].
    destruct (Tuples.eqb u v); reflexivity.
  Qed.

  (** A tuple contributes one to its own multiplicity. *)
  Lemma tuple_multiplicity_head : forall u tuples,
    tuple_multiplicity u (u :: tuples) = S (tuple_multiplicity u tuples).
  Proof.
    intros u tuples. rewrite tuple_multiplicity_cons.
    destruct (Tuples.eqb_spec u u); [reflexivity | contradiction].
  Qed.

  (** A different tuple does not change the queried multiplicity. *)
  Lemma tuple_multiplicity_other : forall u v tuples, u <> v ->
    tuple_multiplicity u (v :: tuples) = tuple_multiplicity u tuples.
  Proof.
    intros u v tuples Hdifferent. rewrite tuple_multiplicity_cons.
    destruct (Tuples.eqb_spec u v); [contradiction | reflexivity].
  Qed.

  (** Positive multiplicity is equivalent to presence in the contribution list. *)
  Lemma tuple_multiplicity_positive : forall u tuples,
    0 < tuple_multiplicity u tuples <-> In u tuples.
  Proof.
    intros u tuples. induction tuples as [| v rest IH].
    - unfold tuple_multiplicity. cbn. split; [lia | contradiction].
    - destruct (Tuples.eqb_spec u v) as [-> | Hdifferent].
      + rewrite tuple_multiplicity_head. cbn [In]. split; [auto | lia].
      + rewrite tuple_multiplicity_other by exact Hdifferent.
        rewrite IH. cbn [In]. intuition congruence.
  Qed.

  (** Zero multiplicity is equivalent to absence from the contribution list. *)
  Lemma tuple_multiplicity_zero : forall u tuples,
    tuple_multiplicity u tuples = 0 <-> ~ In u tuples.
  Proof.
    intros u tuples. split.
    - intros Hzero Hin. apply tuple_multiplicity_positive in Hin. lia.
    - intro Hmissing. destruct (tuple_multiplicity u tuples) eqn:Hcount; [reflexivity |].
      exfalso. apply Hmissing. apply tuple_multiplicity_positive. lia.
  Qed.

  (** Each slot cache tracks a multiset of row projections and a sound delta subset. *)
  Definition slot_cache_ok (state : database_runtime (cell V.t) I.t)
      (s : N) (arity : nat) (tuples : list (list (cell V.t))) : Prop :=
    I.wf arity (runtime_slot_index state s false) /\
    I.wf arity (runtime_slot_index state s true) /\
    (forall u, I.mem (runtime_slot_index state s false) u <-> In u tuples) /\
    (forall u, I.mem (runtime_slot_index state s true) u -> In u tuples) /\
    (forall u, N.to_nat (runtime_projection_count state s u) =
      tuple_multiplicity u tuples).

  (** Equal slot snapshots preserve the complete cache invariant. *)
  Lemma slot_cache_snapshot : forall first second s arity tuples,
    slot_snapshot first s = slot_snapshot second s ->
    slot_cache_ok second s arity tuples -> slot_cache_ok first s arity tuples.
  Proof.
    intros first second s arity tuples Hsnapshot Hcache.
    unfold slot_cache_ok in *. rewrite !(slot_snapshot_index first second s Hsnapshot).
    destruct Hcache as [Hall [Hnew [Hfull [Hdelta Hcounts]]]].
    split; [exact Hall |]. split; [exact Hnew |].
    split; [exact Hfull |]. split; [exact Hdelta |].
    intro u. rewrite (slot_snapshot_count first second s Hsnapshot). apply Hcounts.
  Qed.

  (** Inserting one contribution preserves both indexes and increments its exact count. *)
  Lemma slot_cache_insert : forall state s arity tuples u,
    slot_cache_ok state s arity tuples -> length u = arity ->
    slot_cache_ok (slot_update_one true s u state) s arity (u :: tuples).
  Proof.
    intros state s arity tuples u [Hall [Hnew [Hfull [Hdelta Hcounts]]]] Harity.
    unfold slot_cache_ok. rewrite !slot_update_one_index. split.
    - now apply I.wf_insert.
    - split; [now apply I.wf_insert |]. split.
      + intro v. rewrite (I.mem_insert arity u _ v Hall Harity), Hfull.
        cbn [In]. intuition congruence.
      + split.
        * intros v Hmember. apply (I.mem_insert arity u _ v Hnew Harity) in Hmember.
          cbn [In]. destruct Hmember as [-> | Hmember]; [auto | right; now apply Hdelta].
        * intro v. destruct (Tuples.eqb_spec v u) as [-> | Hdifferent].
          -- rewrite slot_update_one_count_same, N2Nat.inj_succ,
               tuple_multiplicity_head, Hcounts. reflexivity.
          -- rewrite slot_update_one_count_other by exact Hdifferent.
             rewrite tuple_multiplicity_other by exact Hdifferent. apply Hcounts.
  Qed.

  (** Removing one contribution decrements its multiplicity and preserves all other counts. *)
  Lemma slot_cache_remove_counts : forall state s u tuples,
    (forall v, N.to_nat (runtime_projection_count state s v) =
      tuple_multiplicity v (u :: tuples)) ->
    forall v, N.to_nat (runtime_projection_count (slot_update_one false s u state) s v) =
      tuple_multiplicity v tuples.
  Proof.
    intros state s u tuples Hcounts v. destruct (Tuples.eqb_spec v u) as [-> | Hdifferent].
    - rewrite slot_update_one_count_same, N2Nat.inj_pred, Hcounts,
        tuple_multiplicity_head. reflexivity.
    - rewrite slot_update_one_count_other by exact Hdifferent.
      rewrite Hcounts, tuple_multiplicity_other by exact Hdifferent. reflexivity.
  Qed.

  (** Removing a contribution keeps the indexes whenever its count was not one. *)
  Lemma slot_update_one_index_retained : forall state s u new,
    runtime_projection_count state s u <> 1%N ->
    runtime_slot_index (slot_update_one false s u state) s new =
      runtime_slot_index state s new.
  Proof.
    intros state s u new Hnotone. rewrite slot_update_one_index.
    destruct (runtime_projection_count state s u) as [| p] eqn:Hcount; [reflexivity |].
    destruct p; try reflexivity. exfalso. apply Hnotone. reflexivity.
  Qed.

  (** Deletion preserves shared projections and removes a tuple only at its last contribution. *)
  Lemma slot_cache_remove : forall state s arity tuples u,
    slot_cache_ok state s arity (u :: tuples) ->
    slot_cache_ok (slot_update_one false s u state) s arity tuples.
  Proof.
    intros state s arity tuples u [Hall [Hnew [Hfull [Hdelta Hcounts]]]].
    pose proof (slot_cache_remove_counts state s u tuples Hcounts) as Hupdated.
    destruct (tuple_multiplicity u tuples) as [| n] eqn:Hrest.
    - assert (Hone : runtime_projection_count state s u = 1%N).
      { apply N2Nat.inj. rewrite Hcounts, tuple_multiplicity_head, Hrest. reflexivity. }
      assert (Hmissing : ~ In u tuples) by (now apply tuple_multiplicity_zero).
      unfold slot_cache_ok. rewrite !slot_update_one_index, Hone. split.
      + now apply I.wf_remove.
      + split; [now apply I.wf_remove |]. split.
        * intro v. rewrite (I.mem_remove arity u _ v Hall), Hfull. cbn [In]. split.
          -- intros [Hdiffer [Hequal | Hin]]; [congruence | exact Hin].
          -- intro Hin. split; [intro Hequal; subst v; contradiction | now right].
        * split.
          -- intros v Hmember. apply (I.mem_remove arity u _ v Hnew) in Hmember.
             destruct Hmember as [Hdiffer Hmember]. specialize (Hdelta v Hmember).
             destruct Hdelta as [Hequal | Hin]; [congruence | exact Hin].
          -- exact Hupdated.
    - assert (Hnotone : runtime_projection_count state s u <> 1%N).
      { intro Hone. specialize (Hcounts u). rewrite Hone, tuple_multiplicity_head,
          Hrest in Hcounts. cbn in Hcounts. lia. }
      assert (Hpresent : In u tuples).
      { apply tuple_multiplicity_positive. rewrite Hrest. lia. }
      unfold slot_cache_ok. rewrite !slot_update_one_index_retained by exact Hnotone.
      split; [exact Hall |]. split; [exact Hnew |]. split.
      + intro v. rewrite Hfull. cbn [In]. split.
        * intros [Hequal | Hin]; [now subst v | exact Hin].
        * intro Hin. now right.
      + split.
        * intros v Hmember. specialize (Hdelta v Hmember).
          destruct Hdelta as [Hequal | Hin]; [now subst v | exact Hin].
        * exact Hupdated.
  Qed.

  (** Reordering contributions preserves every tuple's multiplicity. *)
  Lemma tuple_multiplicity_permutation : forall u first second,
    Permutation first second -> tuple_multiplicity u first = tuple_multiplicity u second.
  Proof.
    intros u first second Hperm. unfold tuple_multiplicity.
    apply Permutation_length. now apply filter_permutation.
  Qed.

  (** The cache invariant depends on contribution multiplicity, not enumeration order. *)
  Lemma slot_cache_permutation : forall state s arity first second,
    Permutation first second -> slot_cache_ok state s arity first ->
    slot_cache_ok state s arity second.
  Proof.
    intros state s arity first second Hperm [Hall [Hnew [Hfull [Hdelta Hcounts]]]].
    split; [exact Hall |]. split; [exact Hnew |]. split.
    - intro u. split.
      + intro Hmember. eapply Permutation_in; [exact Hperm | now apply Hfull].
      + intro Hin. apply Hfull. eapply Permutation_in;
          [apply Permutation_sym; exact Hperm | exact Hin].
    - split.
      + intros u Hmember. eapply Permutation_in; [exact Hperm | now apply Hdelta].
      + intro u. rewrite Hcounts. now apply tuple_multiplicity_permutation.
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

  (** Index maintenance preserves the prepared function-to-slot table. *)
  Lemma slots_update_function_slots : forall b f u db,
    runtime_function_slots (db_runtime (slots_update b f u db)) =
      runtime_function_slots (db_runtime db).
  Proof.
    intros b f u db. apply slots_update_preserves. intros. reflexivity.
  Qed.

  (** The optional function-group lookup is equivalent to walking its default-empty list. *)
  Lemma slots_update_runtime : forall b f u db,
    db_runtime (slots_update b f u db) =
      slot_update_many b u
        (database_group_entries f (runtime_function_slots (db_runtime db))) (db_runtime db).
  Proof.
    intros b f u db. unfold slots_update, database_group_entries.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db))); reflexivity.
  Qed.

  (** Every cache call records its input cells, including a missing function group. *)
  Lemma slots_update_written_cells : forall b f u db,
    db_written_cells (slots_update b f u db) = u ++ db_written_cells db.
  Proof.
    intros b f u db. unfold slots_update.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db))); reflexivity.
  Qed.

  (** The maintained update counter measures actual calls to the cache wrapper. *)
  Lemma slots_update_cache_updates : forall b f u db,
    db_cache_updates (slots_update b f u db) = N.succ (db_cache_updates db).
  Proof.
    intros b f u db. unfold slots_update.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db)));
      apply N.succ_pos_spec.
  Qed.

  (** A fitting projection returns one cell for every requested position. *)
  Lemma permute_length : forall perm u,
    Forall (fun p => p < length u) perm -> length (permute perm u) = length perm.
  Proof.
    intros perm u Hfits. induction Hfits as [| p rest Hbound Hfits IH].
    - reflexivity.
    - unfold permute in *. cbn [flat_map length].
      assert (Hpresent : nth_error u p <> None) by (now apply nth_error_Some).
      destruct (nth_error u p); [| contradiction]. cbn [option_list app length].
      now rewrite IH.
  Qed.

  (** A projection only selects cells that occur in its input tuple. *)
  Lemma permute_member : forall perm u c, In c (permute perm u) -> In c u.
  Proof.
    intros perm u c Hin. unfold permute in Hin. apply in_flat_map in Hin.
    destruct Hin as [position [_ Hin]].
    destruct (nth_error u position) as [found |] eqn:Hfound;
      cbn [option_list In] in Hin; [| contradiction].
    destruct Hin as [Hequal | Hin]; [subst found | contradiction].
    eapply nth_error_In. exact Hfound.
  Qed.

  (** Actual prepared groups satisfy the independent metadata preservation contract. *)
  Lemma metadata_slots_update : forall db b f u, metadata_ok db ->
    (b = true -> slots_fit db f (length u)) -> metadata_ok (slots_update b f u db).
  Proof.
    intros db b f u Hmetadata Hfits.
    pose proof Hmetadata as Hfacts.
    destruct Hfacts as (_ & _ & _ & _ & _ & _ & Hgroups & _).
    set (layouts := database_group_entries f (runtime_function_slots (db_runtime db))).
    change (metadata_ok
      (database_record_cache u
        (slot_updated_counters layouts (slot_update_many b u layouts (db_runtime db)))
        (database_set_runtime (slot_update_many b u layouts (db_runtime db)) db))).
    apply metadata_record_group; [exact Hmetadata | |].
    - unfold layouts. rewrite Hgroups. apply database_prepared_group_nodup.
    - intros Hb s layout Hin. unfold layouts in Hin. rewrite Hgroups in Hin.
      apply database_prepared_group_member in Hin.
      destruct Hin as [perm [Hslot Hequal]]. subst layout.
      assert (Hmember : In (f, perm) (slots db)) by (eapply nth_error_In; exact Hslot).
      destruct (Hfits Hb perm Hmember) as [_ Hpositions].
      rewrite project_slot_layout_correct by exact Hpositions.
      intros c Hcell. exact (permute_member perm u c Hcell).
  Qed.

  (** Replacing a row composes metadata preservation for its old and new contributions. *)
  Lemma metadata_row_replace : forall db f k previous o, metadata_ok db ->
    slots_fit db f (length (k ++ option_list o)) ->
    metadata_ok (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hmetadata Hnew. unfold row_replace.
    apply metadata_row_write. destruct previous as [before |].
    - apply metadata_slots_update.
      + apply metadata_slots_update; [exact Hmetadata | discriminate].
      + intros _. unfold slots_fit. rewrite slots_update_slots. exact Hnew.
    - apply metadata_slots_update; [exact Hmetadata | intros _; exact Hnew].
  Qed.

  (** Deleting a row needs no projection fit premise to preserve the metadata. *)
  Lemma metadata_row_delete : forall db f k, metadata_ok db ->
    metadata_ok (row_delete f k db).
  Proof.
    intros db f k Hmetadata. unfold row_delete.
    destruct (row_get f k db) as [output |]; [| exact Hmetadata].
    apply metadata_row_erase. apply metadata_slots_update;
      [exact Hmetadata | discriminate].
  Qed.

  (** A prepared group changes its own slot exactly once by the declared projection. *)
  Lemma slots_update_snapshot_same : forall db b f u s perm,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (f, perm) -> Forall (fun p => p < length u) perm ->
    slot_snapshot (db_runtime (slots_update b f u db)) s =
      slot_snapshot (slot_update_one b s (permute perm u) (db_runtime db)) s.
  Proof.
    intros db b f u s perm Hgroups Hslot Hfits. rewrite slots_update_runtime, Hgroups.
    assert (Hmember : In (s, prepare_slot_layout perm) (database_group_entries f
      (database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty))).
    { apply database_prepared_group_member. exists perm. split; [exact Hslot | reflexivity]. }
    rewrite (slot_update_many_snapshot_member b u _
      (database_prepared_group_nodup (slots db) f) _ s _ Hmember).
    rewrite project_slot_layout_correct by exact Hfits. reflexivity.
  Qed.

  (** A prepared function group cannot change a slot declared for another function. *)
  Lemma slots_update_snapshot_other : forall db b f u s g perm,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (g, perm) -> f <> g ->
    slot_snapshot (db_runtime (slots_update b f u db)) s = slot_snapshot (db_runtime db) s.
  Proof.
    intros db b f u s g perm Hgroups Hslot Hdifferent. rewrite slots_update_runtime.
    apply slot_update_many_snapshot_other. rewrite Hgroups.
    intro Hin. apply in_map_iff in Hin. destruct Hin as [[t layout] [Hequal Hmember]].
    cbn [fst] in Hequal. subst t. apply database_prepared_group_member in Hmember.
    destruct Hmember as [other [Hentry _]]. unfold slot_of in Hslot. congruence.
  Qed.

  (** Insertion through a prepared group adds the projected contribution to its slot cache. *)
  Lemma slots_update_cache_insert : forall db f u s perm tuples,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (f, perm) -> Forall (fun p => p < length u) perm ->
    slot_cache_ok (db_runtime db) s (length perm) tuples ->
    slot_cache_ok (db_runtime (slots_update true f u db)) s (length perm)
      (permute perm u :: tuples).
  Proof.
    intros db f u s perm tuples Hgroups Hslot Hfits Hcache.
    eapply slot_cache_snapshot.
    - exact (slots_update_snapshot_same db true f u s perm Hgroups Hslot Hfits).
    - apply slot_cache_insert; [exact Hcache | now apply permute_length].
  Qed.

  (** Deletion through a prepared group removes one projected contribution from its slot cache. *)
  Lemma slots_update_cache_remove : forall db f u s perm tuples,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (f, perm) -> Forall (fun p => p < length u) perm ->
    slot_cache_ok (db_runtime db) s (length perm) (permute perm u :: tuples) ->
    slot_cache_ok (db_runtime (slots_update false f u db)) s (length perm) tuples.
  Proof.
    intros db f u s perm tuples Hgroups Hslot Hfits Hcache.
    eapply slot_cache_snapshot.
    - exact (slots_update_snapshot_same db false f u s perm Hgroups Hslot Hfits).
    - now apply slot_cache_remove.
  Qed.

  (** Updating another function preserves every part of a slot's multiset cache. *)
  Lemma slots_update_cache_other : forall db b f u s g perm tuples,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (g, perm) -> f <> g ->
    slot_cache_ok (db_runtime db) s (length perm) tuples ->
    slot_cache_ok (db_runtime (slots_update b f u db)) s (length perm) tuples.
  Proof.
    intros db b f u s g perm tuples Hgroups Hslot Hdifferent Hcache.
    eapply slot_cache_snapshot.
    - exact (slots_update_snapshot_other db b f u s g perm Hgroups Hslot Hdifferent).
    - exact Hcache.
  Qed.

  (** A row enumeration contributes one projected tuple for each row of the selected function. *)
  Definition row_contributions (f : positive) (perm : list nat)
      (rows : list ((positive * list (cell V.t)) * option (cell V.t))) :=
    map (fun r => permute perm (snd (fst r) ++ option_list (snd r)))
      (filter (fun r => Pos.eqb (fst (fst r)) f) rows).

  (** A contributed tuple has a source row with the selected function and projection. *)
  Lemma row_contributions_member : forall f perm rows u,
    In u (row_contributions f perm rows) <->
      exists k o, In ((f, k), o) rows /\ u = permute perm (k ++ option_list o).
  Proof.
    intros f perm rows u. unfold row_contributions. split.
    - intro Hin. apply in_map_iff in Hin. destruct Hin as [[[g k] o] [Hvalue Hin]].
      apply filter_In in Hin as [Hin Hfunction]. cbn [fst] in Hfunction.
      apply Pos.eqb_eq in Hfunction. subst g. exists k, o. split; [exact Hin |].
      symmetry. exact Hvalue.
    - intros [k [o [Hin Hvalue]]]. apply in_map_iff. exists ((f, k), o).
      split; [symmetry; exact Hvalue |]. apply filter_In.
      split; [exact Hin | apply Pos.eqb_refl].
  Qed.

  (** Row permutations induce permutations of their projected contributions. *)
  Lemma row_contributions_permutation : forall f perm first second,
    Permutation first second ->
    Permutation (row_contributions f perm first) (row_contributions f perm second).
  Proof.
    intros f perm first second Hperm. unfold row_contributions.
    apply Permutation_map. now apply filter_permutation.
  Qed.

  (** A row of the selected function contributes its projected tuple once. *)
  Lemma row_contributions_same : forall f perm k o rows,
    row_contributions f perm (((f, k), o) :: rows) =
      permute perm (k ++ option_list o) :: row_contributions f perm rows.
  Proof.
    intros f perm k o rows. unfold row_contributions. cbn [filter map fst snd].
    now rewrite Pos.eqb_refl.
  Qed.

  (** Rows of another function do not contribute to the selected projection multiset. *)
  Lemma row_contributions_other : forall f g perm k o rows, f <> g ->
    row_contributions g perm (((f, k), o) :: rows) = row_contributions g perm rows.
  Proof.
    intros f g perm k o rows Hdifferent. unfold row_contributions.
    cbn [filter map fst snd]. apply Pos.eqb_neq in Hdifferent. now rewrite Hdifferent.
  Qed.

  (** Enumerating the actual row map agrees with the public row predicate. *)
  Lemma row_elements_member : forall db f k o, RowMap.wf (runtime_rows (db_runtime db)) ->
    (In ((f, k), o) (RowMap.elements (runtime_rows (db_runtime db))) <-> row (view db) f k o).
  Proof.
    intros db f k o Hmap. change (In ((f, k), o)
      (RowMap.elements (runtime_rows (db_runtime db))) <->
      RowMap.get (f, k) (runtime_rows (db_runtime db)) = Some o).
    now apply RowMap.elements_spec.
  Qed.

  (** A well-formed count equals multiplicity in the actual row projection multiset. *)
  Lemma wf_slot_projection_count : forall db s f perm u, wf db ->
    slot_of db s = Some (f, perm) ->
    N.to_nat (runtime_projection_count (db_runtime db) s u) =
      tuple_multiplicity u
        (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db)))).
  Proof.
    intros db s f perm u Hwf Hslot.
    destruct (wf_projection_counts db Hwf s f perm u Hslot)
      as [rs [Hdistinct [Hmembers Hcount]]].
    change (N.to_nat (stored_projection_count db s u) = tuple_multiplicity u
      (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db))))).
    rewrite Hcount. symmetry.
    unfold tuple_multiplicity, row_contributions. eapply filtered_projection_witness_length.
    - exact Tuples.eqb_spec.
    - apply RowFacts.elements_nodup_pairs. now apply wf_row_map.
    - exact Hdistinct.
    - intro r. rewrite Hmembers, Pos.eqb_eq. reflexivity.
  Qed.

  (** Every cached member in a declared slot has a source in the actual projection multiset. *)
  Lemma wf_slot_cache_sound : forall db s f perm, wf db ->
    slot_of db s = Some (f, perm) -> forall new u,
    I.mem (runtime_slot_index (db_runtime db) s new) u ->
    In u (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db)))).
  Proof.
    intros db s f perm Hwf Hslot new u Hmember.
    assert (Hinside : (s < runtime_slot_bound (db_runtime db))%N).
    { eapply slot_of_inside_bound; eassumption. }
    rewrite <- (index_runtime_slot db s new Hinside) in Hmember.
    destruct (wf_index_sound db Hwf s new u Hmember)
      as [g [other [k [o [Hentry [Hrow Hvalue]]]]]].
    rewrite Hslot in Hentry. injection Hentry as <- <-.
    apply row_contributions_member. exists k, o. split; [| exact Hvalue].
    apply row_elements_member; [now apply wf_row_map | exact Hrow].
  Qed.

  (** Every declared slot in a well-formed database has the complete multiset cache invariant. *)
  Lemma wf_slot_cache : forall db s f perm, wf db -> slot_of db s = Some (f, perm) ->
    slot_cache_ok (db_runtime db) s (length perm)
      (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db)))).
  Proof.
    intros db s f perm Hwf Hslot.
    assert (Hinside : (s < runtime_slot_bound (db_runtime db))%N).
    { eapply slot_of_inside_bound; eassumption. }
    assert (Harity : forall new, I.wf (length perm) (runtime_slot_index (db_runtime db) s new)).
    { intro new. rewrite <- (index_runtime_slot db s new Hinside).
      exact (wf_index_arity db Hwf s new f perm Hslot). }
    split; [apply Harity |]. split; [apply Harity |]. split.
    - intro u. split; [now apply wf_slot_cache_sound with (f := f) (perm := perm) |].
      intro Hin. apply row_contributions_member in Hin as [k [o [Hrow ->]]].
      apply row_elements_member in Hrow; [| now apply wf_row_map].
      rewrite <- (index_runtime_slot db s false Hinside).
      exact (wf_index_complete db Hwf s f perm k o Hslot Hrow).
    - split.
      + now apply wf_slot_cache_sound with (f := f) (perm := perm).
      + intro u. now apply wf_slot_projection_count.
  Qed.

  (** A declared fitting slot has only positions within the supplied tuple length. *)
  Lemma slot_projection_fits : forall db s f perm n,
    slot_of db s = Some (f, perm) -> slots_fit db f n -> Forall (fun p => p < n) perm.
  Proof.
    intros db s f perm n Hslot Hfits.
    assert (Hmember : In (f, perm) (slots db)) by (eapply nth_error_In; exact Hslot).
    exact (proj2 (Hfits perm Hmember)).
  Qed.

  (** Inserting a row contribution updates every declared slot's virtual row multiset. *)
  Lemma slots_update_cache_row_insert : forall db f k o s g perm rows,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (g, perm) -> slots_fit db f (length (k ++ option_list o)) ->
    slot_cache_ok (db_runtime db) s (length perm) (row_contributions g perm rows) ->
    slot_cache_ok (db_runtime (slots_update true f (k ++ option_list o) db)) s (length perm)
      (row_contributions g perm (((f, k), o) :: rows)).
  Proof.
    intros db f k o s g perm rows Hgroups Hslot Hfits Hcache.
    destruct (Pos.eq_dec f g) as [-> | Hdifferent].
    - rewrite row_contributions_same. apply slots_update_cache_insert; try assumption.
      eapply slot_projection_fits; eassumption.
    - rewrite row_contributions_other by exact Hdifferent.
      apply slots_update_cache_other with (g := g); assumption.
  Qed.

  (** Removing a row contribution updates every declared slot's virtual row multiset. *)
  Lemma slots_update_cache_row_remove : forall db f k o s g perm rows,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (g, perm) -> slots_fit db f (length (k ++ option_list o)) ->
    slot_cache_ok (db_runtime db) s (length perm)
      (row_contributions g perm (((f, k), o) :: rows)) ->
    slot_cache_ok (db_runtime (slots_update false f (k ++ option_list o) db)) s (length perm)
      (row_contributions g perm rows).
  Proof.
    intros db f k o s g perm rows Hgroups Hslot Hfits Hcache.
    destruct (Pos.eq_dec f g) as [-> | Hdifferent].
    - rewrite row_contributions_same in Hcache. apply slots_update_cache_remove; try assumption.
      eapply slot_projection_fits; eassumption.
    - rewrite row_contributions_other in Hcache by exact Hdifferent.
      apply slots_update_cache_other with (g := g); assumption.
  Qed.

  (** The final row-table write leaves the already-maintained slot caches unchanged. *)
  Lemma row_write_slot_snapshot : forall db f k o s,
    slot_snapshot (db_runtime (row_write f k o db)) s = slot_snapshot (db_runtime db) s.
  Proof.
    intros db f k o s. reflexivity.
  Qed.

  (** Row replacement removes its optional old contribution and adds its new contribution. *)
  Lemma row_replace_cache_list : forall db f k previous o s g perm rest,
    runtime_function_slots (db_runtime db) =
      database_slot_groups 0 (prepare_slot_layouts (slots db)) PTrieCode.empty ->
    slot_of db s = Some (g, perm) -> slots_fit db f (length (k ++ option_list o)) ->
    (forall before, previous = Some before ->
      slots_fit db f (length (k ++ option_list before))) ->
    slot_cache_ok (db_runtime db) s (length perm) (row_contributions g perm
      (option_list (option_map (pair (f, k)) previous) ++ rest)) ->
    slot_cache_ok (db_runtime (row_replace f k previous o db)) s (length perm)
      (row_contributions g perm (((f, k), o) :: rest)).
  Proof.
    intros db f k previous o s g perm rest Hgroups Hslot Hnew Hbefore Hcache.
    unfold row_replace. eapply slot_cache_snapshot; [apply row_write_slot_snapshot |].
    destruct previous as [before |]; cbn [option_map option_list app] in Hcache |- *.
    - apply slots_update_cache_row_insert.
      + rewrite slots_update_function_slots, slots_update_slots. exact Hgroups.
      + unfold slot_of. rewrite slots_update_slots. exact Hslot.
      + unfold slots_fit. rewrite slots_update_slots. exact Hnew.
      + exact (slots_update_cache_row_remove db f k before s g perm rest
          Hgroups Hslot (Hbefore before eq_refl) Hcache).
    - exact (slots_update_cache_row_insert db f k o s g perm rest Hgroups Hslot Hnew Hcache).
  Qed.

  (** The four cache fields relate both indexes and stored counts to the actual row map. *)
  Definition database_cache_correct (db : t) : Prop :=
    (forall s new u, I.mem (index s new db) u ->
      exists f perm k o, slot_of db s = Some (f, perm) /\ row (view db) f k o /\
        u = permute perm (k ++ option_list o)) /\
    (forall s f perm k o, slot_of db s = Some (f, perm) -> row (view db) f k o ->
      I.mem (index s false db) (permute perm (k ++ option_list o))) /\
    (forall s new f perm, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s new db)) /\ projection_counts_ok db.

  (** A correct slot bound exposes the raw cache at every declared slot. *)
  Lemma index_declared_slot : forall db s new f perm,
    runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db)) ->
    slot_of db s = Some (f, perm) ->
    index s new db = runtime_slot_index (db_runtime db) s new.
  Proof.
    intros db s new f perm Hbound Hslot. apply index_runtime_slot. rewrite Hbound.
    assert (Hinside : N.to_nat s < length (slots db)).
    { apply nth_error_Some. unfold slot_of in Hslot. congruence. }
    lia.
  Qed.

  (** A correct slot bound hides all cache entries without a declared slot. *)
  Lemma index_undeclared_slot : forall db s new,
    runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db)) ->
    slot_of db s = None -> index s new db = I.empty.
  Proof.
    intros db s new Hbound Hslot. apply index_outside_bound. rewrite Hbound.
    unfold slot_of in Hslot. apply nth_error_None in Hslot. lia.
  Qed.

  (** Exact per-slot multiplicities provide the finite witnesses required by stored counts. *)
  Lemma projection_counts_from_slot_caches : forall db,
    RowMap.wf (runtime_rows (db_runtime db)) ->
    (forall s f perm, slot_of db s = Some (f, perm) ->
      slot_cache_ok (db_runtime db) s (length perm)
        (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db))))) ->
    projection_counts_ok db.
  Proof.
    intros db Hmap Hcaches s f perm u Hslot.
    destruct (Hcaches s f perm Hslot) as [_ [_ [_ [_ Hcounts]]]].
    destruct (filtered_projection_witness _ _ (fun r => Pos.eqb (fst (fst r)) f)
      (fun r => permute perm (snd (fst r) ++ option_list (snd r)))
      Tuples.eqb Tuples.eqb_spec u (RowMap.elements (runtime_rows (db_runtime db)))
      (RowFacts.elements_nodup_pairs _ _ Hmap)) as [rs [Hdistinct [Hmembers Hlength]]].
    exists rs. split; [exact Hdistinct |]. split.
    - intro r. rewrite Hmembers, Pos.eqb_eq. reflexivity.
    - change (N.to_nat (runtime_projection_count (db_runtime db) s u) = length rs).
      rewrite Hcounts. exact Hlength.
  Qed.

  (** The raw per-slot invariants imply all four public database cache fields. *)
  Lemma database_cache_correct_from_slots : forall db,
    RowMap.wf (runtime_rows (db_runtime db)) ->
    runtime_slot_bound (db_runtime db) = N.of_nat (length (slots db)) ->
    (forall s f perm, slot_of db s = Some (f, perm) ->
      slot_cache_ok (db_runtime db) s (length perm)
        (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db))))) ->
    database_cache_correct db.
  Proof.
    intros db Hmap Hbound Hcaches. split.
    - intros s new u Hmember. destruct (slot_of db s) as [[f perm] |] eqn:Hslot.
      + rewrite (index_declared_slot db s new f perm Hbound Hslot) in Hmember.
        destruct (Hcaches s f perm Hslot) as [_ [_ [Hfull [Hdelta _]]]].
        assert (Hin : In u
          (row_contributions f perm (RowMap.elements (runtime_rows (db_runtime db))))).
        { destruct new; [now apply Hdelta | now apply Hfull]. }
        apply row_contributions_member in Hin as [k [o [Hrow Hvalue]]].
        exists f, perm, k, o. split; [reflexivity |]. split; [| exact Hvalue].
        apply row_elements_member; assumption.
      + rewrite (index_undeclared_slot db s new Hbound Hslot) in Hmember.
        exfalso. exact (I.mem_empty u Hmember).
    - split.
      + intros s f perm k o Hslot Hrow.
        rewrite (index_declared_slot db s false f perm Hbound Hslot).
        destruct (Hcaches s f perm Hslot) as [_ [_ [Hfull _]]]. apply Hfull.
        apply row_contributions_member. exists k, o. split; [| reflexivity].
        apply row_elements_member; assumption.
      + split.
        * intros s new f perm Hslot.
          rewrite (index_declared_slot db s new f perm Hbound Hslot).
          destruct (Hcaches s f perm Hslot) as [Hall [Hnew _]]. destruct new; assumption.
        * apply projection_counts_from_slot_caches; assumption.
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

  (** A row replacement records its new tuple and retains every earlier written cell. *)
  Lemma row_replace_written : forall db f k previous o,
    db_written_cells (row_replace f k previous o db) =
      (k ++ option_list o) ++
        match previous with
        | Some before => (k ++ option_list before) ++ db_written_cells db
        | None => db_written_cells db
        end.
  Proof.
    intros db f k [before |] o; unfold row_replace, row_write;
      cbn [database_set_runtime db_written_cells]; rewrite !slots_update_written_cells;
      reflexivity.
  Qed.

  (** Replacement covers the new row by its recording and every retained row by its old history. *)
  Lemma row_replace_recorded_rows : forall db f k previous o, recorded_rows db ->
    recorded_rows (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hrecorded g args output c Hrow Hin.
    rewrite row_replace_written.
    apply row_replace_sources in Hrow as [Hold | [-> [-> ->]]].
    - apply in_or_app. right. destruct previous as [before |].
      + apply in_or_app. right. exact (Hrecorded g args output c Hold Hin).
      + exact (Hrecorded g args output c Hold Hin).
    - apply in_or_app. now left.
  Qed.

  (** A fitting new contribution preserves the complete row and cache history invariant. *)
  Lemma database_history_row_replace : forall db f k previous o,
    database_history db -> slots_fit db f (length (k ++ option_list o)) ->
    database_history (row_replace f k previous o db).
  Proof.
    intros db f k previous o [Hmetadata Hrows] Hfits. split.
    - now apply metadata_row_replace.
    - now apply row_replace_recorded_rows.
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

  (** Row and cache replacement preserves every observation outside the changed fields. *)
  Lemma row_replace_preserves : forall (A : Type)
      (observe : database_runtime (cell V.t) I.t -> A),
    (forall rows state, observe (runtime_set_rows rows state) = observe state) ->
    (forall flag state, observe (runtime_set_changed flag state) = observe state) ->
    (forall all new counts state,
      observe (runtime_set_indexes all new counts state) = observe state) ->
    forall f k previous o db,
      observe (db_runtime (row_replace f k previous o db)) = observe (db_runtime db).
  Proof.
    intros A observe Hrows Hchanged Hindexes f k [before |] o db;
      unfold row_replace, row_write; cbn [database_set_runtime db_runtime];
      rewrite Hrows, Hchanged;
      repeat rewrite (slots_update_preserves A observe Hindexes); reflexivity.
  Qed.

  (** Index maintenance preserves the row map itself before its final binding update. *)
  Lemma row_replace_map : forall f k previous o db,
    runtime_rows (db_runtime (row_replace f k previous o db)) =
      RowMap.set (f, k) o (runtime_rows (db_runtime db)).
  Proof.
    intros f k [before |] o db; unfold row_replace, row_write;
      cbn [database_set_runtime db_runtime runtime_set_rows runtime_rows];
      repeat rewrite (slots_update_preserves _ (@runtime_rows (cell V.t) I.t)
        (fun all new counts state => eq_refl)); reflexivity.
  Qed.

  (** Replacing one actual binding preserves the complete multiset cache at every declared slot. *)
  Lemma row_replace_slot_cache : forall db f k previous o s g perm,
    wf db -> old db f k = previous -> slots_fit db f (length (k ++ option_list o)) ->
    slot_of db s = Some (g, perm) ->
    slot_cache_ok (db_runtime (row_replace f k previous o db)) s (length perm)
      (row_contributions g perm
        (RowMap.elements (runtime_rows (db_runtime (row_replace f k previous o db))))).
  Proof.
    intros db f k previous o s g perm Hwf Hprevious Hfits Hslot.
    pose proof (wf_row_map db Hwf) as Hmap.
    destruct (RowFacts.set_elements_decomposition _ _ (f, k) previous o Hmap Hprevious)
      as [rest [Hsource [Htarget _]]].
    rewrite row_replace_map. eapply slot_cache_permutation.
    - apply row_contributions_permutation. apply Permutation_sym. exact Htarget.
    - apply (row_replace_cache_list db f k previous o s g perm rest).
      + now apply wf_group_table.
      + exact Hslot.
      + exact Hfits.
      + intros before Hbefore. apply (wf_row_slots db Hwf f k before).
        change (old db f k = Some before). now rewrite Hprevious.
      + eapply slot_cache_permutation.
        * apply row_contributions_permutation. exact Hsource.
        * exact (wf_slot_cache db s g perm Hwf Hslot).
  Qed.

  (** Row replacement preserves both indexes and exact projection counts without an output-wf premise. *)
  Lemma row_replace_cache_correct : forall db f k previous o,
    wf db -> old db f k = previous -> slots_fit db f (length (k ++ option_list o)) ->
    database_cache_correct (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hwf Hprevious Hfits.
    apply database_cache_correct_from_slots.
    - rewrite row_replace_map. apply RowMap.wf_set. now apply wf_row_map.
    - change (runtime_slot_bound (db_runtime (row_replace f k previous o db)) =
        N.of_nat (length (slots (row_replace f k previous o db)))).
      rewrite (row_replace_preserves _ (@runtime_slot_bound (cell V.t) I.t)
        (fun rows state => eq_refl) (fun flag state => eq_refl)
        (fun all new counts state => eq_refl) f k previous o db), row_replace_slots.
      now apply wf_slot_bound.
    - intros s g perm Hslot. apply row_replace_slot_cache; try assumption.
      unfold slot_of in *. now rewrite row_replace_slots in Hslot.
  Qed.

  (** Replacing a well-kinded row preserves the kind condition for every stored binding. *)
  Lemma row_replace_kinds : forall db f k previous o,
    wf db -> kind_ok db f k o ->
    forall g args output, row (view (row_replace f k previous o db)) g args output ->
      match kind (view (row_replace f k previous o db)) g, output with
      | Some ORel, None | Some OId, Some (Id _) | Some (OLat _), Some (Val _) => True
      | _, _ => False
      end.
  Proof.
    intros db f k previous o Hwf [_ [_ Hkind]] g args output Hrow.
    rewrite row_replace_kind. apply row_replace_sources in Hrow as [Hold | [-> [-> ->]]].
    - exact (wf_row_kind db Hwf g args output Hold).
    - exact Hkind.
  Qed.

  (** A replacement whose new cells are allocated keeps every row identifier allocated. *)
  Lemma row_replace_allocated : forall db f k previous o,
    wf db -> kind_ok db f k o ->
    forall g args output i, row (view (row_replace f k previous o db)) g args output ->
      In (Id i) (args ++ option_list output) -> allocated (row_replace f k previous o db) i.
  Proof.
    intros db f k previous o Hwf [Hids _] g args output i Hrow Hin.
    unfold allocated. rewrite row_replace_ids.
    apply row_replace_sources in Hrow as [Hold | [-> [-> ->]]].
    - exact (wf_row_ids db Hwf g args output i Hold Hin).
    - exact (Hids i Hin).
  Qed.

  (** A fitting replacement preserves all row lengths required by the stored slots. *)
  Lemma row_replace_fits : forall db f k previous o,
    wf db -> kind_ok db f k o ->
    forall g args output, row (view (row_replace f k previous o db)) g args output ->
      slots_fit (row_replace f k previous o db) g (length (args ++ option_list output)).
  Proof.
    intros db f k previous o Hwf [_ [Hfits _]] g args output Hrow.
    unfold slots_fit. rewrite row_replace_slots. fold (slots_fit db g (length (args ++ option_list output))).
    apply row_replace_sources in Hrow as [Hold | [-> [-> ->]]].
    - exact (wf_row_slots db Hwf g args output Hold).
    - exact Hfits.
  Qed.

  (** A canonical replacement leaves quiet databases canonical. *)
  Lemma row_replace_canonical : forall db f k previous o,
    wf db -> (forall i, In (Id i) (k ++ option_list o) -> repr db i = i) ->
    pending (row_replace f k previous o db) = 0 -> canonical (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hwf Hnew Hquiet g args output Hrow i Hin.
    unfold repr. rewrite row_replace_forest. fold (repr db i).
    rewrite row_replace_pending in Hquiet.
    apply row_replace_sources in Hrow as [Hold | [-> [-> ->]]].
    - exact (wf_quiet_canonical db Hwf Hquiet g args output Hold i Hin).
    - exact (Hnew i Hin).
  Qed.

  (** Cache updates leave the stored pending-work counter unchanged. *)
  Lemma slots_update_npending : forall b f u db,
    db_npending (slots_update b f u db) = db_npending db.
  Proof.
    intros b f u db. unfold slots_update.
    destruct (PTrieCode.get f (runtime_function_slots (db_runtime db))); reflexivity.
  Qed.

  (** Replacing one row does not change the stored pending-work counter. *)
  Lemma row_replace_npending : forall f k previous o db,
    db_npending (row_replace f k previous o db) = db_npending db.
  Proof.
    intros f k [before |] o db; unfold row_replace, row_write;
      cbn [database_set_runtime db_npending]; now rewrite !slots_update_npending.
  Qed.

  (** Cache correctness is the only remaining obligation for a well-kinded canonical row update. *)
  Lemma row_replace_wf_from_caches : forall db f k previous o,
    wf db -> kind_ok db f k o ->
    (forall i, In (Id i) (k ++ option_list o) -> repr db i = i) ->
    (forall s new u, I.mem (index s new (row_replace f k previous o db)) u ->
      exists g perm args output,
        slot_of (row_replace f k previous o db) s = Some (g, perm) /\
        row (view (row_replace f k previous o db)) g args output /\
        u = permute perm (args ++ option_list output)) ->
    (forall s g perm args output,
      slot_of (row_replace f k previous o db) s = Some (g, perm) ->
      row (view (row_replace f k previous o db)) g args output ->
      I.mem (index s false (row_replace f k previous o db))
        (permute perm (args ++ option_list output))) ->
    (forall s new g perm,
      slot_of (row_replace f k previous o db) s = Some (g, perm) ->
      I.wf (length perm) (index s new (row_replace f k previous o db))) ->
    projection_counts_ok (row_replace f k previous o db) ->
    wf (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hwf Hkind Hcanonical Hsound Hcomplete Harity Hcounts.
    assert (Hruntime :
      (runtime_equalities (db_runtime (row_replace f k previous o db)),
       runtime_queue (db_runtime (row_replace f k previous o db)),
       runtime_function_slots (db_runtime (row_replace f k previous o db)),
       runtime_max_name (db_runtime (row_replace f k previous o db)),
       runtime_slot_bound (db_runtime (row_replace f k previous o db))) =
      (runtime_equalities (db_runtime db), runtime_queue (db_runtime db),
       runtime_function_slots (db_runtime db), runtime_max_name (db_runtime db),
       runtime_slot_bound (db_runtime db))).
    { exact (row_replace_preserves _
        (fun state => (runtime_equalities state, runtime_queue state,
          runtime_function_slots state, runtime_max_name state, runtime_slot_bound state))
        (fun rows state => eq_refl) (fun flag state => eq_refl)
        (fun all new counts state => eq_refl) f k previous o db). }
    injection Hruntime as Hlog Hqueue Hgroups Hmax Hbound.
    change (runtime_equalities (db_runtime (row_replace f k previous o db)) =
      runtime_equalities (db_runtime db)) in Hlog.
    change (runtime_queue (db_runtime (row_replace f k previous o db)) =
      runtime_queue (db_runtime db)) in Hqueue.
    change (runtime_function_slots (db_runtime (row_replace f k previous o db)) =
      runtime_function_slots (db_runtime db)) in Hgroups.
    change (runtime_max_name (db_runtime (row_replace f k previous o db)) =
      runtime_max_name (db_runtime db)) in Hmax.
    change (runtime_slot_bound (db_runtime (row_replace f k previous o db)) =
      runtime_slot_bound (db_runtime db)) in Hbound.
    unfold wf, database_wf. split.
    { rewrite row_replace_forest. exact (wf_forest db Hwf). }
    split.
    { intro i. rewrite row_replace_forest. unfold allocated. rewrite row_replace_ids.
      exact (wf_forest_members db Hwf i). }
    split.
    { rewrite row_replace_forest, row_replace_ids. exact (wf_forest_count db Hwf). }
    split.
    { rewrite row_replace_forest, row_replace_ids. exact (wf_forest_width db Hwf). }
    split.
    { intros i j. rewrite row_replace_same. unfold repr. rewrite row_replace_forest.
      exact (wf_equalities db Hwf i j). }
    split.
    { rewrite Hlog. unfold allocated. rewrite row_replace_ids. exact (wf_log_allocated db Hwf). }
    split.
    { rewrite row_replace_map. apply RowMap.wf_set. exact (wf_row_map db Hwf). }
    split; [exact (row_replace_kinds db f k previous o Hwf Hkind) |].
    split; [exact (row_replace_allocated db f k previous o Hwf Hkind) |].
    split; [exact (row_replace_fits db f k previous o Hwf Hkind) |].
    split.
    { intros g output Houtput. rewrite row_replace_kind in Houtput. rewrite Hmax.
      exact (wf_kind_bound db Hwf g output Houtput). }
    split.
    { rewrite Hbound, row_replace_slots. exact (wf_slot_bound db Hwf). }
    split.
    { rewrite row_replace_npending, row_replace_pending. exact (wf_pending_count db Hwf). }
    split.
    { rewrite Hqueue. unfold allocated. rewrite row_replace_ids. exact (wf_queue_allocated db Hwf). }
    split; [exact (row_replace_canonical db f k previous o Hwf Hcanonical) |].
    split; [exact Hsound |]. split; [exact Hcomplete |]. split; [exact Harity |].
    split; [rewrite Hgroups, row_replace_slots; exact (wf_group_table db Hwf) |].
    split; [exact Hcounts |]. split.
    { rewrite Hmax, row_replace_kind. exact (wf_max_name_attained db Hwf). }
    apply database_history_row_replace.
    - exact (wf_history db Hwf).
    - exact (proj1 (proj2 Hkind)).
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
    pose proof (database_history_allocate_id db (N.succ_pos (ids db))
      (wf_history db Hwf)) as Hhistory.
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
      destruct (N.compare s (N.of_nat (length sl))); try reflexivity;
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

  (** Empty rows and empty construction histories establish the history invariant initially. *)
  Lemma database_history_init : forall ds sl, database_history (init ds sl).
  Proof.
    intros ds sl. split; [apply metadata_init |].
    intros f k o c Hrow _. exfalso. exact (init_rows_empty ds sl f k o Hrow).
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

  (** Initialization records a name maximum that is attained by its declaration table. *)
  Lemma init_max_name_attained : forall ds sl,
    runtime_max_name (db_runtime (init ds sl)) = 1%positive \/
      kind (view (init ds sl)) (runtime_max_name (db_runtime (init ds sl))) <> None.
  Proof.
    intros ds sl. change (database_max_name ds = 1%positive \/
      PTrieCode.get (database_max_name ds) (database_kinds ds) <> None).
    unfold database_kinds. rewrite declaration_trie_lookup. apply database_max_name_attained.
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
    split; [reflexivity |]. split; [apply init_projection_counts |].
    split; [apply init_max_name_attained | apply database_history_init].
  Qed.

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
    change ((match N.compare s (runtime_slot_bound (db_runtime db)) with
      | Lt => match PTrieCode.get (N.succ_pos s) (@PTrieCode.empty I.t) with
        | Some ix => ix
        | None => I.empty
        end
      | _ => I.empty
      end) = I.empty).
    destruct (N.compare s (runtime_slot_bound (db_runtime db))); try reflexivity.
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
        Hcanonical & Hsound & Hcomplete & Harity & Hgroups & Hcounts & Hmaxname & Hhistory).
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
          -- split; [exact Hgroups |]. split; [exact Hcounts |].
             split; [exact Hmaxname | now apply database_history_advance].
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
    pose proof (database_history_union db i j (wf_history db Hwf)) as Hhistory.
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
  Proof.
    intros db Hwf Hcanonical Hpending. unfold rebuild.
    rewrite (LoopNFacts.loopN_stop _ _ db_rstep (db_rebuild_fuel db) (db, []) db).
    - reflexivity.
    - unfold db_rebuild_fuel. lia.
    - unfold pending in Hpending.
      destruct (runtime_queue (db_runtime db)) as [| i rest] eqn:Hqueue;
        [| discriminate].
      cbn [db_rstep fst snd]. unfold db_pop_loser. now rewrite Hqueue.
  Qed.

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

  (** Normalizing a row tuple is the same as normalizing its key and optional output. *)
  Lemma canon_row_tuple : forall db k o,
    map (canon db) (k ++ option_list o) =
      map (canon db) k ++ option_list (option_map (canon db) o).
  Proof.
    intros db k [c |]; rewrite map_app; reflexivity.
  Qed.

  (** Every identifier in a normalized tuple is already its own representative. *)
  Lemma canon_key_fixed : forall db k, wf db ->
    forall i, In (Id i) (map (canon db) k) -> repr db i = i.
  Proof.
    intros db k Hwf i Hin. apply in_map_iff in Hin as [c [Hcell Hin]].
    destruct c as [j | v]; cbn [canon] in Hcell; [| discriminate Hcell].
    injection Hcell as <-. apply repr_idem. exact Hwf.
  Qed.

  (** Normalization preserves allocation, tuple length and the declared output shape. *)
  Lemma kind_ok_canon : forall db f k o, wf db -> kind_ok db f k o ->
    kind_ok db f (map (canon db) k) (option_map (canon db) o).
  Proof.
    intros db f k o Hwf [Hids [Hfits Hkind]]. unfold kind_ok. split.
    - intros i Hin. rewrite <- canon_row_tuple in Hin.
      exact (canon_key_allocated db (k ++ option_list o) Hwf Hids i Hin).
    - split.
      + rewrite <- canon_row_tuple, length_map. exact Hfits.
      + destruct o as [[i | v] |]; exact Hkind.
  Qed.

  (** A fresh constructor row has allocated cells, the required slots and its declared kind. *)
  Lemma fresh_constructor_kind_ok : forall db f k, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    kind (view db) f = Some OId ->
    kind_ok (allocate_id (N.succ_pos (ids db)) db) f (map (canon db) k)
      (Some (Id (N.succ_pos (ids db)))).
  Proof.
    intros db f k Hwf Hargs Hfits Hkind. unfold kind_ok. split.
    - intros i Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + apply allocate_next_monotone. exact (canon_key_allocated db k Hwf Hargs i Hin).
      + cbn [option_list In] in Hin. destruct Hin as [Heq | Hfalse]; [| contradiction].
        injection Heq as <-. unfold allocated. rewrite allocate_id_ids. lia.
    - split.
      + unfold slots_fit in *. rewrite allocate_id_slots, length_app, length_map.
        cbn [option_list length]. replace (length k + 1) with (S (length k)) by lia.
        exact Hfits.
      + rewrite allocate_id_view, Hkind. exact I.
  Qed.

  (** The fresh singleton and every normalized key identifier remain canonical after allocation. *)
  Lemma fresh_constructor_canonical : forall db k, wf db ->
    forall i, In (Id i)
      (map (canon db) k ++ option_list (Some (Id (N.succ_pos (ids db))))) ->
    repr (allocate_id (N.succ_pos (ids db)) db) i = i.
  Proof.
    intros db k Hwf i Hin. rewrite (allocate_next_repr db Hwf i).
    apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    - exact (canon_key_fixed db k Hwf i Hin).
    - cbn [option_list In] in Hin. destruct Hin as [Heq | Hfalse]; [| contradiction].
      injection Heq as <-. apply UnionFindCodeFacts.repr_absent. now apply allocate_next_absent.
  Qed.

  (** The common row-update obligation used by put and fresh constructor allocation. *)
  Definition replacement_preserves_wf : Prop :=
    forall db f k previous o, wf db -> old db f k = previous -> kind_ok db f k o ->
    (forall i, In (Id i) (k ++ option_list o) -> repr db i = i) ->
    wf (row_replace f k previous o db).

  (** Every non-reuse make branch follows from fresh allocation and the common row update. *)
  Lemma wf_make_fresh_from_replacement : replacement_preserves_wf ->
    forall db f k previous, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    old db f (map (canon db) k) = previous ->
    wf (match kind_get f db with
      | Some OId => row_replace f (map (canon db) k) previous
          (Some (Id (N.succ_pos (ids db)))) (allocate_id (N.succ_pos (ids db)) db)
      | _ => allocate_id (N.succ_pos (ids db)) db
      end).
  Proof.
    intros Hreplace db f k previous Hwf Hargs Hfits Hprevious.
    destruct (kind_get f db) as [[| |m] |] eqn:Hkind; try now apply wf_allocate_next.
    apply Hreplace.
    - now apply wf_allocate_next.
    - exact Hprevious.
    - apply fresh_constructor_kind_ok; assumption.
    - apply fresh_constructor_canonical. exact Hwf.
  Qed.

  (** Constructor well-formedness reduces to the proved allocation and one row replacement. *)
  Lemma wf_make_from_replacement : replacement_preserves_wf ->
    forall f k db, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    wf (snd (make f k db)).
  Proof.
    intros Hreplace f k db Hwf Hargs Hfits. unfold make.
    rewrite (normal_key_correct db k Hwf). fold (ids db).
    destruct (row_get f (map (canon db) k) db) as [[[j | v] |] |] eqn:Hprevious;
      cbn [snd]; [exact Hwf | | |];
      apply wf_make_fresh_from_replacement; assumption.
  Qed.

  (** Replacing one value output by another preserves kind and all identifier obligations. *)
  Lemma kind_ok_value_replace : forall db f k a b,
    kind_ok db f k (Some (Val a)) -> kind_ok db f k (Some (Val b)).
  Proof.
    intros db f k a b [Hids [Hfits Hkind]]. unfold kind_ok. split.
    - intros i Hin. apply Hids. apply in_app_iff in Hin. apply in_app_iff.
      destruct Hin as [Hin | Hin]; [now left |].
      cbn [option_list In] in Hin. destruct Hin as [Hfalse | Hfalse];
        [discriminate Hfalse | contradiction].
    - split.
      + rewrite length_app in Hfits |- *. exact Hfits.
      + exact Hkind.
  Qed.

  (** Normalized keys and normalized optional outputs form a canonical row. *)
  Lemma canon_row_fixed : forall db k o, wf db ->
    forall i, In (Id i) (map (canon db) k ++ option_list (option_map (canon db) o)) ->
    repr db i = i.
  Proof.
    intros db k o Hwf i Hin. rewrite <- canon_row_tuple in Hin.
    exact (canon_key_fixed db (k ++ option_list o) Hwf i Hin).
  Qed.

  (** Put uses only a justified union, an unchanged state or one canonical row replacement. *)
  Lemma wf_put_from_replacement : replacement_preserves_wf ->
    forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Proof.
    intros Hreplace f k o db Hwf Hkind.
    pose proof (kind_ok_canon db f k o Hwf Hkind) as Hnormal.
    unfold put. rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    rewrite combine_output_correct. fold (old db f (map (canon db) k)).
    destruct (old db f (map (canon db) k)) as [before |] eqn:Hprevious.
    - pose proof (wf_row_kind db Hwf f (map (canon db) k) before Hprevious) as Hbefore.
      destruct Hkind as [Hids [Hfits Hshape]].
      destruct (kind (view db) f) as [[| |m] |] eqn:Hdecl in Hshape, Hbefore;
        destruct o as [[i | v] |]; destruct before as [[j | w] |];
        cbn in Hshape, Hbefore; try contradiction.
      + cbn [combine option_map canon]. rewrite output_eqb_refl. exact Hwf.
      + cbn [combine option_map canon]. rewrite output_eqb_refl.
        apply wf_union; [exact Hwf | |].
        * eapply wf_row_ids; [exact Hwf | exact Hprevious |].
          apply in_app_iff. right. cbn [option_list In]. now left.
        * apply repr_allocated; [exact Hwf |]. apply Hids.
          apply in_app_iff. right. cbn [option_list In]. now left.
      + cbn [combine option_map canon]. rewrite Hdecl.
        destruct (output_eqb (Some (Val w)) (Some (Val (V.merge m w v)))); [exact Hwf |].
        apply Hreplace.
        * exact Hwf.
        * exact Hprevious.
        * exact (kind_ok_value_replace db f (map (canon db) k) v (V.merge m w v) Hnormal).
        * exact (canon_row_fixed db k (Some (Val (V.merge m w v))) Hwf).
    - cbn [combine]. apply Hreplace.
      + exact Hwf.
      + exact Hprevious.
      + exact Hnormal.
      + exact (canon_row_fixed db k o Hwf).
  Qed.

  (** Exact projection multiplicities complete well-formed canonical row replacement. *)
  Lemma row_replace_wf : replacement_preserves_wf.
  Proof.
    intros db f k previous o Hwf Hprevious Hkind Hcanonical.
    destruct (row_replace_cache_correct db f k previous o Hwf Hprevious
      (proj1 (proj2 Hkind))) as [Hsound [Hcomplete [Harity Hcounts]]].
    apply row_replace_wf_from_caches; assumption.
  Qed.

  (** Kind-correct insertion keeps the database well formed. *)
  Lemma wf_put : forall f k o db, wf db -> kind_ok db f k o -> wf (put f k o db).
  Proof.
    exact (wf_put_from_replacement row_replace_wf).
  Qed.

  (** Constructor allocation keeps the database well formed. *)
  Lemma wf_make : forall f k db, wf db ->
    (forall j, In (Id j) k -> allocated db j) -> slots_fit db f (S (length k)) ->
    wf (snd (make f k db)).
  Proof.
    exact (wf_make_from_replacement row_replace_wf).
  Qed.

  (** Erasing a row removes precisely its selected table binding. *)
  Lemma row_erase_binding : forall f k db g args output,
    row (view (row_erase f k db)) g args output <->
      row (view db) g args output /\ (g, args) <> (f, k).
  Proof.
    intros f k db g args output.
    change (RowMap.get (g, args) (RowMap.remove (f, k) (runtime_rows (db_runtime db))) =
      Some output <-> RowMap.get (g, args) (runtime_rows (db_runtime db)) = Some output /\
        (g, args) <> (f, k)).
    apply RowFacts.remove_binding_iff.
  Qed.

  (** Cache maintenance and table deletion preserve all unrelated runtime observations. *)
  Lemma row_delete_preserves : forall (A : Type)
      (observe : database_runtime (cell V.t) I.t -> A),
    (forall rows state, observe (runtime_set_rows rows state) = observe state) ->
    (forall all new counts state,
      observe (runtime_set_indexes all new counts state) = observe state) ->
    forall f k db, observe (db_runtime (row_delete f k db)) = observe (db_runtime db).
  Proof.
    intros A observe Hrows Hindexes f k db. unfold row_delete.
    destruct (row_get f k db); [| reflexivity].
    unfold row_erase. cbn [database_set_runtime db_runtime]. rewrite Hrows.
    now apply slots_update_preserves.
  Qed.

  (** Deleting a row keeps every function declaration exactly unchanged. *)
  Lemma row_delete_kind : forall f k db, kind (view (row_delete f k db)) = kind (view db).
  Proof.
    intros f k db. unfold view, kind_get. cbn [kind].
    rewrite (row_delete_preserves _ (@runtime_kinds (cell V.t) I.t)
      (fun rows state => eq_refl) (fun all new counts state => eq_refl) f k db).
    reflexivity.
  Qed.

  (** Deleting a row keeps the stored equality relation exactly unchanged. *)
  Lemma row_delete_same : forall f k db, same (view (row_delete f k db)) = same (view db).
  Proof.
    intros f k db. unfold view. cbn [same].
    rewrite (row_delete_preserves _ (@runtime_equalities (cell V.t) I.t)
      (fun rows state => eq_refl) (fun all new counts state => eq_refl) f k db).
    reflexivity.
  Qed.

  (** Deletion removes one row key and retains all other rows, even before rebuilding. *)
  Lemma row_delete_binding : forall f k db g args output,
    row (view (row_delete f k db)) g args output <->
      row (view db) g args output /\ (g, args) <> (f, k).
  Proof.
    intros f k db g args output. unfold row_delete.
    destruct (row_get f k db) as [before |] eqn:Hprevious.
    - now rewrite row_erase_binding, slots_update_view.
    - split; [| tauto]. intro Hrow. split; [exact Hrow |].
      intro Hequal. inversion Hequal; subst.
      change (row_get f k db = Some output) in Hrow. congruence.
  Qed.

  (** Deleting a contribution retains the complete preexisting write history. *)
  Lemma row_delete_written : forall db f k,
    incl (db_written_cells db) (db_written_cells (row_delete f k db)).
  Proof.
    intros db f k c Hin. unfold row_delete.
    destruct (row_get f k db) as [before |]; [| exact Hin].
    change (In c (db_written_cells (slots_update false f (k ++ option_list before) db))).
    rewrite slots_update_written_cells. apply in_or_app. now right.
  Qed.

  (** Deletion only retains rows whose cells were already recorded. *)
  Lemma row_delete_recorded_rows : forall db f k, recorded_rows db ->
    recorded_rows (row_delete f k db).
  Proof.
    intros db f k Hrecorded.
    eapply recorded_rows_transport; [| apply row_delete_written | exact Hrecorded].
    intros g args output Hrow. now apply row_delete_binding in Hrow as [Hrow _].
  Qed.

  (** Deletion preserves the complete row and cache history invariant. *)
  Lemma database_history_row_delete : forall db f k, database_history db ->
    database_history (row_delete f k db).
  Proof.
    intros db f k [Hmetadata Hrows]. split.
    - now apply metadata_row_delete.
    - now apply row_delete_recorded_rows.
  Qed.

  (** Removing a stored row preserves every satisfying interpretation without a quietness premise. *)
  Lemma row_delete_sat : forall (M : model (V := V.t)) nu f k db,
    sat V.merge M nu (view db) -> sat V.merge M nu (view (row_delete f k db)).
  Proof.
    intros M nu f k db Hsat. eapply sat_restrict; [apply row_delete_kind | | | exact Hsat].
    - intros g args output Hrow. now apply row_delete_binding in Hrow as [Hrow _].
    - intros i j Hsame. now rewrite row_delete_same in Hsame.
  Qed.

  (** Deleting a row never modifies identifier representatives. *)
  Lemma row_delete_forest : forall f k db,
    db_forest (row_delete f k db) = db_forest db.
  Proof.
    intros f k db. unfold row_delete. destruct (row_get f k db) as [o |]; [| reflexivity].
    change (db_forest (slots_update false f (k ++ option_list o) db) = db_forest db).
    apply slots_update_forest.
  Qed.

  (** Deletion retains the allocation interval, slot declarations and pending queue. *)
  Lemma row_delete_ids : forall f k db, ids (row_delete f k db) = ids db.
  Proof.
    intros f k db. apply row_delete_preserves; intros; reflexivity.
  Qed.

  Lemma row_delete_slots : forall f k db, slots (row_delete f k db) = slots db.
  Proof.
    intros f k db. apply row_delete_preserves; intros; reflexivity.
  Qed.

  Lemma row_delete_pending : forall f k db, pending (row_delete f k db) = pending db.
  Proof.
    intros f k db. exact (row_delete_preserves _ (fun state => length (runtime_queue state))
      (fun rows state => eq_refl) (fun all new counts state => eq_refl) f k db).
  Qed.

  Lemma row_delete_npending : forall f k db,
    db_npending (row_delete f k db) = db_npending db.
  Proof.
    intros f k db. unfold row_delete. destruct (row_get f k db) as [o |]; [| reflexivity].
    change (db_npending (slots_update false f (k ++ option_list o) db) = db_npending db).
    apply slots_update_npending.
  Qed.

  (** Deleting the obsolete binding does not reset an already-raised change flag. *)
  Lemma row_delete_changed : forall f k db, changed (row_delete f k db) = changed db.
  Proof.
    intros f k db. apply row_delete_preserves; intros; reflexivity.
  Qed.

  (** A present deletion uses the finite-map removal of precisely the selected row key. *)
  Lemma row_delete_map_present : forall f k db o, row_get f k db = Some o ->
    runtime_rows (db_runtime (row_delete f k db)) =
      RowMap.remove (f, k) (runtime_rows (db_runtime db)).
  Proof.
    intros f k db o Hrow. unfold row_delete. rewrite Hrow. unfold row_erase.
    cbn [database_set_runtime db_runtime runtime_set_rows runtime_rows].
    rewrite (slots_update_preserves _ (@runtime_rows (cell V.t) I.t)
      (fun all new counts state => eq_refl)). reflexivity.
  Qed.

  (** Erasing a binding leaves every previously updated slot cache intact. *)
  Lemma row_erase_slot_snapshot : forall db f k s,
    slot_snapshot (db_runtime (row_erase f k db)) s = slot_snapshot (db_runtime db) s.
  Proof.
    reflexivity.
  Qed.

  (** Actual row deletion preserves exact projection multiplicities and both index caches. *)
  Lemma row_delete_cache_correct : forall db f k,
    wf db -> database_cache_correct (row_delete f k db).
  Proof.
    intros db f k Hwf. destruct (row_get f k db) as [o |] eqn:Hrow.
    - pose proof (row_delete_map_present f k db o Hrow) as Hmap.
      assert (Hbound : runtime_slot_bound (db_runtime (row_delete f k db)) =
        runtime_slot_bound (db_runtime db)).
      { apply row_delete_preserves; intros; reflexivity. }
      apply (database_cache_correct_from_slots (row_delete f k db)).
      + refine (eq_ind_r (fun rows => RowMap.wf rows) _ Hmap).
        apply RowMap.wf_remove. exact (wf_row_map db Hwf).
      + exact (eq_trans Hbound (eq_trans (wf_slot_bound db Hwf)
          (eq_sym (f_equal (fun sl => N.of_nat (length sl)) (row_delete_slots f k db))))).
      + intros s g perm Hslot. unfold slot_of in Hslot. rewrite row_delete_slots in Hslot.
        fold (slot_of db s) in Hslot.
        pose proof (RowFacts.remove_elements_decomposition _
          (runtime_rows (db_runtime db)) (f, k) (Some o) (wf_row_map db Hwf) Hrow) as Hrows.
        cbn [option_list option_map app] in Hrows.
        pose proof (wf_slot_cache db s g perm Hwf Hslot) as Hcache.
        pose proof (slot_cache_permutation (db_runtime db) s (length perm) _ _
          (row_contributions_permutation g perm _ _ Hrows) Hcache) as Hordered.
        refine (eq_ind_r (fun rows => slot_cache_ok (db_runtime (row_delete f k db))
          s (length perm) (row_contributions g perm (RowMap.elements rows))) _ Hmap).
        unfold row_delete. rewrite Hrow.
        eapply slot_cache_snapshot; [apply row_erase_slot_snapshot |].
        apply slots_update_cache_row_remove; try assumption.
        * exact (wf_group_table db Hwf).
        * exact (wf_row_slots db Hwf f k o Hrow).
    - unfold row_delete. rewrite Hrow. unfold database_cache_correct.
      repeat split.
      + exact (wf_index_sound db Hwf).
      + exact (wf_index_complete db Hwf).
      + exact (wf_index_arity db Hwf).
      + exact (wf_projection_counts db Hwf).
  Qed.

  (** Removing a stored row preserves every structural and multiset-cache invariant. *)
  Lemma row_delete_wf : forall db f k, wf db -> wf (row_delete f k db).
  Proof.
    intros db f k Hwf.
    assert (Hruntime :
      (runtime_equalities (db_runtime (row_delete f k db)),
       runtime_queue (db_runtime (row_delete f k db)),
       runtime_function_slots (db_runtime (row_delete f k db)),
       runtime_max_name (db_runtime (row_delete f k db)),
       runtime_slot_bound (db_runtime (row_delete f k db))) =
      (runtime_equalities (db_runtime db), runtime_queue (db_runtime db),
       runtime_function_slots (db_runtime db), runtime_max_name (db_runtime db),
       runtime_slot_bound (db_runtime db))).
    { exact (row_delete_preserves _
        (fun state => (runtime_equalities state, runtime_queue state,
          runtime_function_slots state, runtime_max_name state, runtime_slot_bound state))
        (fun rows state => eq_refl) (fun all new counts state => eq_refl) f k db). }
    injection Hruntime as Hlog Hqueue Hgroups Hmax Hbound.
    change (runtime_equalities (db_runtime (row_delete f k db)) =
      runtime_equalities (db_runtime db)) in Hlog.
    change (runtime_queue (db_runtime (row_delete f k db)) =
      runtime_queue (db_runtime db)) in Hqueue.
    change (runtime_function_slots (db_runtime (row_delete f k db)) =
      runtime_function_slots (db_runtime db)) in Hgroups.
    change (runtime_max_name (db_runtime (row_delete f k db)) =
      runtime_max_name (db_runtime db)) in Hmax.
    change (runtime_slot_bound (db_runtime (row_delete f k db)) =
      runtime_slot_bound (db_runtime db)) in Hbound.
    assert (Hsource : forall g args output, row (view (row_delete f k db)) g args output ->
      row (view db) g args output).
    { intros g args output Hrow. now apply row_delete_binding in Hrow as [Hrow _]. }
    assert (Hmap : RowMap.wf (runtime_rows (db_runtime (row_delete f k db)))).
    { destruct (row_get f k db) as [o |] eqn:Hrow.
      - refine (eq_ind_r (fun rows => RowMap.wf rows) _
          (row_delete_map_present f k db o Hrow)). apply RowMap.wf_remove.
        exact (wf_row_map db Hwf).
      - unfold row_delete. rewrite Hrow. exact (wf_row_map db Hwf). }
    destruct (row_delete_cache_correct db f k Hwf) as [Hsound [Hcomplete [Harity Hcounts]]].
    unfold wf, database_wf. split.
    { rewrite row_delete_forest. exact (wf_forest db Hwf). }
    split.
    { intro i. rewrite row_delete_forest. unfold allocated. rewrite row_delete_ids.
      exact (wf_forest_members db Hwf i). }
    split.
    { rewrite row_delete_forest, row_delete_ids. exact (wf_forest_count db Hwf). }
    split.
    { rewrite row_delete_forest, row_delete_ids. exact (wf_forest_width db Hwf). }
    split.
    { intros i j. rewrite row_delete_same. unfold repr. rewrite row_delete_forest.
      exact (wf_equalities db Hwf i j). }
    split.
    { rewrite Hlog. unfold allocated. rewrite row_delete_ids. exact (wf_log_allocated db Hwf). }
    split; [exact Hmap |]. split.
    { intros g args output Hrow. rewrite row_delete_kind.
      exact (wf_row_kind db Hwf g args output (Hsource g args output Hrow)). }
    split.
    { intros g args output i Hrow Hin. unfold allocated. rewrite row_delete_ids.
      exact (wf_row_ids db Hwf g args output i (Hsource g args output Hrow) Hin). }
    split.
    { intros g args output Hrow. unfold slots_fit. rewrite row_delete_slots.
      exact (wf_row_slots db Hwf g args output (Hsource g args output Hrow)). }
    split.
    { intros g output Houtput. rewrite row_delete_kind in Houtput. rewrite Hmax.
      exact (wf_kind_bound db Hwf g output Houtput). }
    split.
    { rewrite Hbound, row_delete_slots. exact (wf_slot_bound db Hwf). }
    split.
    { rewrite row_delete_npending, row_delete_pending. exact (wf_pending_count db Hwf). }
    split.
    { rewrite Hqueue. unfold allocated. rewrite row_delete_ids. exact (wf_queue_allocated db Hwf). }
    split.
    { intros Hquiet g args output Hrow i Hin. unfold repr. rewrite row_delete_forest.
      rewrite row_delete_pending in Hquiet.
      exact (wf_quiet_canonical db Hwf Hquiet g args output (Hsource g args output Hrow) i Hin). }
    split; [exact Hsound |]. split; [exact Hcomplete |]. split; [exact Harity |].
    split; [rewrite Hgroups, row_delete_slots; exact (wf_group_table db Hwf) |].
    split; [exact Hcounts |]. split.
    { rewrite Hmax, row_delete_kind. exact (wf_max_name_attained db Hwf). }
    apply database_history_row_delete. exact (wf_history db Hwf).
  Qed.

  (** Conflict resolution preserves declarations even during an active repair batch. *)
  Lemma output_conflict_kind_raw : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)),
    kind (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) = kind (view db).
  Proof.
    intros db previous co.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |]; try reflexivity.
    unfold union. destruct (UnionFindCode.union a b (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Conflict resolution changes no rows, independently of queue coverage. *)
  Lemma output_conflict_rows_raw : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)),
    row (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) = row (view db).
  Proof.
    intros db previous co.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |]; try reflexivity.
    unfold union. destruct (UnionFindCode.union a b (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Every newly logged equality comes from the actual two conflicting outputs. *)
  Lemma output_conflict_same_sources_raw : forall db
      (previous : option (option (cell V.t))) (co : option (cell V.t)) i j,
    same (view (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db
      | _, _ => db
      end)) i j ->
    clos_refl_sym_trans positive
      (fun x y => same (view db) x y \/
        (previous = Some (Some (Id x)) /\ co = Some (Id y))) i j.
  Proof.
    intros db previous co i j Hsame.
    destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
      try solve [apply rst_step; now left].
    unfold union in Hsame.
    destruct (UnionFindCode.union a b (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |].
    - apply (proj1 (equality_log_cons a b (runtime_equalities (db_runtime db)) i j)) in Hsame.
      eapply equality_closure_mono; [| exact Hsame].
      intros x y [Hold | Hpair]; [now left |].
      right. injection Hpair as -> ->. split; reflexivity.
    - apply rst_step. now left.
  Qed.

  (** Put preserves declarations without requiring a quiet public database invariant. *)
  Lemma put_kind_raw : forall db f k o, kind (view (put f k o db)) = kind (view db).
  Proof.
    intros db f k o. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hkind : kind (view next) = kind (view db)) by apply output_conflict_kind_raw.
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hkind |]. now rewrite row_replace_kind.
    - now rewrite row_replace_kind.
  Qed.

  (** The executed normalizers determine the only row that a put can add. *)
  Lemma put_row_sources_raw : forall db f k o g args output,
    row (view (put f k o db)) g args output ->
      row (view db) g args output \/
      (g = f /\ args = normal_key db k /\
        output = combine_output db f (row_get f (normal_key db k) db)
          (option_map (normal_cell db) o)).
  Proof.
    intros db f k o g args output. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hrows : row (view next) = row (view db)) by apply output_conflict_rows_raw.
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

  (** Put logs only old equalities and conflicts at its actually normalized key. *)
  Lemma put_same_sources_raw : forall db f k o i j,
    same (view (put f k o db)) i j ->
    clos_refl_sym_trans positive
      (fun x y => same (view db) x y \/
        (row_get f (normal_key db k) db = Some (Some (Id x)) /\
          option_map (normal_cell db) o = Some (Id y))) i j.
  Proof.
    intros db f k o i j. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hsame : forall a b, same (view next) a b ->
      clos_refl_sym_trans positive
        (fun x y => same (view db) x y \/
          (previous = Some (Some (Id x)) /\ co = Some (Id y))) a b).
    { apply output_conflict_same_sources_raw. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [apply Hsame |].
      rewrite row_replace_same. apply Hsame.
    - rewrite row_replace_same. apply Hsame.
  Qed.

  (** Put is semantically sound whenever its actual normalization preserves meaning. *)
  Lemma put_sat_normal_meaning : forall (M : model (V := V.t)) nu db f k o,
    sat V.merge M nu (view db) ->
    (forall c, den nu (normal_cell db c) = den nu c) ->
    holds M nu (view db) f k o -> sat V.merge M nu (view (put f k o db)).
  Proof.
    intros M nu db f k o Hsat Hnormal Hholds.
    eapply (@sat_put_view V.t V.merge M nu (view db) (view (put f k o db)) f k o
      (normal_key db k) (option_map (normal_cell db) o) (row_get f (normal_key db k) db)).
    - exact Hsat.
    - apply put_kind_raw.
    - intros before Hprevious. exact Hprevious.
    - unfold normal_key. rewrite map_map. apply map_ext. exact Hnormal.
    - destruct o as [c |]; cbn [option_map]; [now rewrite Hnormal | reflexivity].
    - exact Hholds.
    - apply put_row_sources_raw.
    - apply put_same_sources_raw.
  Qed.

  (** The semantic loop needs only a valid forest whose representatives keep their meaning. *)
  Definition model_forest (M : model (V := V.t)) (nu : positive -> carrier M) (db : t) : Prop :=
    UnionFind.wf (db_forest db) /\ forall i, nu (repr db i) = nu i.

  (** A satisfying public database starts with the weaker semantic forest invariant. *)
  Lemma model_forest_initial : forall M nu db,
    wf db -> sat V.merge M nu (view db) -> model_forest M nu db.
  Proof.
    intros M nu db Hwf Hsat. split; [exact (wf_forest db Hwf) |].
    intro i. pose proof (canon_den M nu db Hwf Hsat (Id i)) as Hden.
    now injection Hden.
  Qed.

  (** The actual find-based cell normalizer preserves denotations under the semantic invariant. *)
  Lemma model_forest_normal : forall M nu db, model_forest M nu db ->
    forall c, den nu (normal_cell db c) = den nu c.
  Proof.
    intros M nu db [Hforest Hmeaning] [i | v]; cbn [normal_cell den]; [| reflexivity].
    destruct (N.compare (runtime_allocated (db_runtime db)) (Npos i)); try reflexivity;
      rewrite (UnionFind.find_repr i (db_forest db) Hforest); cbn [den];
      f_equal; exact (Hmeaning i).
  Qed.

  (** Row and scheduling updates that retain the forest also retain its interpretation. *)
  Lemma model_forest_unchanged : forall M nu db db',
    db_forest db' = db_forest db -> model_forest M nu db -> model_forest M nu db'.
  Proof.
    intros M nu db db' Hequal. unfold model_forest, repr. now rewrite Hequal.
  Qed.

  (** Linking identifiers with equal interpretations preserves representative meanings. *)
  Lemma model_forest_union : forall M nu db i j,
    model_forest M nu db -> nu i = nu j -> model_forest M nu (union i j db).
  Proof.
    intros M nu db i j [Hforest Hmeaning] Hequal. split.
    - rewrite union_forest. now apply UnionFind.wf_union.
    - intro x. unfold repr in Hmeaning |- *. rewrite union_forest.
      destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
      destruct roots as [[winner loser] |]; cbn [snd].
      + destruct (UnionFind.union_some i j (db_forest db) winner loser forest Hforest Hunion)
          as [_ [Hroots Hrepr]].
        assert (Hjoined : nu winner = nu loser).
        { destruct Hroots as [[-> ->] | [-> ->]]; rewrite !Hmeaning; congruence. }
        rewrite (Hrepr x). destruct (Pos.eqb (UnionFind.repr (db_forest db) x) loser) eqn:Hloser.
        * apply Pos.eqb_eq in Hloser. rewrite Hjoined, <- Hloser. exact (Hmeaning x).
        * exact (Hmeaning x).
      + rewrite (proj2 (UnionFind.union_none i j (db_forest db) forest Hforest Hunion) x).
        exact (Hmeaning x).
  Qed.

  (** A true row supplies equal meanings for every constructor conflict raised by put. *)
  Lemma put_model_forest : forall M nu db f k o,
    model_forest M nu db -> sat V.merge M nu (view db) -> holds M nu (view db) f k o ->
    model_forest M nu (put f k o db).
  Proof.
    intros M nu db f k o Hmodel Hsat Hholds.
    pose proof (model_forest_normal M nu db Hmodel) as Hnormal.
    set (ck := normal_key db k).
    set (co := option_map (normal_cell db) o).
    set (previous := row_get f ck db).
    assert (Hcanonical : holds M nu (view db) f ck co).
    { eapply (@holds_transport V.t M nu nu (view db) (view db) f k ck o co).
      - reflexivity.
      - unfold ck, normal_key. rewrite map_map. apply map_ext. exact Hnormal.
      - unfold co. destruct o as [c |]; cbn [option_map]; [now rewrite Hnormal | reflexivity].
      - exact Hholds. }
    assert (Hprevious : forall before, previous = Some before -> holds M nu (view db) f ck before).
    { intros before Hlookup. exact (proj1 Hsat f ck before Hlookup). }
    assert (Hnext : model_forest M nu (match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end)).
    { destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |]; try exact Hmodel.
      apply model_forest_union; [exact Hmodel |].
      pose proof (Hprevious (Some (Id a)) eq_refl) as Hold.
      unfold holds in Hold, Hcanonical.
      destruct (kind (view db) f) as [[| |m] |]; try contradiction; congruence. }
    unfold put. fold ck co previous.
    set (updated := combine_output db f previous co).
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hnext |].
      eapply model_forest_unchanged; [apply row_replace_forest | exact Hnext].
    - eapply model_forest_unchanged; [apply row_replace_forest | exact Hnext].
  Qed.

  (** The removed source still justifies its normalized row in the restricted view. *)
  Lemma deleted_normal_row_holds : forall M nu db f k o,
    model_forest M nu db -> sat V.merge M nu (view db) -> row (view db) f k o ->
    holds M nu (view (row_delete f k db)) f
      (normal_key db k) (option_map (normal_cell db) o).
  Proof.
    intros M nu db f k o Hmodel Hsat Hrow.
    pose proof (model_forest_normal M nu db Hmodel) as Hnormal.
    eapply (@holds_transport V.t M nu nu (view db) (view (row_delete f k db)) f k
      (normal_key db k) o (option_map (normal_cell db) o)).
    - now rewrite row_delete_kind.
    - unfold normal_key. rewrite map_map. apply map_ext. exact Hnormal.
    - destruct o as [c |]; cbn [option_map]; [now rewrite Hnormal | reflexivity].
    - exact (proj1 Hsat f k o Hrow).
  Qed.

  (** Actual row repair preserves both satisfaction and the invariant needed by the next repair. *)
  Lemma repair_current_semantic : forall M nu db f k,
    model_forest M nu db -> sat V.merge M nu (view db) ->
    model_forest M nu (repair_current f k db) /\
      sat V.merge M nu (view (repair_current f k db)).
  Proof.
    intros M nu db f k Hmodel Hsat. unfold repair_current.
    destruct (row_get f k db) as [o |] eqn:Hrow; [| now split].
    destruct (andb (Pos.eqb (db_tuple_code (normal_key db k)) (db_tuple_code k))
      (output_eqb (option_map (normal_cell db) o) o)); [now split |].
    assert (Hdeleted : model_forest M nu (row_delete f k db)).
    { eapply model_forest_unchanged; [apply row_delete_forest | exact Hmodel]. }
    pose proof (row_delete_sat M nu f k db Hsat) as Hrestricted.
    pose proof (deleted_normal_row_holds M nu db f k o Hmodel Hsat Hrow) as Hholds.
    split.
    - now apply put_model_forest.
    - apply put_sat_normal_meaning; [exact Hrestricted | | exact Hholds].
      now apply model_forest_normal.
  Qed.

  (** Queue removal changes neither rows, equality evidence, kinds nor the forest. *)
  Lemma db_pop_loser_preserves : forall db i db', db_pop_loser db = Some (i, db') ->
    db_forest db' = db_forest db /\ view db' = view db.
  Proof.
    intros db i db' Hpop. unfold db_pop_loser in Hpop.
    destruct (runtime_queue (db_runtime db)) as [| j rest]; [discriminate |].
    injection Hpop as Hname Hdb. subst i db'. split; reflexivity.
  Qed.

  (** Every continuing callback preserves the weaker semantic invariant. *)
  Lemma db_rstep_semantic_continue : forall M nu s s',
    model_forest M nu (fst s) /\ sat V.merge M nu (view (fst s)) ->
    db_rstep s = inl s' ->
    model_forest M nu (fst s') /\ sat V.merge M nu (view (fst s')).
  Proof.
    intros M nu [db work] s' [Hmodel Hsat] Hstep.
    destruct work as [| [f k] rest]; cbn [db_rstep fst snd] in Hstep.
    - destruct (db_pop_loser db) as [[i db'] |] eqn:Hpop; [| discriminate].
      injection Hstep as Hnext. subst s'. cbn [fst].
      destruct (db_pop_loser_preserves db i db' Hpop) as [Hforest Hview].
      split; [eapply model_forest_unchanged; eassumption | now rewrite Hview].
    - injection Hstep as Hnext. subst s'. cbn [fst].
      now apply repair_current_semantic.
  Qed.

  (** A stopped callback returns the database whose semantic invariant it carries. *)
  Lemma db_rstep_semantic_stop : forall M nu s db',
    model_forest M nu (fst s) /\ sat V.merge M nu (view (fst s)) ->
    db_rstep s = inr db' -> model_forest M nu db' /\ sat V.merge M nu (view db').
  Proof.
    intros M nu [db work] db' Hsemantic Hstep.
    destruct work as [| [f k] rest]; cbn [db_rstep fst snd] in Hstep; [| discriminate].
    destruct (db_pop_loser db) as [[i next] |]; [discriminate |].
    injection Hstep as Hnext. now subst db'.
  Qed.

  (** Rebuilding keeps every satisfying model and identifier interpretation. *)
  Lemma rebuild_sat : forall (M : model (V := V.t)) nu db, wf db ->
    sat V.merge M nu (view db) -> sat V.merge M nu (view (rebuild db)).
  Proof.
    intros M nu db Hwf Hsat.
    pose proof (LoopNFacts.loopN_preserves _ _ db_rstep
      (fun s => model_forest M nu (fst s) /\ sat V.merge M nu (view (fst s)))
      (fun result => model_forest M nu result /\ sat V.merge M nu (view result))
      (db_rstep_semantic_continue M nu) (db_rstep_semantic_stop M nu)
      (db_rebuild_fuel db) (db, [])
      (conj (model_forest_initial M nu db Hwf Hsat) Hsat)) as Hloop.
    unfold rebuild.
    destruct (loopN db_rstep (db_rebuild_fuel db) (db, [])) as [s | result];
      exact (proj2 Hloop).
  Qed.

  (** A stale work entry with no current row is discarded without any state update. *)
  Lemma repair_current_absent : forall db f k,
    row_get f k db = None -> repair_current f k db = db.
  Proof.
    intros db f k Habsent. unfold repair_current. now rewrite Habsent.
  Qed.

  (** A row already equal to its normal form takes the unchanged-state branch. *)
  Lemma repair_current_fixed : forall db f k o,
    row_get f k db = Some o -> normal_key db k = k ->
    option_map (normal_cell db) o = o -> repair_current f k db = db.
  Proof.
    intros db f k o Hrow Hkey Houtput. unfold repair_current.
    now rewrite Hrow, Hkey, Houtput, Pos.eqb_refl, output_eqb_refl.
  Qed.

  (** Every repair retains a change flag raised before it began. *)
  Lemma repair_current_changed : forall db f k,
    changed db = true -> changed (repair_current f k db) = true.
  Proof.
    intros db f k Hchanged. unfold repair_current.
    destruct (row_get f k db) as [o |]; [| exact Hchanged].
    destruct (andb (Pos.eqb (db_tuple_code (normal_key db k)) (db_tuple_code k))
      (output_eqb (option_map (normal_cell db) o) o)); [exact Hchanged |].
    apply changed_put. now rewrite row_delete_changed.
  Qed.

  (** Every property preserved by both actual callback branches survives the fuelled loop. *)
  Lemma rebuild_preserves : forall (P : t -> Prop),
    (forall db f k, P db -> P (repair_current f k db)) ->
    (forall db i db', P db -> db_pop_loser db = Some (i, db') -> P db') ->
    forall db, P db -> P (rebuild db).
  Proof.
    intros P Hrepair Hpop db Hinitial.
    assert (Hstep : forall s, P (fst s) ->
      match db_rstep s with inl next => P (fst next) | inr result => P result end).
    { intros [current work] Hcurrent.
      destruct work as [| [f k] rest]; cbn [db_rstep fst snd].
      - destruct (db_pop_loser current) as [[i next] |] eqn:Hqueue;
          [eapply Hpop; eassumption | exact Hcurrent].
      - now apply Hrepair. }
    assert (Hcontinue : forall s s', P (fst s) -> db_rstep s = inl s' -> P (fst s')).
    { intros s s' Hcurrent Hgo. specialize (Hstep s Hcurrent). now rewrite Hgo in Hstep. }
    assert (Hstop : forall s result, P (fst s) -> db_rstep s = inr result -> P result).
    { intros s result Hcurrent Hdone. specialize (Hstep s Hcurrent). now rewrite Hdone in Hstep. }
    pose proof (LoopNFacts.loopN_preserves _ _ db_rstep (fun s => P (fst s)) P
      Hcontinue Hstop (db_rebuild_fuel db) (db, []) Hinitial) as Hloop.
    unfold rebuild. destruct (loopN db_rstep (db_rebuild_fuel db) (db, [])); exact Hloop.
  Qed.

  (** Queue scheduling retains layout, allocation and the current change flag. *)
  Lemma db_pop_loser_layout : forall db i db', db_pop_loser db = Some (i, db') ->
    slots db' = slots db /\ ids db' = ids db /\ changed db' = changed db.
  Proof.
    intros db i db' Hpop. unfold db_pop_loser in Hpop.
    destruct (runtime_queue (db_runtime db)) as [| j rest]; [discriminate |].
    injection Hpop as Hname Hdb. subst i db'. repeat split; reflexivity.
  Qed.

  (** A raised change flag stays raised through every repair and queue operation. *)
  Lemma changed_rebuild : forall db, changed db = true -> changed (rebuild db) = true.
  Proof.
    apply (rebuild_preserves (fun db => changed db = true)).
    - exact repair_current_changed.
    - intros db i db' Hchanged Hpop.
      rewrite (proj2 (proj2 (db_pop_loser_layout db i db' Hpop))). exact Hchanged.
  Qed.

  (** Put preserves declarations, slots and allocation even in an active repair batch. *)
  Lemma put_layout_raw : forall db f k o,
    kind (view (put f k o db)) = kind (view db) /\
    slots (put f k o db) = slots db /\ ids (put f k o db) = ids db.
  Proof.
    intros db f k o. split; [apply put_kind_raw |]. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hnext : slots next = slots db /\ ids next = ids db).
    { unfold next. destruct previous as [[[a | v] |] |];
        destruct co as [[b | w] |]; try (split; reflexivity).
      unfold union. destruct (UnionFindCode.union a b (db_forest db)) as [roots forest].
      destruct roots as [[winner loser] |]; split; reflexivity. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hnext |].
      now rewrite row_replace_slots, row_replace_ids.
    - now rewrite row_replace_slots, row_replace_ids.
  Qed.

  (** Single-row repair keeps all public layout observations. *)
  Lemma repair_current_layout : forall db f k,
    kind (view (repair_current f k db)) = kind (view db) /\
    slots (repair_current f k db) = slots db /\ ids (repair_current f k db) = ids db.
  Proof.
    intros db f k. unfold repair_current.
    destruct (row_get f k db) as [o |]; [| repeat split; reflexivity].
    destruct (andb (Pos.eqb (db_tuple_code (normal_key db k)) (db_tuple_code k))
      (output_eqb (option_map (normal_cell db) o) o)); [repeat split; reflexivity |].
    pose proof (put_layout_raw (row_delete f k db) f
      (normal_key db k) (option_map (normal_cell db) o)) as Hlayout.
    now rewrite row_delete_kind, row_delete_slots, row_delete_ids in Hlayout.
  Qed.

  (** Rebuilding keeps layout and allocation. *)
  Lemma layout_rebuild : forall db, wf db ->
    kind (view (rebuild db)) = kind (view db) /\ slots (rebuild db) = slots db /\
    ids (rebuild db) = ids db.
  Proof.
    intros db _. apply (rebuild_preserves (fun current =>
      kind (view current) = kind (view db) /\ slots current = slots db /\ ids current = ids db)).
    - intros current f k Hlayout.
      destruct (repair_current_layout current f k) as [Hkind [Hslots Hids]].
      now rewrite Hkind, Hslots, Hids.
    - intros current i next Hlayout Hpop.
      destruct (db_pop_loser_preserves current i next Hpop) as [_ Hview].
      destruct (db_pop_loser_layout current i next Hpop) as [Hslots [Hids _]].
      now rewrite Hview, Hslots, Hids.
    - repeat split; reflexivity.
  Qed.

  (** Queue removal preserves canonical rows because both the view and forest are unchanged. *)
  Lemma db_pop_loser_canonical : forall db i db',
    db_pop_loser db = Some (i, db') -> canonical db -> canonical db'.
  Proof.
    intros db i db' Hpop Hcanonical.
    destruct (db_pop_loser_preserves db i db' Hpop) as [Hforest Hview].
    unfold canonical, repr in *. now rewrite Hview, Hforest.
  Qed.

  (** Deletion preserves every premise for a later kind-correct insertion. *)
  Lemma row_delete_kind_ok : forall db f k g args output,
    kind_ok (row_delete f k db) g args output <-> kind_ok db g args output.
  Proof.
    intros db f k g args output. unfold kind_ok, allocated, slots_fit.
    now rewrite row_delete_ids, row_delete_slots, row_delete_kind.
  Qed.

  (** Every actual row of a well-formed database satisfies the insertion shape conditions. *)
  Lemma wf_row_kind_ok : forall db f k o, wf db -> row (view db) f k o -> kind_ok db f k o.
  Proof.
    intros db f k o Hwf Hrow. split.
    - intros i Hin. exact (wf_row_ids db Hwf f k o i Hrow Hin).
    - split; [exact (wf_row_slots db Hwf f k o Hrow) |].
      exact (wf_row_kind db Hwf f k o Hrow).
  Qed.

  (** A row of representative identifiers is fixed by the actual guarded normalizer. *)
  Lemma normal_row_fixed : forall db k o,
    UnionFind.wf (db_forest db) ->
    (forall i, In (Id i) (k ++ option_list o) -> repr db i = i) ->
    normal_key db k = k /\ option_map (normal_cell db) o = o.
  Proof.
    intros db k o Hforest Hfixed.
    assert (Hcell : forall c, In c (k ++ option_list o) -> normal_cell db c = c).
    { intros [i | v] Hin; [| reflexivity]. cbn [normal_cell].
      destruct (N.compare (runtime_allocated (db_runtime db)) (Npos i)); try reflexivity;
        rewrite (UnionFind.find_repr i (db_forest db) Hforest); f_equal; exact (Hfixed i Hin). }
    split.
    - unfold normal_key. rewrite <- (map_id k) at 2. apply map_ext_in.
      intros c Hin. apply Hcell. apply in_or_app. now left.
    - destruct o as [c |]; [| reflexivity]. cbn [option_map]. f_equal.
      apply Hcell. apply in_or_app. right. cbn [option_list In]. now left.
  Qed.

  (** Canonical rows are skipped even when an active batch prevents public well-formedness. *)
  Lemma repair_current_canonical : forall db f k,
    UnionFind.wf (db_forest db) -> canonical db -> repair_current f k db = db.
  Proof.
    intros db f k Hforest Hcanonical.
    destruct (row_get f k db) as [o |] eqn:Hrow; [| now apply repair_current_absent].
    destruct (normal_row_fixed db k o Hforest (Hcanonical f k o Hrow)) as [Hkey Houtput].
    now apply repair_current_fixed with (o := o).
  Qed.

  (** A repair begun in a public well-formed state preserves its complete database invariant. *)
  Lemma repair_current_wf : forall db f k, wf db -> wf (repair_current f k db).
  Proof.
    intros db f k Hwf. unfold repair_current.
    destruct (row_get f k db) as [o |] eqn:Hrow; [| exact Hwf].
    destruct (andb (Pos.eqb (db_tuple_code (normal_key db k)) (db_tuple_code k))
      (output_eqb (option_map (normal_cell db) o) o)); [exact Hwf |].
    apply wf_put; [now apply row_delete_wf |]. apply row_delete_kind_ok.
    rewrite (normal_key_correct db k Hwf), (normal_output_correct db o Hwf).
    apply kind_ok_canon; [exact Hwf |]. now apply wf_row_kind_ok.
  Qed.

  (** Rebuilding a canonical database that is closed under congruence leaves the flag alone. *)
  Lemma rebuild_quiet : forall db, wf db -> canonical db ->
    (forall i j, cong db i j -> same (view db) i j) -> changed (rebuild db) = changed db.
  Proof.
    intros db Hwf Hcanonical _.
    assert (Hresult : UnionFind.wf (db_forest (rebuild db)) /\
      canonical (rebuild db) /\ changed (rebuild db) = changed db).
    { apply (rebuild_preserves (fun current => UnionFind.wf (db_forest current) /\
        canonical current /\ changed current = changed db)).
      - intros current f k [Hforest [Hfixed Hflag]].
        rewrite (repair_current_canonical current f k Hforest Hfixed).
        exact (conj Hforest (conj Hfixed Hflag)).
      - intros current i next [Hforest [Hfixed Hflag]] Hpop.
        destruct (db_pop_loser_preserves current i next Hpop) as [Hsame_forest _].
        destruct (db_pop_loser_layout current i next Hpop) as [_ [_ Hsame_flag]].
        split; [now rewrite Hsame_forest |]. split.
        + eapply db_pop_loser_canonical; eassumption.
        + now rewrite Hsame_flag.
      - split; [exact (wf_forest db Hwf) |]. split; [exact Hcanonical | reflexivity]. }
    exact (proj2 (proj2 Hresult)).
  Qed.

  (** Pending identifiers are distinct old roots that no longer represent their classes. *)
  Definition queue_valid (db : t) : Prop :=
    NoDup (runtime_queue (db_runtime db)) /\
      Forall (fun x => repr db x <> x) (runtime_queue (db_runtime db)).

  (** Queue observations and representatives completely determine queue validity. *)
  Lemma queue_valid_frame : forall db db',
    runtime_queue (db_runtime db') = runtime_queue (db_runtime db) ->
    (forall x, repr db' x = repr db x) -> queue_valid db -> queue_valid db'.
  Proof.
    intros db db' Hqueue Hrepr [Hdistinct Hnonroots]. unfold queue_valid.
    rewrite Hqueue. split; [exact Hdistinct |].
    eapply Forall_impl; [| exact Hnonroots]. intros x Hnonroot. now rewrite Hrepr.
  Qed.

  (** A fresh database has no pending roots. *)
  Lemma queue_valid_init : forall ds sl, queue_valid (init ds sl).
  Proof.
    intros ds sl. split; constructor.
  Qed.

  (** Union keeps every old queued loser nonrepresentative and prepends a previously absent root. *)
  Lemma queue_valid_union : forall db i j,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (union i j db).
  Proof.
    intros db i j Hforest [Hdistinct Hnonroots]. rewrite Forall_forall in Hnonroots.
    unfold queue_valid, union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest] eqn:Hunion.
    assert (Htail : Forall (fun x => UnionFind.repr forest x <> x)
      (runtime_queue (db_runtime db))).
    { apply Forall_forall. intros x Hin.
      pose proof (ForestFacts.union_keeps_nonrepresentative i j (db_forest db) x Hforest
        (Hnonroots x Hin)) as Hstable. rewrite Hunion in Hstable. exact Hstable. }
    destruct roots as [[winner loser] |].
    - change (NoDup (loser :: runtime_queue (db_runtime db)) /\
        Forall (fun x => UnionFind.repr forest x <> x) (loser :: runtime_queue (db_runtime db))).
      split.
      + constructor; [| exact Hdistinct]. intro Hin.
        apply (Hnonroots loser Hin).
        exact (ForestFacts.union_loser_was_representative i j (db_forest db)
          winner loser forest Hforest Hunion).
      + constructor; [| exact Htail].
        exact (ForestFacts.union_loser_is_nonrepresentative i j (db_forest db)
          winner loser forest Hforest Hunion).
    - change (NoDup (runtime_queue (db_runtime db)) /\
        Forall (fun x => UnionFind.repr forest x <> x) (runtime_queue (db_runtime db))).
      now split.
  Qed.

  (** Singleton addition changes neither queued identifiers nor their representatives. *)
  Lemma queue_valid_allocate : forall db i,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (allocate_id i db).
  Proof.
    intros db i Hforest Hqueue. eapply (queue_valid_frame db); [reflexivity | | exact Hqueue].
    intro x. apply UnionFind.repr_add. exact Hforest.
  Qed.

  (** Path compression preserves queue validity because it preserves every representative. *)
  Lemma queue_valid_find : forall db i,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (snd (find i db)).
  Proof.
    intros db i Hforest Hqueue. eapply (queue_valid_frame db); [reflexivity | | exact Hqueue].
    intro x. apply UnionFind.find_same. exact Hforest.
  Qed.

  (** Slot maintenance changes neither the queue nor the forest. *)
  Lemma queue_valid_slots_update : forall db add f u,
    queue_valid db -> queue_valid (slots_update add f u db).
  Proof.
    intros db add f u Hqueue. eapply (queue_valid_frame db); [| | exact Hqueue].
    - apply slots_update_preserves. intros. reflexivity.
    - intro x. unfold repr. now rewrite slots_update_forest.
  Qed.

  (** Row replacement changes neither the queue nor the forest. *)
  Lemma queue_valid_row_replace : forall db f k previous o,
    queue_valid db -> queue_valid (row_replace f k previous o db).
  Proof.
    intros db f k previous o Hqueue. eapply (queue_valid_frame db); [| | exact Hqueue].
    - exact (row_replace_preserves _ (@runtime_queue (cell V.t) I.t)
        (fun rows state => eq_refl) (fun flag state => eq_refl)
        (fun all new counts state => eq_refl) f k previous o db).
    - intro x. unfold repr. now rewrite row_replace_forest.
  Qed.

  (** Row deletion retains every pending identifier and its nonrepresentative status. *)
  Lemma queue_valid_row_delete : forall db f k,
    queue_valid db -> queue_valid (row_delete f k db).
  Proof.
    intros db f k Hqueue. eapply (queue_valid_frame db); [| | exact Hqueue].
    - exact (row_delete_preserves _ (@runtime_queue (cell V.t) I.t)
        (fun rows state => eq_refl) (fun all new counts state => eq_refl) f k db).
    - intro x. unfold repr. now rewrite row_delete_forest.
  Qed.

  (** Advancing only clears cache and change observations. *)
  Lemma queue_valid_advance : forall db, queue_valid db -> queue_valid (advance db).
  Proof.
    intros db Hqueue. eapply (queue_valid_frame db); [reflexivity | | exact Hqueue]. reflexivity.
  Qed.

  (** Removing the queue head retains distinctness and the nonrepresentative property. *)
  Lemma queue_valid_pop : forall db i db',
    queue_valid db -> db_pop_loser db = Some (i, db') -> queue_valid db'.
  Proof.
    intros db i db' Hvalid Hpop. unfold db_pop_loser in Hpop.
    destruct (runtime_queue (db_runtime db)) as [| head rest] eqn:Hqueue; [discriminate |].
    injection Hpop as Hname Hdb. subst i db'.
    unfold queue_valid in Hvalid. rewrite Hqueue in Hvalid.
    destruct Hvalid as [Hdistinct Hnonroots].
    change (NoDup rest /\ Forall (fun x => repr db x <> x) rest).
    inversion Hdistinct; inversion Hnonroots; subst. now split.
  Qed.

  (** Distinct allocated queue identifiers fit within the interval without a public-wf premise. *)
  Lemma queue_length_le_ids_from_members : forall db,
    NoDup (runtime_queue (db_runtime db)) ->
    (forall x, In x (runtime_queue (db_runtime db)) -> allocated db x) ->
    pending db <= N.to_nat (ids db).
  Proof.
    intros db Hdistinct Hallocated.
    assert (Hkeys : NoDup (map Pos.to_nat (runtime_queue (db_runtime db)))).
    { apply NoDup_map_NoDup_ForallPairs; [| exact Hdistinct].
      intros x y Hx Hy Hequal. now apply Pos2Nat.inj. }
    assert (Hinclude : incl (map Pos.to_nat (runtime_queue (db_runtime db)))
      (seq 1 (N.to_nat (ids db)))).
    { intros n Hin. apply in_map_iff in Hin as [x [Hequal Hin]]. subst n.
      pose proof (Hallocated x Hin) as Hbound. unfold allocated in Hbound.
      assert (Hnatural : Pos.to_nat x <= N.to_nat (ids db)) by lia.
      pose proof (Pos2Nat.is_pos x). apply in_seq. lia. }
    assert (Hlength : length (map Pos.to_nat (runtime_queue (db_runtime db))) <=
      length (seq 1 (N.to_nat (ids db)))).
    { apply NoDup_incl_length; assumption. }
    rewrite length_map, length_seq in Hlength. exact Hlength.
  Qed.

  (** Public row and allocation invariants supply the queue's allocated-member premise. *)
  Lemma queue_length_le_ids : forall db, wf db -> queue_valid db ->
    pending db <= N.to_nat (ids db).
  Proof.
    intros db Hwf [Hdistinct Hnonroots]. apply queue_length_le_ids_from_members; [exact Hdistinct |].
    pose proof (wf_queue_allocated db Hwf) as Hallocated. now rewrite Forall_forall in Hallocated.
  Qed.

  (** An explicitly consistent binary queue counter inherits the same interval bound. *)
  Lemma queue_counter_le_ids_from_members : forall db,
    NoDup (runtime_queue (db_runtime db)) ->
    (forall x, In x (runtime_queue (db_runtime db)) -> allocated db x) ->
    db_npending db = N.of_nat (pending db) -> (db_npending db <= ids db)%N.
  Proof.
    intros db Hdistinct Hallocated Hcount.
    pose proof (queue_length_le_ids_from_members db Hdistinct Hallocated) as Hbound.
    rewrite Hcount. lia.
  Qed.

  (** The exact binary queue counter is bounded by the identifier allocation counter. *)
  Lemma queue_counter_le_ids : forall db, wf db -> queue_valid db ->
    (db_npending db <= ids db)%N.
  Proof.
    intros db Hwf Hqueue. pose proof (queue_length_le_ids db Hwf Hqueue) as Hbound.
    rewrite (wf_pending_count db Hwf). lia.
  Qed.

  (** Put preserves the forest and queue invariants even inside a repair batch. *)
  Lemma put_queue_state : forall db f k o,
    UnionFind.wf (db_forest db) -> queue_valid db ->
    UnionFind.wf (db_forest (put f k o db)) /\ queue_valid (put f k o db).
  Proof.
    intros db f k o Hforest Hqueue. unfold put.
    remember (row_get f (normal_key db k) db) as previous.
    remember (option_map (normal_cell db) o) as co.
    set (updated := combine_output db f previous co).
    set (next := match previous, co with
      | Some (Some (Id a)), Some (Id b) => union a b db | _, _ => db end).
    assert (Hnext : UnionFind.wf (db_forest next) /\ queue_valid next).
    { unfold next. destruct previous as [[[a | v] |] |]; destruct co as [[b | w] |];
        try (now split). split.
      - rewrite union_forest. now apply UnionFind.wf_union.
      - now apply queue_valid_union. }
    destruct previous as [before |].
    - destruct (output_eqb before updated); [exact Hnext |]. split.
      + rewrite row_replace_forest. exact (proj1 Hnext).
      + apply queue_valid_row_replace. exact (proj2 Hnext).
    - split.
      + rewrite row_replace_forest. exact (proj1 Hnext).
      + apply queue_valid_row_replace. exact (proj2 Hnext).
  Qed.

  Lemma queue_valid_put : forall db f k o,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (put f k o db).
  Proof.
    intros db f k o Hforest Hqueue. exact (proj2 (put_queue_state db f k o Hforest Hqueue)).
  Qed.

  (** Constructor reuse or allocation keeps the same valid pending-root queue. *)
  Lemma make_queue_state : forall db f k,
    UnionFind.wf (db_forest db) -> queue_valid db ->
    UnionFind.wf (db_forest (snd (make f k db))) /\ queue_valid (snd (make f k db)).
  Proof.
    intros db f k Hforest Hqueue.
    assert (Hfresh : UnionFind.wf (db_forest (allocate_id (N.succ_pos (ids db)) db)) /\
      queue_valid (allocate_id (N.succ_pos (ids db)) db)).
    { split; [now apply UnionFind.wf_add | now apply queue_valid_allocate]. }
    unfold make. destruct (row_get f (normal_key db k) db) as [[[j | v] |] |];
      try (exact (conj Hforest Hqueue)).
    all: destruct (kind_get f db) as [[| |m] |]; cbn [snd]; try exact Hfresh.
    all: split; [rewrite row_replace_forest; exact (proj1 Hfresh) |].
    all: apply queue_valid_row_replace; exact (proj2 Hfresh).
  Qed.

  Lemma queue_valid_make : forall db f k,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (snd (make f k db)).
  Proof.
    intros db f k Hforest Hqueue. exact (proj2 (make_queue_state db f k Hforest Hqueue)).
  Qed.

  (** Repair keeps the structural queue invariant without assuming public quietness. *)
  Lemma repair_queue_state : forall db f k,
    UnionFind.wf (db_forest db) -> queue_valid db ->
    UnionFind.wf (db_forest (repair_current f k db)) /\ queue_valid (repair_current f k db).
  Proof.
    intros db f k Hforest Hqueue. unfold repair_current.
    destruct (row_get f k db) as [o |]; [| now split].
    destruct (andb (Pos.eqb (db_tuple_code (normal_key db k)) (db_tuple_code k))
      (output_eqb (option_map (normal_cell db) o) o)); [now split |].
    apply put_queue_state.
    - now rewrite row_delete_forest.
    - now apply queue_valid_row_delete.
  Qed.

  Lemma queue_valid_repair : forall db f k,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (repair_current f k db).
  Proof.
    intros db f k Hforest Hqueue. exact (proj2 (repair_queue_state db f k Hforest Hqueue)).
  Qed.

  (** Both completed and exhausted rebuilds preserve distinct queued nonrepresentatives. *)
  Lemma rebuild_queue_state : forall db,
    UnionFind.wf (db_forest db) -> queue_valid db ->
    UnionFind.wf (db_forest (rebuild db)) /\ queue_valid (rebuild db).
  Proof.
    intros db Hforest Hqueue. apply (rebuild_preserves (fun current =>
      UnionFind.wf (db_forest current) /\ queue_valid current)).
    - intros current f k [Hforest' Hqueue']. now apply repair_queue_state.
    - intros current i next [Hforest' Hqueue'] Hpop. split.
      + now rewrite (proj1 (db_pop_loser_preserves current i next Hpop)).
      + eapply queue_valid_pop; eassumption.
    - now split.
  Qed.

  Lemma queue_valid_rebuild : forall db,
    UnionFind.wf (db_forest db) -> queue_valid db -> queue_valid (rebuild db).
  Proof.
    intros db Hforest Hqueue. exact (proj2 (rebuild_queue_state db Hforest Hqueue)).
  Qed.

End Database.

Module DatabaseT (V : VALUE_T) (I : INDEX_T V) <: DATABASE_ALL V I.
  Include Database V I.
  (* spec: wmark potential *)
  Definition decl_names (db : t) : list positive :=
    map fst (PTrieCode.elements (runtime_kinds (db_runtime db))).
  Definition wmark (db : t) : N :=
    fold_right N.max (N.max (db_nuses db) (ids db))
      (map Npos (db_index_counters db) ++ map Npos (decl_names db) ++
        map (fun c => match c with
          | Id i => Npos (xO i)
          | Val v => Npos (xI (V.encode v))
          end) (db_written_cells db)).
  Definition unit (db : t) : nat :=
    (N.to_nat (N.log2 (ids db)) + 1) * (N.size_nat (wmark db) + 1).
  Definition slots_of (db : t) (f : positive) : nat :=
    length (filter (fun s => Pos.eqb (fst s) f) (slots db)).
  (* STUB-CODE *)
  Definition potential (_ : N) (_ : t) : N := 0%N.
  Definition num_slots (db : t) : nat := length (slots db).
  TimeFun db_cell_code db_cell_eqb db_tuple_code db_row_code row_get kind_get.
  TimeFun normal_cell normal_key output_eqb combine_output.
  TimeFun slot_index_get projection_table_get slot_update_one slot_update_many slot_updated_counters.
  TimeFun slots_update row_write row_replace row_erase row_delete.
  TimeFun init.
  TimeFun find.
  TimeFun lookup.
  TimeFun union.
  TimeFun allocate_id.
  TimeFun make.
  TimeFun put.
  TimeFun repair_current.
  TimeFun db_get_uses db_pop_loser.
  TimeFun db_rstep.
  TimeFun db_rebuild_fuel.
  TimeFun rebuild.
  TimeFun index.
  TimeFun advance.
  TimeFun changed.
  TimeFun ids.

  (** A functional construction trace bounds cached widths using the public index laws. *)
  Lemma index_history_cell_bits : forall written ix bits,
    database_index_history I.empty I.insert I.remove written ix ->
    (forall c, In c written -> cell_bits V.encode c <= bits) ->
    I.max_cell_bits ix <= bits.
  Proof.
    intros written ix bits Hhistory Hwritten.
    apply (database_index_history_induction (cell V.t) I.t I.empty I.insert I.remove written
      (fun current => I.max_cell_bits current <= bits)); [| | | exact Hhistory].
    - rewrite I.max_cell_bits_empty. lia.
    - intros u current Hcells Hcurrent. eapply Nat.le_trans; [apply I.max_cell_bits_insert |].
      apply Nat.max_lub; [exact Hcurrent |].
      induction u as [|c u IH]; cbn [fold_right]; [lia |]. apply Nat.max_lub.
      + apply Hwritten, Hcells. now left.
      + apply IH. intros d Hin. apply Hcells. now right.
    - intros u current Hcurrent. eapply Nat.le_trans; [apply I.max_cell_bits_remove | exact Hcurrent].
  Qed.

  (** Every insertion pays the actual binary increment of the stored projection count. *)
  Lemma T_slot_update_one_count_succ_ge : forall s u state,
    (N.T_succ (runtime_projection_count state s u) <=
      T_slot_update_one true s u state)%N.
  Proof.
    intros s u state. unfold runtime_projection_count.
    time_unfold T_slot_update_one. cbn beta iota zeta. lia.
  Qed.

  (** A non-final deletion pays the predecessor of its stored projection count. *)
  Lemma T_slot_update_one_count_pred_ge : forall s u state,
    runtime_projection_count state s u <> 0%N ->
    runtime_projection_count state s u <> 1%N ->
    (N.T_pred (runtime_projection_count state s u) <=
      T_slot_update_one false s u state)%N.
  Proof.
    intros s u state Hnonzero Hnotone.
    time_unfold T_slot_update_one. cbn beta iota zeta.
    fold (runtime_projection_count state s u).
    destruct (runtime_projection_count state s u) as [|p]; [contradiction |].
    destruct p; [lia | lia | contradiction].
  Qed.

  (** All-ones multiplicities force an arbitrarily long carry inside one slot update. *)
  Lemma T_slot_update_one_carry_ge : forall n s u state,
    runtime_projection_count state s u = Npos (database_carry_value n) ->
    (N.of_nat n + 2 <= T_slot_update_one true s u state)%N.
  Proof.
    intros n s u state Hcount.
    pose proof (T_slot_update_one_count_succ_ge s u state) as Htime.
    rewrite Hcount, database_carry_successor_time in Htime. exact Htime.
  Qed.

  (** A nonempty slot walk pays projection, one update, and its updated-state continuation. *)
  Lemma T_slot_update_many_cons : forall b u s layout rest state,
    T_slot_update_many b u ((s, layout) :: rest) state =
      (1 + T_project_slot_layout layout u +
       T_slot_update_one b s (project_slot_layout layout u) state +
       T_slot_update_many b u rest
         (slot_update_one b s (project_slot_layout layout u) state))%N.
  Proof.
    intros b u s layout rest state. time_unfold T_slot_update_many. ring.
  Qed.

  (** The empty slot walk performs only its entry call. *)
  Lemma T_slot_update_many_nil : forall b u state,
    T_slot_update_many b u [] state = 1%N.
  Proof.
    intros b u state. time_unfold T_slot_update_many. reflexivity.
  Qed.

  (** Reading either index cache pays the binary slot key once. *)
  Lemma T_slot_index_get_width : forall code indexes,
    (T_slot_index_get code indexes <=
      1 + PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1))%N.
  Proof.
    intros code indexes. time_unfold T_slot_index_get.
    apply N.add_le_mono_l. apply PTrieT.T_get_le.
  Qed.

  (** Reading a projection-count table pays the same binary slot key. *)
  Lemma T_projection_table_get_width : forall code counts,
    (T_projection_table_get code counts <=
      1 + PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1))%N.
  Proof.
    intros code counts. time_unfold T_projection_table_get.
    apply N.add_le_mono_l. apply PTrieT.T_get_le.
  Qed.

  (** One slot update exposes count width separately from tuple and index costs. *)
  Lemma T_slot_update_one_local : forall add s u state,
    let code := N.succ_pos s in
    let all := slot_index_get code (runtime_all_indexes state) in
    let fresh := slot_index_get code (runtime_new_indexes state) in
    let count := runtime_projection_count state s u in
    (T_slot_update_one add s u state <=
      32 + N.T_succ_pos s + T_db_tuple_code u +
      6 * (PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1)) +
      2 * (PTrieT.c_trie * N.of_nat (Pos.size_nat (db_tuple_code u) + 1)) +
      I.T_insert u all + I.T_insert u fresh + I.T_remove u all + I.T_remove u fresh +
      N.of_nat (N.size_nat count) + 2)%N.
  Proof.
    intros add s u state. cbn beta zeta.
    set (code := N.succ_pos s) in *.
    set (tuple_code := db_tuple_code u) in *.
    set (table := projection_table_get code (runtime_projection_counts state)).
    set (all := slot_index_get code (runtime_all_indexes state)) in *.
    set (fresh := slot_index_get code (runtime_new_indexes state)) in *.
    pose proof (T_projection_table_get_width code (runtime_projection_counts state)) as Htable.
    pose proof (T_slot_index_get_width code (runtime_all_indexes state)) as Hall.
    pose proof (T_slot_index_get_width code (runtime_new_indexes state)) as Hfresh.
    assert (Hget : (PTrieCode.T_get tuple_code table <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat tuple_code + 1))%N).
    { apply PTrieT.T_get_le. }
    assert (Hset_slot : forall A (v : A) (m : PTrieCode.t A),
      (PTrieCode.T_set code v m <= PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1))%N).
    { intros A v m. apply PTrieT.T_set_le. }
    assert (Hset_tuple : forall v,
      (PTrieCode.T_set tuple_code v table <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat tuple_code + 1))%N).
    { intro v. apply PTrieT.T_set_le. }
    assert (Hremove : (PTrieCode.T_remove tuple_code table <=
      PTrieT.c_trie * N.of_nat (Pos.size_nat tuple_code + 1))%N).
    { apply PTrieT.T_remove_le. }
    pose proof (N.T_succ_le (runtime_projection_count state s u)) as Hsucc.
    pose proof (N.T_pred_le (runtime_projection_count state s u)) as Hpred.
    unfold runtime_projection_count in Hsucc, Hpred |- *.
    fold code tuple_code table in Hsucc, Hpred |- *.
    set (count := match PTrieCode.get tuple_code table with Some (_, n) => n | None => 0%N end) in *.
    time_unfold T_slot_update_one. cbn beta iota zeta.
    fold code tuple_code table count all fresh.
    destruct add; [| destruct count as [|[p|p|]]];
      try time_unfold @T_runtime_set_indexes;
      time_pose; time_simpl; time_cbn_all.
    all: set (slot_cost := (PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1))%N) in *;
      set (tuple_cost := (PTrieT.c_trie * N.of_nat (Pos.size_nat tuple_code + 1))%N) in *;
      clearbody slot_cost tuple_cost; lia.
  Qed.

  (** A preserved state predicate turns uniform per-layout costs into a complete walk bound. *)
  Lemma T_slot_update_many_bound : forall b u layouts state
    (P : database_runtime (cell V.t) I.t -> Prop) budget,
    P state ->
    (forall s layout current, In (s, layout) layouts -> P current ->
      P (slot_update_one b s (project_slot_layout layout u) current) /\
      (T_project_slot_layout layout u +
       T_slot_update_one b s (project_slot_layout layout u) current <= budget)%N) ->
    (T_slot_update_many b u layouts state <=
      (budget + 1) * N.of_nat (length layouts) + 1)%N.
  Proof.
    intros b u layouts. induction layouts as [|[s layout] rest IH];
      intros state P budget Hstate Hstep.
    - rewrite T_slot_update_many_nil. cbn [length]. lia.
    - destruct (Hstep s layout state (or_introl eq_refl) Hstate) as [Hnext Hcost].
      pose proof (IH (slot_update_one b s (project_slot_layout layout u) state) P budget Hnext
        (fun t block current Hin => Hstep t block current (or_intror Hin))) as Htail.
      rewrite T_slot_update_many_cons. cbn [length]. nia.
  Qed.

  (** A duplicate-free walk reads each slot before any earlier update can change it. *)
  Lemma T_slot_update_many_snapshots : forall b u layouts original state budget,
    NoDup (map fst layouts) ->
    (forall s layout, In (s, layout) layouts -> slot_snapshot state s = slot_snapshot original s) ->
    (forall s layout current, In (s, layout) layouts ->
      slot_snapshot current s = slot_snapshot original s ->
      (T_project_slot_layout layout u +
       T_slot_update_one b s (project_slot_layout layout u) current <= budget)%N) ->
    (T_slot_update_many b u layouts state <=
      (budget + 1) * N.of_nat (length layouts) + 1)%N.
  Proof.
    intros b u layouts. induction layouts as [|[s layout] rest IH];
      intros original state budget Hnodup Hsnapshots Hstep.
    - rewrite T_slot_update_many_nil. cbn [length]. lia.
    - cbn [map fst] in Hnodup. inversion Hnodup as [|key keys Hmissing Htail]; subst.
      pose proof (Hstep s layout state (or_introl eq_refl)
        (Hsnapshots s layout (or_introl eq_refl))) as Hhead.
      assert (Hnext : forall t block, In (t, block) rest ->
        slot_snapshot (slot_update_one b s (project_slot_layout layout u) state) t =
          slot_snapshot original t).
      { intros t block Hin. rewrite slot_update_one_snapshot_other.
        - apply (Hsnapshots t block). now right.
        - intro Hequal. subst t. apply Hmissing. exact (in_map fst rest (s, block) Hin). }
      pose proof (IH original (slot_update_one b s (project_slot_layout layout u) state)
        budget Htail Hnext
        (fun t block current Hin => Hstep t block current (or_intror Hin))) as Hrest.
      rewrite T_slot_update_many_cons. cbn [length]. nia.
  Qed.

  (** Counter collection emits precisely the full and delta counter for every visited slot. *)
  Lemma slot_updated_counters_length : forall layouts state,
    length (slot_updated_counters layouts state) = 2 * length layouts.
  Proof.
    intro layouts. induction layouts as [|[s layout] rest IH]; intro state;
      cbn [slot_updated_counters length]; [reflexivity | rewrite IH; lia].
  Qed.

  Definition c_db : N :=
    4096 * (I.c_ix + 1) * (PTrieT.c_trie + 1) * (UnionFindT.c_uf + 1) * (V.c_key + 1).

  (** The database coefficient dominates the trie work and every constant observation cost. *)
  Lemma c_db_trie_budget : (128 * (PTrieT.c_trie + 1) <= c_db)%N.
  Proof.
    unfold c_db. generalize I.c_ix, PTrieT.c_trie, UnionFindT.c_uf, V.c_key.
    intros a b c d. nia.
  Qed.

  (** Every database operation has room for its fixed record-construction overhead. *)
  Lemma c_db_constant_budget : (128 <= c_db)%N.
  Proof.
    pose proof c_db_trie_budget. nia.
  Qed.

  (** The positive bit count agrees with the natural length of the positive size code. *)
  Lemma positive_size_nat : forall p, Pos.to_nat (Pos.size p) = Pos.size_nat p.
  Proof.
    intro p. induction p; cbn [Pos.size Pos.size_nat];
      rewrite ?Pos2Nat.inj_succ, ?IHp; reflexivity.
  Qed.

  (** Binary slot width fits its logarithmic public query size, including zero. *)
  Lemma slot_width_log : forall s, N.size_nat s <= N.to_nat (N.log2 s) + 1.
  Proof.
    intros [| [p | p |]]; cbn [N.size_nat N.log2 N.to_nat Pos.size_nat];
      rewrite ?positive_size_nat; lia.
  Qed.

  (** The positive slot encoding adds at most one bit to the queried number. *)
  Lemma slot_code_bits : forall s, Pos.size_nat (N.succ_pos s) <= N.size_nat s + 1.
  Proof.
    intros [| p]; [cbn; lia |].
    cbn [N.succ_pos N.size_nat]. induction p; cbn [Pos.succ Pos.size_nat]; lia.
  Qed.

  (** Collecting the two final counters pays one bounded slot lookup per cache. *)
  Lemma T_slot_updated_counters_le : forall layouts state bits,
    (forall s layout, In (s, layout) layouts -> N.size_nat s <= bits) ->
    (T_slot_updated_counters layouts state <=
      16 * (I.c_ix + PTrieT.c_trie + 1) * N.of_nat (length layouts + 1) *
        N.of_nat (bits + 1))%N.
  Proof.
    intro layouts. induction layouts as [|[s layout] rest IH]; intros state bits Hbits.
    - time_unfold T_slot_updated_counters. cbn [length]. nia.
    - pose proof (IH state bits (fun t block Hin => Hbits t block (or_intror Hin))) as Htail.
      pose proof (Hbits s layout (or_introl eq_refl)) as Hslot.
      pose proof (slot_code_bits s) as Hcode.
      pose proof (N.T_succ_pos_le s) as Hsucc.
      pose proof (T_slot_index_get_width (N.succ_pos s) (runtime_all_indexes state)) as Hall.
      pose proof (T_slot_index_get_width (N.succ_pos s) (runtime_new_indexes state)) as Hnew.
      pose proof (I.T_next_le (slot_index_get (N.succ_pos s) (runtime_all_indexes state))) as Hall_next.
      pose proof (I.T_next_le (slot_index_get (N.succ_pos s) (runtime_new_indexes state))) as Hnew_next.
      time_unfold T_slot_updated_counters.
      time_unfold @T_runtime_all_indexes. time_unfold @T_runtime_new_indexes.
      cbn [length]. nia.
  Qed.

  (** Taking the maximum over a list retains its initial lower bound. *)
  Lemma fold_max_base : forall values base, (base <= fold_right N.max base values)%N.
  Proof.
    intro values. induction values as [| value values IH]; intro base; cbn [fold_right].
    - lia.
    - eapply N.le_trans; [apply IH | apply N.le_max_r].
  Qed.

  (** Every recorded value is below the maximum over the recording list. *)
  Lemma fold_max_member : forall values base value,
    In value values -> (value <= fold_right N.max base values)%N.
  Proof.
    intro values. induction values as [| head values IH]; intros base value Hin.
    - contradiction.
    - cbn [fold_right]. destruct Hin as [-> | Hin]; [apply N.le_max_l |].
      eapply N.le_trans; [now apply IH | apply N.le_max_r].
  Qed.

  (** Increasing a binary number never decreases its encoded width. *)
  Lemma N_width_mono : forall n m, (n <= m)%N -> N.size_nat n <= N.size_nat m.
  Proof.
    intros [| p] [| q] Hle; cbn [N.size_nat]; try lia.
    destruct (Pos.eq_dec p q) as [-> | Hneq]; [lia |].
    apply Pos.size_nat_monotone. lia.
  Qed.

  (** The exact watermark formula always covers the allocated identifier interval. *)
  Lemma wmark_ids : forall db, (ids db <= wmark db)%N.
  Proof.
    intro db. unfold wmark. eapply N.le_trans; [apply N.le_max_r | apply fold_max_base].
  Qed.

  (** The declaration inventory is exactly the domain of the stored kind trie. *)
  Lemma decl_names_spec : forall db f,
    kind (view db) f <> None <-> In f (decl_names db).
  Proof.
    intros db f. unfold decl_names.
    change (PTrieCode.get f (runtime_kinds (db_runtime db)) <> None <->
      In f (map fst (PTrieCode.elements (runtime_kinds (db_runtime db))))).
    split.
    - intro Hpresent. destruct (PTrieCode.get f (runtime_kinds (db_runtime db))) as [output |] eqn:Hget;
        [| contradiction]. apply in_map_iff. exists (f, output). split; [reflexivity |].
      now apply PTrie.elements_spec.
    - intro Hin. apply in_map_iff in Hin as [[g output] [Heq Hin]].
      cbn [fst] in Heq. subst g. apply PTrie.elements_spec in Hin. congruence.
  Qed.

  (** A guarded slot lookup pays only the query's bits and one trie access. *)
  Lemma T_index_bits : forall s new db,
    (T_index s new db <= 16 * (PTrieT.c_trie + 1) * N.of_nat (N.size_nat s + 1))%N.
  Proof.
    intros s new db. pose proof (N.T_compare_le s (runtime_slot_bound (db_runtime db))) as Hcompare.
    pose proof (N.T_succ_pos_le s) as Hsucc.
    pose proof (slot_code_bits s) as Hbits.
    pose proof (PTrieT.T_get_le I.t (N.succ_pos s)
      (if new then runtime_new_indexes (db_runtime db) else runtime_all_indexes (db_runtime db))) as Hget.
    time_unfold T_index. time_unfold @T_db_runtime. time_unfold @T_runtime_slot_bound.
    destruct (N.compare s (runtime_slot_bound (db_runtime db))); try nia.
    destruct new; time_unfold @T_runtime_new_indexes; time_unfold @T_runtime_all_indexes;
      cbn in Hget; nia.
  Qed.

  (** Unary logarithms agree with the width of a positive binary integer. *)
  Lemma positive_nat_log2_size : forall p,
    S (Nat.log2 (Pos.to_nat p)) = Pos.size_nat p.
  Proof.
    intro p. induction p.
    - rewrite Pos2Nat.inj_xI.
      replace (S (2 * Pos.to_nat p)) with (2 * Pos.to_nat p + 1) by lia.
      rewrite Nat.log2_succ_double by apply Pos2Nat.is_pos.
      cbn [Pos.size_nat]. now rewrite IHp.
    - rewrite Pos2Nat.inj_xO, Nat.log2_double by apply Pos2Nat.is_pos.
      cbn [Pos.size_nat]. now rewrite IHp.
    - reflexivity.
  Qed.

  (** A unary logarithm is bounded by the width of the same binary integer. *)
  Lemma nat_log2_N_width : forall n, Nat.log2 (N.to_nat n) <= N.size_nat n.
  Proof.
    intros [| p]; [reflexivity |].
    change (Nat.log2 (Pos.to_nat p) <= Pos.size_nat p).
    pose proof (positive_nat_log2_size p). lia.
  Qed.

  (** Forest cardinality is exactly the database allocation counter. *)
  Lemma forest_card_ids : forall db, wf db ->
    UnionFind.card (db_forest db) = N.to_nat (ids db).
  Proof.
    intros db Hwf. unfold UnionFind.card. now rewrite (wf_forest_count db Hwf).
  Qed.

  (** Find adds only the fixed record-wrapper work to the actual forest clock. *)
  Lemma T_find_overhead : forall i db,
    (T_find i db = UnionFindT.T_find i (db_forest db) + 14)%N.
  Proof.
    intros i db. time_unfold T_find. time_unfold @T_database_set_forest.
    time_simpl. time_cbn. nia.
  Qed.

  (** The shared coefficient also dominates forest work and fixed wrapper costs. *)
  Lemma c_db_forest_budget : (128 * (UnionFindT.c_uf + 1) <= c_db)%N.
  Proof.
    unfold c_db. generalize I.c_ix, PTrieT.c_trie, UnionFindT.c_uf, V.c_key.
    intros a b c d. nia.
  Qed.

  (** Allocated finds fit the logarithmic database unit without any history assumption. *)
  Lemma T_find_unit_budget : forall i db, wf db -> allocated db i ->
    (UnionFindT.T_find i (db_forest db) <=
      2 * UnionFindT.c_uf * N.of_nat (unit db))%N.
  Proof.
    intros i db Hwf Hi.
    pose proof (UnionFindT.T_find_le i (db_forest db) (wf_forest db Hwf)) as Hfind.
    rewrite (forest_card_ids db Hwf) in Hfind.
    pose proof (nat_log2_N_width (ids db)) as Hlog.
    pose proof (slot_width_log (ids db)) as Hlogwidth.
    assert (Hwidth : Nat.max (UnionFind.width (db_forest db)) (Pos.size_nat i) <=
      N.size_nat (wmark db)).
    { apply Nat.max_lub.
      - eapply Nat.le_trans; [exact (wf_forest_width db Hwf) |].
        apply N_width_mono. apply wmark_ids.
      - change (N.size_nat (Npos i) <= N.size_nat (wmark db)).
        apply N_width_mono. eapply N.le_trans; [exact Hi | apply wmark_ids]. }
    unfold unit. rewrite Nat2N.inj_mul.
    set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost.
    nia.
  Qed.

  (** The input-cell width sum separates tuple payloads from list bookkeeping. *)
  Definition tuple_cell_bits (k : list (cell V.t)) : nat :=
    fold_right (fun c n => cell_bits V.encode c + n) 0 k.

  (** Cell encoding has exactly the public tagged-cell width. *)
  Lemma db_cell_code_bits : forall c,
    Pos.size_nat (db_cell_code c) = cell_bits V.encode c.
  Proof.
    intros [i | v]; reflexivity.
  Qed.

  (** Self-delimiting glue adds at most twice the first code's width. *)
  Lemma glue_width_bound : forall a b,
    Pos.size_nat (glue a b) <= 2 * Pos.size_nat a + Pos.size_nat b.
  Proof.
    intro a. induction a as [a IH | a IH |]; intro b; cbn [glue Pos.size_nat].
    - specialize (IH b). lia.
    - specialize (IH b). lia.
    - lia.
  Qed.

  (** The generated glue clock charges exactly one step per bit of its first code. *)
  Lemma T_glue_bits : forall a b, T_glue a b = N.of_nat (Pos.size_nat a).
  Proof.
    intro a. induction a as [a IH | a IH |]; intro b; time_unfold T_glue;
      cbn [Pos.size_nat]; rewrite ?Nat2N.inj_succ, ?IH; lia.
  Qed.

  (** Tuple codes have width linear in the sum of their tagged cell widths. *)
  Lemma db_tuple_code_bits : forall k,
    Pos.size_nat (db_tuple_code k) <= 2 * tuple_cell_bits k + 1.
  Proof.
    intro k. induction k as [| c rest IH]; [reflexivity |].
    change (Pos.size_nat (glue (db_cell_code c) (db_tuple_code rest)) <=
      2 * (cell_bits V.encode c + tuple_cell_bits rest) + 1).
    pose proof (glue_width_bound (db_cell_code c) (db_tuple_code rest)) as Hglue.
    rewrite db_cell_code_bits in Hglue. lia.
  Qed.

  (** Row-key width is linear in the function name and tuple payload widths. *)
  Lemma db_row_code_bits : forall f k,
    Pos.size_nat (db_row_code f k) <= 2 * Pos.size_nat f + 2 * tuple_cell_bits k + 1.
  Proof.
    intros f k. pose proof (glue_width_bound f (db_tuple_code k)) as Hglue.
    pose proof (db_tuple_code_bits k) as Htuple.
    change (Pos.size_nat (glue f (db_tuple_code k)) <=
      2 * Pos.size_nat f + 2 * tuple_cell_bits k + 1). lia.
  Qed.

  (** Cell encoding pays the value encoder only in the value branch. *)
  Lemma T_db_cell_code_bound : forall c,
    (T_db_cell_code c <= (V.c_key + 2) * N.of_nat (cell_bits V.encode c + 1))%N.
  Proof.
    intros [i | v].
    - time_unfold T_db_cell_code. cbn [cell_bits Pos.size_nat]. nia.
    - pose proof (V.T_encode_le v) as Hencode.
      change (V.T_encode v <= V.c_key * N.of_nat (Pos.size_nat (V.encode v) + 1))%N in Hencode.
      time_unfold T_db_cell_code. cbn [cell_bits Pos.size_nat]. nia.
  Qed.

  (** The generated list-code walk pays once for every cell and its delimiter bits. *)
  Lemma T_list_cell_code_bound : forall k,
    (T_list_code db_cell_code (fun c => T_db_cell_code c) k <=
      (V.c_key + 6) * N.of_nat (tuple_cell_bits k + length k + 1))%N.
  Proof.
    intro k. induction k as [| c rest IH].
    - time_unfold @T_list_code. cbn [tuple_cell_bits fold_right length]. nia.
    - pose proof (T_db_cell_code_bound c) as Hcell.
      pose proof (T_glue_bits (db_cell_code c) (list_code db_cell_code rest)) as Hglue.
      rewrite db_cell_code_bits in Hglue. time_unfold @T_list_code.
      unfold tuple_cell_bits in *. cbn [fold_right length] in *. nia.
  Qed.

  (** Tuple encoding adds only its wrapper to the linear list-code walk. *)
  Lemma T_db_tuple_code_bound : forall k,
    (T_db_tuple_code k <=
      (V.c_key + 8) * N.of_nat (tuple_cell_bits k + length k + 1))%N.
  Proof.
    intro k. pose proof (T_list_cell_code_bound k) as Hlist.
    time_unfold T_db_tuple_code. nia.
  Qed.

  (** Encoding a row key adds the function-name delimiter to the tuple walk. *)
  Lemma T_db_row_code_bound : forall f k,
    (T_db_row_code f k <= (V.c_key + 16) *
      N.of_nat (Pos.size_nat f + tuple_cell_bits k + length k + 1))%N.
  Proof.
    intros f k. pose proof (T_db_tuple_code_bound k) as Htuple.
    pose proof (T_glue_bits f (db_tuple_code k)) as Hglue.
    time_unfold T_db_row_code. time_unfold @T_pair_code.
    time_unfold @Datatypes.T_fst. time_unfold @Datatypes.T_snd.
    cbn [fst snd]. nia.
  Qed.

  (** The row-map wrapper adds at most five steps around encoding and trie lookup. *)
  Lemma T_row_get_overhead : forall f k db,
    (T_row_get f k db <= T_db_row_code f k +
      PTrieT.T_get (db_row_code f k) (runtime_rows (db_runtime db)) + 5)%N.
  Proof.
    intros f k db. time_unfold T_row_get.
    time_unfold @T_db_runtime. time_unfold @T_runtime_rows.
    time_unfold @Map.Datatypes.T_option_map.
    destruct (PTrieCode.get (db_row_code f k) (runtime_rows (db_runtime db)));
      time_unfold @Datatypes.T_snd; nia.
  Qed.

  (** Row lookup pays linearly for the complete encoded query key. *)
  Lemma T_row_get_bound : forall f k db,
    (T_row_get f k db <= 32 * (PTrieT.c_trie + 1) * (V.c_key + 1) *
      N.of_nat (Pos.size_nat f + tuple_cell_bits k + length k + 1))%N.
  Proof.
    intros f k db. pose proof (T_row_get_overhead f k db) as Hrow.
    pose proof (T_db_row_code_bound f k) as Hcode.
    pose proof (PTrieT.T_get_le _ (db_row_code f k)
      (runtime_rows (db_runtime db))) as Hget.
    pose proof (db_row_code_bits f k) as Hbits.
    set (trie_cost := PTrieT.c_trie) in *. clearbody trie_cost.
    nia.
  Qed.

  (** A uniform cell-width bound controls the sum used by tuple encoding. *)
  Lemma tuple_cell_bits_bound : forall u bits,
    (forall c, In c u -> cell_bits V.encode c <= bits) ->
    tuple_cell_bits u <= length u * bits.
  Proof.
    intro u. induction u as [|c rest IH]; intros bits Hcells.
    - reflexivity.
    - pose proof (Hcells c (or_introl eq_refl)) as Hhead.
      pose proof (IH bits (fun d Hin => Hcells d (or_intror Hin))) as Htail.
      unfold tuple_cell_bits in *. cbn [fold_right length]. lia.
  Qed.

  (** One slot mutation fits a uniform tuple, count, slot-key and index-width budget. *)
  Lemma T_slot_update_one_width : forall b s u state arity count_limit bits,
    (forall new, I.wf arity (runtime_slot_index state s new)) ->
    length u <= count_limit ->
    (forall c, In c u -> cell_bits V.encode c <= bits) ->
    N.size_nat s <= bits ->
    N.size_nat (runtime_projection_count state s u) <= bits ->
    (forall new, I.width (runtime_slot_index state s new) u <= 4 * bits + 2) ->
    (T_slot_update_one b s u state <=
      128 * (I.c_ix + PTrieT.c_trie + V.c_key + 1) *
        N.of_nat (count_limit + 1) * N.of_nat (bits + 1))%N.
  Proof.
    intros b s u state arity count_limit bits Harity Hlength Hcells Hslot Hcount Hwidth.
    set (factor := (N.of_nat (count_limit + 1) * N.of_nat (bits + 1))%N).
    pose proof (tuple_cell_bits_bound u bits Hcells) as Hsum.
    assert (Hencoding_size : (N.of_nat (tuple_cell_bits u + length u + 1) <= factor)%N)
      by (unfold factor; nia).
    assert (Htuple_key : (N.of_nat (Pos.size_nat (db_tuple_code u) + 1) <= 2 * factor)%N).
    { pose proof (db_tuple_code_bits u). unfold factor. nia. }
    assert (Hencoding : (T_db_tuple_code u <= (V.c_key + 8) * factor)%N).
    { eapply N.le_trans; [apply T_db_tuple_code_bound |].
      now apply N.mul_le_mono_l. }
    assert (Hmutation : forall new,
      (I.T_insert u (runtime_slot_index state s new) +
       I.T_remove u (runtime_slot_index state s new) <= 8 * I.c_ix * factor)%N).
    { intro new.
      pose proof (I.T_insert_le arity u (runtime_slot_index state s new) (Harity new)) as Hinsert.
      pose proof (I.T_remove_le arity u (runtime_slot_index state s new) (Harity new)) as Hremove.
      assert (Hsize : (N.of_nat (length u + 1) *
        N.of_nat (I.width (runtime_slot_index state s new) u + 1) <= 4 * factor)%N).
      { specialize (Hwidth new). unfold factor. nia. }
      eapply N.le_trans; [apply N.add_le_mono; [exact Hinsert | exact Hremove] |].
      replace (I.c_ix * N.of_nat (length u + 1) *
        N.of_nat (I.width (runtime_slot_index state s new) u + 1) +
        I.c_ix * N.of_nat (length u + 1) *
        N.of_nat (I.width (runtime_slot_index state s new) u + 1))%N with
        (2 * I.c_ix * (N.of_nat (length u + 1) *
          N.of_nat (I.width (runtime_slot_index state s new) u + 1)))%N by ring.
      replace (8 * I.c_ix * factor)%N with (2 * I.c_ix * (4 * factor))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (Hmutation false) as Hall.
    pose proof (Hmutation true) as Hnew.
    unfold runtime_slot_index in Hall, Hnew. cbn beta iota in Hall, Hnew.
    pose proof (T_slot_update_one_local b s u state) as Hlocal. cbn beta zeta in Hlocal.
    pose proof (N.T_succ_pos_le s) as Hsucc.
    pose proof (slot_code_bits s) as Hcode.
    assert (Hfactor : (1 <= factor)%N) by (unfold factor; nia).
    assert (Hbits : (N.of_nat (bits + 1) <= factor)%N) by (unfold factor; nia).
    assert (Hslot_key : (N.of_nat (Pos.size_nat (N.succ_pos s) + 1) <= 2 * factor)%N)
      by lia.
    assert (Hslot_cost : (PTrieT.c_trie * N.of_nat (Pos.size_nat (N.succ_pos s) + 1) <=
      2 * PTrieT.c_trie * factor)%N).
    { replace (2 * PTrieT.c_trie * factor)%N with (PTrieT.c_trie * (2 * factor))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Htuple_cost : (PTrieT.c_trie * N.of_nat (Pos.size_nat (db_tuple_code u) + 1) <=
      2 * PTrieT.c_trie * factor)%N).
    { replace (2 * PTrieT.c_trie * factor)%N with (PTrieT.c_trie * (2 * factor))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hsucc_factor : (N.T_succ_pos s <= factor)%N) by lia.
    assert (Hcount_factor : (N.of_nat (N.size_nat (runtime_projection_count state s u)) <=
      factor)%N) by lia.
    replace (128 * (I.c_ix + PTrieT.c_trie + V.c_key + 1) *
      N.of_nat (count_limit + 1) * N.of_nat (bits + 1))%N with
      (128 * (I.c_ix + PTrieT.c_trie + V.c_key + 1) * factor)%N by (unfold factor; ring).
    clearbody factor.
    assert (Hcoarse : (T_slot_update_one b s u state <=
      34 + (16 * I.c_ix + 16 * PTrieT.c_trie + V.c_key + 10) * factor)%N).
    { clear -Hlocal Hslot_cost Htuple_cost Hall Hnew Hencoding Hsucc_factor Hcount_factor.
      nia. }
    eapply N.le_trans; [exact Hcoarse |]. clear -Hfactor. nia.
  Qed.

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
  Proof.
    intros s new db. pose proof (T_index_bits s new db) as Htime.
    pose proof (slot_width_log s) as Hwidth. pose proof c_db_trie_budget as Hcoefficient.
    nia.
  Qed.

  (** Advancing visits every slot. *)
  Lemma T_advance_le : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof.
    intro db. pose proof c_db_constant_budget as Hcoefficient.
    time_unfold T_advance. time_unfold @T_runtime_set_indexes.
    time_unfold @T_runtime_set_changed. time_unfold @T_database_set_runtime.
    time_simpl. time_cbn. nia.
  Qed.

  (** Every recorded index or activity counter is included in the exact watermark maximum. *)
  Lemma recorded_counters_wmark : forall db p, In p (db_index_counters db) ->
    (Npos p <= wmark db)%N.
  Proof.
    intros db p Hin. unfold wmark. apply fold_max_member.
    apply in_app_iff. left. now apply in_map.
  Qed.

  (** Every recorded cell has a tagged encoding whose width is covered by the watermark. *)
  Lemma recorded_cells_wmark : forall db c, In c (db_written_cells db) ->
    cell_bits V.encode c <= N.size_nat (wmark db).
  Proof.
    intros db c Hin.
    assert (Hbound : (Npos (db_cell_code c) <= wmark db)%N).
    { unfold wmark. apply fold_max_member.
      apply in_app_iff. right. apply in_app_iff. right. apply in_map_iff.
      exists c. split; [destruct c; reflexivity | exact Hin]. }
    pose proof (N_width_mono _ _ Hbound) as Hwidth.
    change (Pos.size_nat (db_cell_code c) <= N.size_nat (wmark db)) in Hwidth.
    now rewrite db_cell_code_bits in Hwidth.
  Qed.

  (** Genuine construction histories bound public indexes without requiring row consistency. *)
  Lemma metadata_wmark_index : forall db s new, metadata_ok db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof.
    intros db s new Hmetadata.
    destruct (metadata_public_index db s new Hmetadata) as [Hcounter Hhistory]. split.
    - now apply recorded_counters_wmark.
    - eapply index_history_cell_bits; [exact Hhistory |].
      intros c Hin. exact (recorded_cells_wmark db c Hin).
  Qed.

  (** The high-water mark covers every stored cell encoding. *)
  Lemma wmark_cells : forall db f k o c, wf db -> row (view db) f k o ->
    In c (k ++ option_list o) -> cell_bits V.encode c <= N.size_nat (wmark db).
  Proof.
    intros db f k o c Hwf Hrow Hin. apply recorded_cells_wmark.
    exact (wf_recorded_rows db Hwf f k o c Hrow Hin).
  Qed.

  (** The high-water mark covers every declared function name. *)
  Lemma wmark_names : forall db f, wf db -> kind (view db) f <> None ->
    Pos.size_nat f <= N.size_nat (wmark db).
  Proof.
    intros db f _ Hkind. change (N.size_nat (Npos f) <= N.size_nat (wmark db)).
    apply N_width_mono. unfold wmark. apply fold_max_member.
    apply in_app_iff. right. apply in_app_iff. left. apply in_map.
    now apply decl_names_spec.
  Qed.

  (** One database unit covers the watermark width and a constant step. *)
  Lemma unit_width_budget : forall db, N.size_nat (wmark db) + 1 <= unit db.
  Proof.
    intro db. unfold unit. nia.
  Qed.

  (** The allocation guard fits the same unit because identifiers are watermarked. *)
  Lemma unit_ids_width : forall db, N.size_nat (ids db) + 1 <= unit db.
  Proof.
    intro db. pose proof (N_width_mono (ids db) (wmark db) (wmark_ids db)).
    pose proof (unit_width_budget db). lia.
  Qed.

  (** Every database unit is positive, including the empty database. *)
  Lemma unit_positive : forall db, (1 <= N.of_nat (unit db))%N.
  Proof.
    intro db. pose proof (unit_width_budget db). lia.
  Qed.

  (** The size operation returns the number of bits as a binary natural. *)
  Lemma N_size_value : forall n, N.to_nat (N.size n) = N.size_nat n.
  Proof.
    intros [| p]; cbn [N.size N.to_nat N.size_nat]; [reflexivity | apply positive_size_nat].
  Qed.

  (** Incrementing a counter adds at most one bit. *)
  Lemma N_successor_width : forall n, N.size_nat (n + 1) <= N.size_nat n + 1.
  Proof.
    intro n. replace (n + 1)%N with (N.succ n) by lia.
    pose proof (slot_code_bits n) as Hbits. destruct n; exact Hbits.
  Qed.

  (** Product encodings have at most the sum of their operand widths. *)
  Lemma N_product_width : forall n m,
    N.size_nat (n * m) <= N.size_nat n + N.size_nat m.
  Proof.
    intros [| p] [| q]; cbn [N.mul N.size_nat]; try lia. apply Pos.size_nat_mul.
  Qed.

  (** A sum has a coarse linear width bound, including both zero operands. *)
  Lemma N_sum_width : forall n m,
    N.size_nat (n + m) <= N.size_nat n + N.size_nat m + 2.
  Proof.
    intros n m.
    assert (Hnumber : (n + m <= (n + 1) * (m + 1))%N) by nia.
    pose proof (N_width_mono _ _ Hnumber) as Hwidth.
    pose proof (N_product_width (n + 1) (m + 1)).
    pose proof (N_successor_width n). pose proof (N_successor_width m). lia.
  Qed.

  (** The pinned watermark covers the stored occurrence count directly. *)
  Lemma wmark_nuses : forall db, (db_nuses db <= wmark db)%N.
  Proof.
    intro db. unfold wmark. eapply N.le_trans; [apply N.le_max_l | apply fold_max_base].
  Qed.

  (** Fuel arithmetic factors through the logarithmic allocation and watermark widths. *)
  Lemma rebuild_fuel_scalar_budget : forall a w l : N,
    (a <= l)%N -> (a <= w)%N -> (1 <= l)%N ->
    ((a + 2) * (a + 2 * w + 6) + 7 * a + 5 * w + 32 <=
      128 * l * (w + 1))%N.
  Proof.
    intros a w l Hal Haw Hl.
    assert (Hleft : (a + 2 <= 3 * l)%N) by lia.
    assert (Hright : (a + 2 * w + 6 <= 6 * (w + 1))%N) by lia.
    pose proof (N.mul_le_mono _ _ _ _ Hleft Hright) as Hproduct.
    assert (Hla : (a <= l * (w + 1))%N) by nia.
    assert (Hlw : (w <= l * (w + 1))%N) by nia.
    assert (Hlone : (1 <= l * (w + 1))%N) by nia.
    nia.
  Qed.

  (** Constructing the exact binary fuel uses one database unit of operand widths. *)
  Lemma T_db_rebuild_fuel_unit : forall db,
    (db_npending db <= wmark db)%N ->
    (T_db_rebuild_fuel db <= 128 * N.of_nat (unit db))%N.
  Proof.
    intros db Hpending.
    pose proof (N_width_mono _ _ (wmark_ids db)) as Hids.
    pose proof (N_width_mono _ _ (wmark_nuses db)) as Huses.
    pose proof (N_width_mono _ _ Hpending) as Hpending_width.
    pose proof (slot_width_log (ids db)) as Hlog.
    pose proof (database_counter_bits_value (N.size (ids db))) as Hsize.
    rewrite N_size_value in Hsize.
    assert (Ha : N.size_nat (N.size (ids db) + 2) <= N.size_nat (ids db) + 2).
    { pose proof (database_counter_bits_value (N.size (ids db) + 2)) as Hwidth.
      rewrite N2Nat.inj_add, N_size_value in Hwidth. cbn in Hwidth. lia. }
    assert (Hb : N.size_nat (db_nuses db + 1) <= N.size_nat (wmark db) + 1).
    { pose proof (N_successor_width (db_nuses db)). lia. }
    assert (Hab : N.size_nat ((N.size (ids db) + 2) * (db_nuses db + 1)) <=
      N.size_nat (ids db) + N.size_nat (wmark db) + 3).
    { pose proof (N_product_width (N.size (ids db) + 2) (db_nuses db + 1)). lia. }
    assert (Habp : N.size_nat ((N.size (ids db) + 2) * (db_nuses db + 1) +
      db_npending db) <= N.size_nat (ids db) + 2 * N.size_nat (wmark db) + 5).
    { pose proof (N_sum_width ((N.size (ids db) + 2) * (db_nuses db + 1))
        (db_npending db)). lia. }
    pose proof (database_N_size_time (ids db)) as Htime_size.
    assert (Htime_a : (N.T_add (N.size (ids db)) 2 <=
      N.of_nat (N.size_nat (ids db)) + 3)%N).
    { pose proof (N.T_add_le (N.size (ids db)) 2) as Htime.
      cbn [N.size_nat Pos.size_nat] in Htime. lia. }
    assert (Htime_b : (N.T_add (db_nuses db) 1 <=
      N.of_nat (N.size_nat (wmark db)) + 2)%N).
    { pose proof (N.T_add_le (db_nuses db) 1) as Htime.
      cbn [N.size_nat Pos.size_nat] in Htime. lia. }
    assert (Htime_product : (N.T_mul (N.size (ids db) + 2) (db_nuses db + 1) <=
      (N.of_nat (N.size_nat (ids db)) + 2) *
        (N.of_nat (N.size_nat (ids db)) + 2 * N.of_nat (N.size_nat (wmark db)) + 6) + 1)%N).
    { pose proof (database_N_mul_time (N.size (ids db) + 2) (db_nuses db + 1)) as Htime.
      clear - Htime Ha Hb. nia. }
    assert (Htime_pending : (N.T_add ((N.size (ids db) + 2) * (db_nuses db + 1))
      (db_npending db) <= N.of_nat (N.size_nat (ids db)) +
        2 * N.of_nat (N.size_nat (wmark db)) + 4)%N).
    { pose proof (N.T_add_le ((N.size (ids db) + 2) * (db_nuses db + 1))
        (db_npending db)) as Htime. lia. }
    assert (Htime_last : (N.T_add ((N.size (ids db) + 2) * (db_nuses db + 1) +
      db_npending db) 1 <= N.of_nat (N.size_nat (ids db)) +
        2 * N.of_nat (N.size_nat (wmark db)) + 7)%N).
    { pose proof (N.T_add_le ((N.size (ids db) + 2) * (db_nuses db + 1) +
        db_npending db) 1) as Htime. cbn [N.size_nat Pos.size_nat] in Htime. lia. }
    eapply N.le_trans with (m :=
      ((N.of_nat (N.size_nat (ids db)) + 2) *
        (N.of_nat (N.size_nat (ids db)) + 2 * N.of_nat (N.size_nat (wmark db)) + 6) +
        7 * N.of_nat (N.size_nat (ids db)) + 5 * N.of_nat (N.size_nat (wmark db)) + 32)%N).
    - time_unfold T_db_rebuild_fuel. time_unfold @T_db_runtime.
      time_unfold @T_runtime_allocated. time_unfold @T_db_nuses. time_unfold @T_db_npending.
      fold (ids db). nia.
    - pose proof (rebuild_fuel_scalar_budget (N.of_nat (N.size_nat (ids db)))
        (N.of_nat (N.size_nat (wmark db)))
        (N.of_nat (N.to_nat (N.log2 (ids db)) + 1))) as Hscalar.
      specialize (Hscalar ltac:(lia) ltac:(lia) ltac:(lia)).
      clear - Hscalar. unfold unit. rewrite Nat2N.inj_mul, !Nat2N.inj_add in *. nia.
  Qed.

  (** Identifier normalization first pays the stored allocation guard, then an optional find. *)
  Lemma T_normal_cell_id : forall db i,
    (T_normal_cell db (Id i) = N.T_compare (ids db) (Npos i) + 3 +
      match N.compare (ids db) (Npos i) with
      | Lt => 0
      | _ => UnionFindT.T_find i (db_forest db) + 2
      end)%N.
  Proof.
    intros db i. time_unfold T_normal_cell. time_unfold @T_db_runtime.
    time_unfold @T_runtime_allocated. time_unfold @T_db_forest.
    time_unfold @Datatypes.T_fst. fold (ids db).
    destruct (N.compare (ids db) (Npos i)); nia.
  Qed.

  (** The guard keeps normalization bounded even for arbitrarily large unallocated queries. *)
  Lemma T_normal_cell_bound : forall db c, wf db ->
    (T_normal_cell db c <=
      (2 * UnionFindT.c_uf + 8) * N.of_nat (unit db))%N.
  Proof.
    intros db [i | v] Hwf.
    - pose proof (N.T_compare_le (ids db) (Npos i)) as Hcompare.
      pose proof (unit_ids_width db) as Hwidth.
      pose proof (unit_positive db) as Hpositive. rewrite T_normal_cell_id.
      destruct (N.compare (ids db) (Npos i)) eqn:Hcompare_result.
      + apply N.compare_eq_iff in Hcompare_result.
        assert (Hi : allocated db i) by (unfold allocated; lia).
        pose proof (T_find_unit_budget i db Hwf Hi) as Hfind.
        set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost. nia.
      + set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost. nia.
      + apply N.compare_gt_iff in Hcompare_result.
        assert (Hi : allocated db i) by (unfold allocated; lia).
        pose proof (T_find_unit_budget i db Hwf Hi) as Hfind.
        set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost. nia.
    - time_unfold T_normal_cell. pose proof (unit_positive db).
      set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost. nia.
  Qed.

  (** Key normalization pays one guarded cell normalization per list element. *)
  Lemma T_normal_key_bound : forall db k, wf db ->
    (T_normal_key db k <= (2 * UnionFindT.c_uf + 12) *
      N.of_nat (length k + 1) * N.of_nat (unit db))%N.
  Proof.
    intros db k Hwf.
    pose proof (ListDef.T_map_le (normal_cell db) (fun c => T_normal_cell db c)
      ((2 * UnionFindT.c_uf + 8) * N.of_nat (unit db))%N k
      (fun c => T_normal_cell_bound db c Hwf)) as Hmap.
    pose proof (unit_positive db) as Hpositive. time_unfold T_normal_key.
    set (forest_cost := UnionFindT.c_uf) in *. clearbody forest_cost. nia.
  Qed.

  (** Normalizing an allocated identifier produces a cell whose width fits one unit. *)
  Lemma normal_cell_allocated_bits : forall db i, wf db -> allocated db i ->
    cell_bits V.encode (normal_cell db (Id i)) <= unit db.
  Proof.
    intros db i Hwf Hi. rewrite (normal_cell_correct db (Id i) Hwf).
    pose proof (repr_allocated db i Hwf Hi) as Hrepr.
    assert (Hbound : (Npos (repr db i) <= wmark db)%N).
    { eapply N.le_trans; [exact Hrepr | apply wmark_ids]. }
    pose proof (N_width_mono _ _ Hbound) as Hbits.
    pose proof (unit_width_budget db) as Hunit.
    cbn [canon cell_bits Pos.size_nat N.size_nat] in *. lia.
  Qed.

  (** Normalization either preserves a query cell or replaces its identifier within the unit. *)
  Lemma normal_cell_bits : forall db c, wf db ->
    cell_bits V.encode (normal_cell db c) <= cell_bits V.encode c + unit db.
  Proof.
    intros db [i | v] Hwf.
    - destruct (N.compare (ids db) (Npos i)) eqn:Hcompare.
      + apply N.compare_eq_iff in Hcompare.
        assert (Hi : allocated db i) by (unfold allocated; lia).
        pose proof (normal_cell_allocated_bits db i Hwf Hi). lia.
      + unfold normal_cell. fold (ids db). rewrite Hcompare. lia.
      + apply N.compare_gt_iff in Hcompare.
        assert (Hi : allocated db i) by (unfold allocated; lia).
        pose proof (normal_cell_allocated_bits db i Hwf Hi). lia.
    - cbn [normal_cell]. lia.
  Qed.

  (** Normalization preserves the number of cells in a query key. *)
  Lemma normal_key_length : forall db k, length (normal_key db k) = length k.
  Proof.
    intros db k. unfold normal_key. apply length_map.
  Qed.

  (** The normalized key width is covered by its original width and one unit per cell. *)
  Lemma normal_key_bits_bound : forall db k, wf db ->
    tuple_cell_bits (normal_key db k) <= tuple_cell_bits k + length k * unit db.
  Proof.
    intros db k Hwf. unfold normal_key, tuple_cell_bits.
    induction k as [| c rest IH]; cbn [map fold_right length] in *; [lia |].
    pose proof (normal_cell_bits db c Hwf). nia.
  Qed.

  (** The declaration guard uses the base name or an actual declared, watermarked name. *)
  Lemma runtime_max_name_bits : forall db, wf db ->
    Pos.size_nat (runtime_max_name (db_runtime db)) <= unit db.
  Proof.
    intros db Hwf. destruct (wf_max_name_attained db Hwf) as [Hbase | Hkind].
    - rewrite Hbase. cbn [Pos.size_nat]. pose proof (unit_positive db). lia.
    - pose proof (wmark_names db _ Hwf Hkind).
      pose proof (unit_width_budget db). lia.
  Qed.

  (** Any function name admitted by the guard has width bounded by one unit. *)
  Lemma guarded_name_bits : forall db f, wf db ->
    (f <= runtime_max_name (db_runtime db))%positive -> Pos.size_nat f <= unit db.
  Proof.
    intros db f Hwf Hname.
    assert (Hnumber : (Npos f <= Npos (runtime_max_name (db_runtime db)))%N)
      by exact Hname.
    pose proof (N_width_mono _ _ Hnumber) as Hbits.
    pose proof (runtime_max_name_bits db Hwf) as Hmaximum.
    cbn [N.size_nat] in Hbits. lia.
  Qed.

  (** The database coefficient covers row encoding, guarded finds, and their fixed overhead. *)
  Lemma c_db_lookup_parts :
    (32 * (PTrieT.c_trie + 1) * (V.c_key + 1) <= c_db /\
      64 * (PTrieT.c_trie + 1) * (V.c_key + 1) +
        2 * UnionFindT.c_uf + 17 <= c_db)%N.
  Proof.
    unfold c_db. generalize I.c_ix, PTrieT.c_trie, UnionFindT.c_uf, V.c_key.
    intros a b c d. split; nia.
  Qed.

  (** Separate payload and structural budgets absorb the three parts of a guarded lookup. *)
  Lemma database_lookup_cost_combine :
    forall coefficient row_cost cell_cost work payload guard normal read : N,
      (row_cost <= coefficient -> 2 * row_cost + cell_cost + 5 <= coefficient ->
        guard <= 5 * work -> normal <= cell_cost * work ->
        read <= row_cost * (payload + 2 * work) ->
        guard + normal + read <= coefficient * work + coefficient * payload)%N.
  Proof.
    intros coefficient row_cost cell_cost work payload guard normal read
      Hrow_cost Hcombined Hguard Hnormal Hread.
    assert (Hpayload : (row_cost * payload <= coefficient * payload)%N).
    { apply N.mul_le_mono_r. exact Hrow_cost. }
    assert (Hwork : ((2 * row_cost + cell_cost + 5) * work <= coefficient * work)%N).
    { apply N.mul_le_mono_r. exact Hcombined. }
    nia.
  Qed.

  (** A name admitted by the guard pays for normalization and the encoded row query. *)
  Lemma T_lookup_active_budget : forall f k db, wf db ->
    (f <= runtime_max_name (db_runtime db))%positive ->
    (Pos.T_compare (runtime_max_name (db_runtime db)) f + 3 +
      T_normal_key db k + T_row_get f (normal_key db k) db <=
      c_db * (N.of_nat (length k + 1) * N.of_nat (unit db)) +
        c_db * N.of_nat (tuple_cell_bits k))%N.
  Proof.
    intros f k db Hwf Hname.
    pose proof (T_normal_key_bound db k Hwf) as Hnormal.
    pose proof (T_row_get_bound f (normal_key db k) db) as Hrow.
    pose proof (Pos.T_compare_le (runtime_max_name (db_runtime db)) f) as Hcompare.
    pose proof (runtime_max_name_bits db Hwf) as Hmaximum.
    pose proof (guarded_name_bits db f Hwf Hname) as Hfunction.
    pose proof (normal_key_bits_bound db k Hwf) as Hkey.
    pose proof (unit_positive db) as Hpositive.
    assert (Hmass : Pos.size_nat f + tuple_cell_bits (normal_key db k) +
      length (normal_key db k) + 1 <= tuple_cell_bits k + 2 * (length k + 1) * unit db).
    { rewrite normal_key_length. nia. }
    eapply database_lookup_cost_combine with
      (row_cost := (32 * (PTrieT.c_trie + 1) * (V.c_key + 1))%N)
      (cell_cost := (2 * UnionFindT.c_uf + 12)%N).
    - exact (proj1 c_db_lookup_parts).
    - pose proof (proj2 c_db_lookup_parts) as Hcoefficient.
      set (trie_cost := PTrieT.c_trie) in *.
      set (forest_cost := UnionFindT.c_uf) in *. clearbody trie_cost forest_cost. nia.
    - nia.
    - nia.
    - eapply N.le_trans; [exact Hrow |]. apply N.mul_le_mono_l. nia.
  Qed.

  (** The high-water mark covers every slot index. *)
  Lemma wmark_index : forall db s new, wf db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof.
    intros db s new Hwf. apply metadata_wmark_index. exact (wf_metadata db Hwf).
  Qed.

  (** Insertion never reduces the spending unit. *)
  Lemma unit_mono_put : forall f k o db, wf db -> unit db <= unit (put f k o db).
  Proof. Admitted. (* STUB *)

  (** Make never reduces the spending unit. *)
  Lemma unit_mono_make : forall f k db, wf db -> unit db <= unit (snd (make f k db)).
  Proof. Admitted. (* STUB *)

  (** Union never reduces the spending unit. *)
  Lemma wmark_union : forall i j db, wmark (union i j db) = wmark db.
  Proof.
    intros i j db. unfold union.
    destruct (UnionFindCode.union i j (db_forest db)) as [roots forest].
    destruct roots as [[winner loser] |]; reflexivity.
  Qed.

  (** Removing a scheduling entry leaves every component of the pinned watermark unchanged. *)
  Lemma wmark_pop_loser : forall db i db', db_pop_loser db = Some (i, db') ->
    wmark db' = wmark db.
  Proof.
    intros db i db' Hpop. unfold db_pop_loser in Hpop.
    destruct (runtime_queue (db_runtime db)) as [| j rest]; [discriminate |].
    injection Hpop as Hname Hdb. subst i db'. reflexivity.
  Qed.

  (** Queue scheduling keeps the spending unit exactly, including in active repair states. *)
  Lemma unit_pop_loser : forall db i db', db_pop_loser db = Some (i, db') ->
    unit db' = unit db.
  Proof.
    intros db i db' Hpop. unfold unit.
    rewrite (wmark_pop_loser db i db' Hpop),
      (proj1 (proj2 (db_pop_loser_layout db i db' Hpop))). reflexivity.
  Qed.

  Lemma unit_mono_union : forall i j db, wf db -> unit db <= unit (union i j db).
  Proof.
    intros i j db _. unfold unit. rewrite union_ids, wmark_union. reflexivity.
  Qed.

  (** Rebuilding never reduces the spending unit. *)
  Lemma unit_mono_rebuild : forall db, wf db -> unit db <= unit (rebuild db).
  Proof. Admitted. (* STUB *)
  (** Advancing keeps the watermark and the amortized credit. *)
  Lemma advance_credit : forall B db, wf db ->
    wmark (advance db) = wmark db /\ (potential B (advance db) = potential B db)%N.
  Proof. Admitted. (* STUB *)

  (** Each initialization scan fits the same total amount of charged input. *)
  Lemma database_init_sum_budget : forall cost decls slots layout declaration_bits slot_bits,
    (1 <= cost ->
      1 + 25 * (layout + slots + 1) + (slots + 1) + (3 * slots + 2) +
      16 * (decls + declaration_bits + 1) + (slots + 1) + (declaration_bits + 4) +
      (slots + 1) + 8 * cost * (decls + declaration_bits + 1) +
      8 * cost * (slots + slot_bits + 1) <=
      128 * cost * (decls + slots + layout + declaration_bits + slot_bits + 1))%N.
  Proof.
    intros cost decls slots layout declaration_bits slot_bits Hcost.
    set (total := (decls + slots + layout + declaration_bits + slot_bits + 1)%N).
    set (budget := (cost * total)%N).
    assert (Htotal : (total <= budget)%N).
    { unfold budget. replace total with (1 * total)%N at 1 by ring.
      apply N.mul_le_mono_r. exact Hcost. }
    assert (Hkinds : (8 * cost * (decls + declaration_bits + 1) <= 8 * budget)%N).
    { unfold budget. replace (8 * cost * (decls + declaration_bits + 1))%N with
        (8 * (cost * (decls + declaration_bits + 1)))%N by ring.
      apply N.mul_le_mono_l.
      apply N.mul_le_mono_l. unfold total. lia. }
    assert (Hgroups : (8 * cost * (slots + slot_bits + 1) <= 8 * budget)%N).
    { unfold budget. replace (8 * cost * (slots + slot_bits + 1))%N with
        (8 * (cost * (slots + slot_bits + 1)))%N by ring.
      apply N.mul_le_mono_l.
      apply N.mul_le_mono_l. unfold total. lia. }
    replace (128 * cost * total)%N with (128 * budget)%N by (unfold budget; ring).
    unfold total in Htotal. clearbody total budget. lia.
  Qed.

  (** Initialization sums preparation, name scans, and amortized dense slot numbering. *)
  Lemma T_init_budget : forall ds sl,
    (T_init ds sl <= 128 * (PTrieT.c_trie + 1) *
      N.of_nat (length ds + length sl + layout_work sl +
        fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds +
        fold_right (fun s n => (Pos.size_nat (fst s) + n)%nat) 0%nat sl + 1))%N.
  Proof.
    intros ds sl.
    pose proof (T_prepare_slot_layouts_le sl) as Hprepare.
    pose proof (T_database_kinds_le ds) as Hkinds.
    pose proof (T_database_max_name_le ds) as Hnames.
    pose proof (T_database_slot_groups_le (prepare_slot_layouts sl) PTrieCode.empty) as Hgroups.
    destruct (database_prepared_sizes sl) as [Hprepared_length Hprepared_bits].
    rewrite Hprepared_length, Hprepared_bits in Hgroups.
    pose proof (Datatypes.T_length_le sl) as Hlength.
    pose proof (T_database_of_nat_le (length sl)) as Hconvert.
    pose proof (database_counter_bits_value (N.of_nat (length sl))) as Hslot_bits.
    rewrite Nat2N.id in Hslot_bits.
    pose proof (N.T_succ_le (N.of_nat (length sl))) as Hsucc.
    pose proof (N.T_succ_pos_le (N.of_nat (length sl))) as Hsucc_pos.
    pose proof (T_database_counter_max_le (Npos (database_max_name ds))
      (N.succ (N.of_nat (length sl)))) as Hmaximum.
    cbn [N.size_nat] in Hmaximum.
    pose proof (database_max_name_bits ds) as Hname_bits.
    assert (Hsucc_small : (N.T_succ (N.of_nat (length sl)) <=
      N.of_nat (length sl) + 1)%N) by (clear - Hsucc Hslot_bits; lia).
    assert (Hsucc_pos_small : (N.T_succ_pos (N.of_nat (length sl)) <=
      N.of_nat (length sl) + 1)%N) by (clear - Hsucc_pos Hslot_bits; lia).
    assert (Hmaximum_small : (N.T_max (Npos (database_max_name ds))
      (N.succ (N.of_nat (length sl))) <=
      N.of_nat (fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds) + 4)%N)
      by (clear - Hmaximum Hname_bits; lia).
    assert (Hbranch : ((match sl with [] => 0 | _ :: _ =>
      N.T_succ_pos (N.of_nat (length sl)) end) <= N.of_nat (length sl) + 1)%N).
    { destruct sl; [cbn; lia | exact Hsucc_pos_small]. }
    clear Hprepared_length Hprepared_bits Hslot_bits Hname_bits Hsucc Hsucc_pos Hmaximum.
    time_unfold T_init. cbn beta zeta.
    rewrite !Nat2N.inj_add in Hprepare, Hkinds, Hnames, Hgroups |- *.
    repeat rewrite Nat2N.inj_add.
    set (cost := (PTrieT.c_trie + 1)%N) in *.
    set (decls := N.of_nat (length ds)) in *.
    set (slots_count := N.of_nat (length sl)) in *.
    set (layout := N.of_nat (layout_work sl)) in *.
    set (declaration_bits := N.of_nat
      (fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds)) in *.
    set (slot_bits := N.of_nat
      (fold_right (fun s n => (Pos.size_nat (fst s) + n)%nat) 0%nat sl)) in *.
    assert (Hcost : (1 <= cost)%N) by (unfold cost; lia).
    pose proof (database_init_sum_budget cost decls slots_count layout declaration_bits slot_bits Hcost)
      as Hbudget.
    clearbody cost decls slots_count layout declaration_bits slot_bits. lia.
  Qed.

  (** Initialization pays for declarations and slot permutations. *)
  Lemma T_init_le : forall ds sl,
    (T_init ds sl <= c_db * N.of_nat (length ds + length sl + layout_work sl + 1) *
      N.of_nat ((fold_right (fun s n => length (snd s) + n) 0 sl + 1)%nat) +
      c_db * N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl)%nat))%N.
  Proof.
    intros ds sl. eapply N.le_trans; [apply T_init_budget |].
    eapply N.le_trans.
    - apply N.mul_le_mono_r. exact c_db_trie_budget.
    - set (amount := N.of_nat (length ds + length sl + layout_work sl + 1)).
      set (names := N.of_nat ((fold_right (fun d n => Pos.size_nat (name d) + n) 0 ds +
        fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl)%nat)).
      assert (Hsum : N.of_nat (length ds + length sl + layout_work sl +
        fold_right (fun d n => (Pos.size_nat (name d) + n)%nat) 0%nat ds +
        fold_right (fun s n => (Pos.size_nat (fst s) + n)%nat) 0%nat sl + 1) =
        (amount + names)%N) by (unfold amount, names; lia).
      rewrite Hsum, N.mul_add_distr_l. apply N.add_le_mono_r.
      replace (c_db * amount)%N with ((c_db * amount) * 1)%N at 1 by ring.
      apply N.mul_le_mono_l. lia.
  Qed.

  (** Find traverses allocated identifiers at the database unit. *)
  Lemma T_find_le : forall i db, wf db -> allocated db i ->
    (T_find i db <= c_db * N.of_nat (unit db))%N.
  Proof.
    intros i db Hwf Hi. rewrite T_find_overhead.
    pose proof (T_find_unit_budget i db Hwf Hi) as Hfind.
    pose proof c_db_forest_budget as Hcoefficient.
    assert (Hunit : (1 <= N.of_nat (unit db))%N).
    { unfold unit. rewrite Nat2N.inj_mul. nia. }
    nia.
  Qed.

  (** Lookup charges the stored unit and query cell encodings. *)
  Lemma T_lookup_le : forall f k db, wf db ->
    (T_lookup f k db <= c_db * N.of_nat (length k + 1) * N.of_nat (unit db) +
      c_db * N.of_nat ((fold_right (fun c n => cell_bits V.encode c + n) 0 k)%nat))%N.
  Proof.
    intros f k db Hwf.
    pose proof (Pos.T_compare_le (runtime_max_name (db_runtime db)) f) as Hcompare.
    pose proof (runtime_max_name_bits db Hwf) as Hmaximum.
    pose proof (unit_positive db) as Hpositive.
    pose proof c_db_constant_budget as Hcoefficient.
    time_unfold T_lookup. time_unfold @T_db_runtime. time_unfold @T_runtime_max_name.
    destruct (Pos.compare (runtime_max_name (db_runtime db)) f) eqn:Hbranch.
    - apply Pos.compare_eq_iff in Hbranch.
      assert (Hname : (f <= runtime_max_name (db_runtime db))%positive) by lia.
      pose proof (T_lookup_active_budget f k db Hwf Hname) as Hactive.
      unfold tuple_cell_bits in Hactive. nia.
    - nia.
    - apply Pos.compare_gt_iff in Hbranch.
      assert (Hname : (f <= runtime_max_name (db_runtime db))%positive) by lia.
      pose proof (T_lookup_active_budget f k db Hwf Hname) as Hactive.
      unfold tuple_cell_bits in Hactive. nia.
  Qed.

  (** The change flag is stored. *)
  Lemma T_changed_le : forall db, (T_changed db <= c_db)%N.
  Proof.
    intro db. pose proof c_db_constant_budget as Hcoefficient.
    time_unfold T_changed. time_unfold @T_db_runtime. time_unfold @T_runtime_changed. nia.
  Qed.

  (** The allocation counter is stored. *)
  Lemma T_ids_le : forall db, (T_ids db <= c_db)%N.
  Proof.
    intro db. pose proof c_db_constant_budget as Hcoefficient.
    time_unfold T_ids. time_unfold @T_db_runtime. time_unfold @T_runtime_allocated. nia.
  Qed.

  Definition use_entry := (positive * list (cell V.t))%type.
  Definition stored_row := (use_entry * option (cell V.t))%type.
  Definition repair_state := (t * list use_entry)%type.

  (* spec: rows uses_entries queue next_id forest_ok class_size uf_state
     index_counters written_cells *)
  Definition rows (db : t) : list stored_row :=
    map snd (PTrieCode.elements (runtime_rows (db_runtime db))).
  (* STUB-CODE *)
  Definition uses_entries : t -> list (positive * use_entry) := fun _ => [].
  Definition queue (db : t) : list positive := runtime_queue (db_runtime db).
  Definition next_id (db : t) : positive := N.succ_pos (ids db).
  (* STUB-CODE *)
  Definition uf_state (db : t) : UnionFind.t := db_forest db.
  (* STUB-CODE *)
  Definition class_size (db : t) (x : positive) : N :=
    N.of_nat (UnionFind.size_of (uf_state db) x).
  (** A historical row key resolves to its current stored key. *)
  (* STUB-CODE *)
  Definition located (_ : t) (_ : positive) (_ : list (cell V.t))
      : option (list (cell V.t)) := None.
  (** Repair retains located rows, metadata and the allocated forest's equality meaning. *)
  Definition forest_ok (db : t) : Prop :=
    (forall f k0 k, located db f k0 = Some k ->
      exists o, In ((f, k), o) (rows db) /\ kind (view db) f <> None) /\
    metadata_ok db /\ db_npending db = N.of_nat (pending db) /\
    UnionFind.wf (db_forest db) /\ UnionFind.card (db_forest db) = N.to_nat (ids db) /\
    (forall i j, same (view db) i j <-> repr db i = repr db j).
  Definition k_credit : N := 1. (* STUB *)
  Definition k_loop : N := 1. (* STUB *)
  Definition k_active : N := 1. (* STUB *)
  Definition k_queue : N := 1. (* STUB *)
  Definition k_stop : N := 1. (* STUB *)
  Definition k_driver : N := 512.

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
    intros db f k0 k Hforest Hlocated. exact (proj1 Hforest f k0 k Hlocated).
  Qed.

  (** The repair invariant retains independent cache metadata throughout an active batch. *)
  Lemma forest_metadata : forall db, forest_ok db -> metadata_ok db.
  Proof.
    intros db [_ [Hmetadata _]]. exact Hmetadata.
  Qed.

  (** The repair invariant equates the stored pending count with the queue observation. *)
  Lemma forest_pending_count : forall db, forest_ok db ->
    db_npending db = N.of_nat (pending db).
  Proof.
    intros db [_ [_ [Hpending _]]]. exact Hpending.
  Qed.

  (** Active repair keeps the same well-formed union-find discipline as public states. *)
  Lemma forest_uf_wf : forall db, forest_ok db -> UnionFind.wf (db_forest db).
  Proof.
    intros db [_ [_ [_ [Hforest _]]]]. exact Hforest.
  Qed.

  (** The forest's cardinality agrees with the exact allocation counter. *)
  Lemma forest_cardinality : forall db, forest_ok db ->
    UnionFind.card (db_forest db) = N.to_nat (ids db).
  Proof.
    intros db [_ [_ [_ [_ [Hcard _]]]]]. exact Hcard.
  Qed.

  (** The equality log and forest representatives have the same meaning during repair. *)
  Lemma forest_same_repr : forall db, forest_ok db ->
    forall i j, same (view db) i j <-> repr db i = repr db j.
  Proof.
    intros db [_ [_ [_ [_ [_ Hsame]]]]]. exact Hsame.
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

  (** Active repair states expose cache metadata directly, without a public wf conversion. *)
  Lemma inv_on_metadata : forall db work, inv_on db work -> metadata_ok db.
  Proof.
    intros db work Hinv. apply forest_metadata. unfold inv_on in Hinv. tauto.
  Qed.

  (** Active and queued repair states expose their forest invariant directly. *)
  Lemma inv_on_forest_wf : forall db work, inv_on db work -> UnionFind.wf (db_forest db).
  Proof.
    intros db work Hinv. apply forest_uf_wf. unfold inv_on in Hinv. tauto.
  Qed.

  (** Active repair retains the exact forest cardinality without a public wf conversion. *)
  Lemma inv_on_forest_card : forall db work, inv_on db work ->
    UnionFind.card (db_forest db) = N.to_nat (ids db).
  Proof.
    intros db work Hinv. apply forest_cardinality. unfold inv_on in Hinv. tauto.
  Qed.

  (** Active repair states expose equality agreement without a public wf conversion. *)
  Lemma inv_on_same_repr : forall db work i j, inv_on db work ->
    (same (view db) i j <-> repr db i = repr db j).
  Proof.
    intros db work i j Hinv. apply forest_same_repr. unfold inv_on in Hinv. tauto.
  Qed.

  (** Representatives remain fixed throughout every active repair state. *)
  Lemma inv_on_repr_idem : forall db work i, inv_on db work ->
    repr db (repr db i) = repr db i.
  Proof.
    intros db work i Hinv. unfold repr. apply UnionFind.repr_idem.
    exact (inv_on_forest_wf db work Hinv).
  Qed.

  (** Active repair states expose the exact stored queue count directly. *)
  Lemma inv_on_pending_count : forall db work, inv_on db work ->
    db_npending db = N.of_nat (pending db).
  Proof.
    intros db work Hinv. apply forest_pending_count. unfold inv_on in Hinv. tauto.
  Qed.

  (** Distinct allocated queue entries bound the actual stored pending counter. *)
  Lemma inv_on_pending_bound : forall db work, inv_on db work ->
    (db_npending db <= ids db)%N.
  Proof.
    intros db work Hinv. apply queue_counter_le_ids_from_members.
    - unfold inv_on, queue in Hinv. tauto.
    - unfold inv_on, queue in Hinv. tauto.
    - exact (inv_on_pending_count db work Hinv).
  Qed.

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
  Definition get_uses : positive -> t -> list use_entry := db_get_uses.
  TimeFun get_uses.
  Definition pop_loser : t -> option (positive * t) := db_pop_loser.
  TimeFun pop_loser.
  Definition repair_entry (e : use_entry) (db : t) : t :=
    repair_current (fst e) (snd e) db.
  TimeFun repair_entry.
  Definition rstep (s : repair_state) : repair_state + t := db_rstep s.
  TimeFun rstep.
  Definition rebuild_fuel (db : t) : N := db_rebuild_fuel db.
  TimeFun rebuild_fuel.

  TimeFun locate.
  TimeFun rank_slots.
  Definition k_locate : N := 1. (* STUB *)
  Definition k_repair : N := 1. (* STUB *)
  Definition k_pop : N := 64 * (PTrieT.c_trie + 1) * (UnionFindT.c_uf + 1).
  Definition k_rstep : N := 64.
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
    metadata_ok db /\
    (forall s f perm new, slot_of db s = Some (f, perm) ->
      I.wf (length perm) (index s new db)).

  (** Empty initialized caches satisfy the maintained slot invariant for every layout. *)
  Lemma slots_ok_init : forall ds sl, slots_ok (init ds sl).
  Proof.
    intros ds sl. split; [apply metadata_init |].
    intros s f perm new _. rewrite index_init_empty. apply I.wf_empty.
  Qed.

  (** Recorded slot bounds identify each declared slot with its raw cache entry. *)
  Lemma slots_metadata_inside : forall db s f perm, metadata_ok db ->
    slot_of db s = Some (f, perm) -> (s < runtime_slot_bound (db_runtime db))%N.
  Proof.
    intros db s f perm Hmetadata Hslot.
    destruct Hmetadata as (_ & _ & _ & _ & _ & _ & _ & Hbound). rewrite Hbound.
    assert (Hinside : N.to_nat s < length (slots db)).
    { apply nth_error_Some. unfold slot_of in Hslot. congruence. }
    lia.
  Qed.
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
  Proof.
    intros db Hinv. exact (proj1 (inv_on_metadata db [] Hinv)).
  Qed.

  (** The maintained invariant gives the slot facts that an update reads. *)
  Lemma F_slots_ok : forall db work, inv_on db work -> slots_ok db.
  Proof.
    intros db work Hinv. split; [exact (inv_on_metadata db work Hinv) |].
    intros s f perm new Hslot.
    destruct Hinv as (_ & _ & _ & _ & Hindexes & _).
    specialize (Hindexes s f perm Hslot). destruct new; tauto.
  Qed.
  (** A slot update keeps those facts. *)
  Lemma F_slots_ok_update : forall db b f u, slots_ok db ->
    slots_fit db f (length u) -> slots_ok (slots_update b f u db).
  Proof.
    intros db b f u [Hmetadata Harity] Hfits.
    assert (Hupdated : metadata_ok (slots_update b f u db)).
    { apply metadata_slots_update; [exact Hmetadata | intros _; exact Hfits]. }
    split; [exact Hupdated |]. intros s g perm new Hslot.
    assert (Horiginal : slot_of db s = Some (g, perm)).
    { unfold slot_of in Hslot |- *. rewrite slots_update_slots in Hslot. exact Hslot. }
    pose proof (Harity s g perm new Horiginal) as Hwf.
    rewrite index_runtime_slot in Hwf by
      (eapply slots_metadata_inside; [exact Hmetadata | exact Horiginal]).
    rewrite index_runtime_slot by
      (eapply slots_metadata_inside; [exact Hupdated | exact Hslot]).
    pose proof Hmetadata as Hfacts.
    destruct Hfacts as (_ & _ & _ & _ & _ & _ & Hgroups & _).
    destruct (Pos.eq_dec f g) as [Hequal | Hdifferent].
    - subst g.
      assert (Hpositions : Forall (fun p => p < length u) perm).
      { assert (Hin : In (f, perm) (slots db)) by (eapply nth_error_In; exact Horiginal).
        exact (proj2 (Hfits perm Hin)). }
      rewrite (slot_snapshot_index _ _ s
        (slots_update_snapshot_same db b f u s perm Hgroups Horiginal Hpositions)).
      rewrite slot_update_one_index. destruct b.
      + apply I.wf_insert; [exact Hwf | now apply permute_length].
      + destruct (runtime_projection_count (db_runtime db) s (permute perm u)) as [|p];
          [exact Hwf |]. destruct p; try exact Hwf. now apply I.wf_remove.
    - rewrite (slot_snapshot_index _ _ s
        (slots_update_snapshot_other db b f u s g perm Hgroups Horiginal Hdifferent)).
      exact Hwf.
  Qed.

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
  Proof.
    intros db work. time_unfold T_rstep. time_unfold T_db_rstep.
    destruct work as [| [f k] rest]; cbn [fst snd].
    - unfold pop_loser. destruct (db_pop_loser db) as [[x next] |];
        time_unfold T_pop_loser; try time_unfold T_get_uses;
        time_simpl; unfold k_rstep; lia.
    - time_unfold T_repair_entry. time_simpl. cbn [fst snd]. unfold k_rstep. lia.
  Qed.
  (** A pop moves the selected bucket at one step per entry. *)
  Lemma T_pop_loser_counter_bound : forall db,
    (T_pop_loser db <= 64 + N.of_nat (N.size_nat (db_npending db)))%N.
  Proof.
    intro db. pose proof (N.T_pred_le (db_npending db)) as Hpred.
    time_unfold T_pop_loser. time_unfold T_db_pop_loser.
    destruct (runtime_queue (db_runtime db)) as [| i rest].
    - time_simpl. time_cbn. lia.
    - time_unfold @T_runtime_set_union. time_unfold @T_database_set_runtime.
      time_unfold @T_database_set_pending. time_simpl. time_cbn. lia.
  Qed.

  Lemma T_pop_loser_le : forall db x db', inv db -> pop_loser db = Some (x, db') ->
    (T_pop_loser db <= k_pop * N.of_nat (work_weight db (bucket db x) + 1) *
      N.of_nat (unit db))%N.
  Proof.
    intros db x db' Hinv _.
    pose proof (T_pop_loser_counter_bound db) as Htime.
    assert (Hcount : (db_npending db <= wmark db)%N).
    { eapply N.le_trans; [exact (inv_on_pending_bound db [] Hinv) | apply wmark_ids]. }
    pose proof (N_width_mono _ _ Hcount) as Hbits.
    pose proof (unit_width_budget db) as Hwidth.
    pose proof (unit_positive db) as Hunit.
    assert (Hcoefficient : (64 <= k_pop)%N) by (unfold k_pop; nia).
    assert (Hweight : (1 <= N.of_nat (work_weight db (bucket db x) + 1))%N) by lia.
    assert (Hsmall : (T_pop_loser db <= 64 * N.of_nat (unit db))%N) by nia.
    nia.
  Qed.
  (** An empty pop reads the stored queue. *)
  Lemma T_pop_none_le : forall db, inv db -> pop_loser db = None ->
    (T_pop_loser db <= k_pop * N.of_nat (unit db))%N.
  Proof.
    intros db _ Hnone. unfold pop_loser, db_pop_loser in Hnone.
    destruct (runtime_queue (db_runtime db)) as [| i rest] eqn:Hqueue; [| discriminate].
    time_unfold T_pop_loser. time_unfold T_db_pop_loser. rewrite Hqueue.
    time_unfold @T_db_runtime. time_unfold @T_runtime_queue.
    assert (Hunit : (1 <= N.of_nat (unit db))%N).
    { unfold unit. rewrite Nat2N.inj_mul. nia. }
    unfold k_pop. nia.
  Qed.
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
  Proof. reflexivity. Qed.

  (** Direct bucket lookup agrees with the occurrence inventory. *)
  Lemma F4_bucket : forall db work x, inv_on db work -> get_uses x db = bucket db x.
  Proof. Admitted. (* STUB *)

  (** An empty pop detects an empty pending queue. *)
  Lemma F4_pop_none : forall db, inv db -> (pop_loser db = None <-> queue db = []).
  Proof.
    intros db _. unfold pop_loser, db_pop_loser, queue.
    destruct (runtime_queue (db_runtime db)); split; congruence.
  Qed.

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
  Proof.
    intros db [| [f k] rest]; reflexivity.
  Qed.

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
  Proof.
    intros [db work] next _ Hstep. unfold rstep in Hstep.
    destruct work as [| [f k] rest]; cbn [db_rstep fst snd] in Hstep.
    - destruct (db_pop_loser db) as [[i current] |] eqn:Hpop; [| discriminate].
      injection Hstep as Hnext. subst next. cbn [fst].
      destruct (db_pop_loser_preserves db i current Hpop) as [_ Hview].
      destruct (db_pop_loser_layout db i current Hpop) as [_ [Hids _]].
      split; [now rewrite Hview | exact Hids].
    - injection Hstep as Hnext. subst next. cbn [fst].
      destruct (repair_current_layout db f k) as [Hkind [_ Hids]]. now split.
  Qed.

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
  Proof.
    intro db.
    assert (Hcallback : forall s, (T_db_rstep s <= T_rstep s)%N).
    { intro s. time_unfold T_rstep. lia. }
    pose proof (LoopNFacts.T_loopN_mono _ _ db_rstep T_db_rstep T_rstep Hcallback
      (db_rebuild_fuel db) (db, [])) as Hloop.
    time_unfold T_rebuild. time_unfold T_rebuild_fuel.
    unfold rebuild_fuel, rstep in *. cbn beta zeta.
    change (T_loopN db_rstep (fun s => T_db_rstep s) (db_rebuild_fuel db) (db, []) <=
      T_loopN (fun s : repair_state => db_rstep s) T_rstep
        (db_rebuild_fuel db) (db, []))%N in Hloop.
    destruct (loopN db_rstep (db_rebuild_fuel db) (db, []));
      time_simpl; unfold k_driver; lia.
  Qed.

  (** Slot lookup charges its binary slot code. *)
  Lemma T10_index : forall s new db,
    (T_index s new db <= c_db * N.of_nat (N.to_nat (N.log2 s) + 1))%N.
  Proof.
    exact T_index_le.
  Qed.

  (** Advancing clears each maintained slot once. *)
  Lemma T11_advance : forall db, (T_advance db <= c_db * N.of_nat (num_slots db + 1))%N.
  Proof.
    exact T_advance_le.
  Qed.

  (** Stored counters agree with the occurrence inventory and pending queue. *)
  Lemma F15_counts : forall db work, inv_on db work ->
    N.to_nat (nuses db) = length (uses_entries db) /\ N.of_nat (pending db) = npending db.
  Proof. Admitted. (* STUB *)

  (** The declaration inventory contains precisely the names with a kind. *)
  Lemma F_decl_names : forall db f, inv db ->
    (kind (view db) f <> None <-> In f (decl_names db)).
  Proof.
    intros db f _. apply decl_names_spec.
  Qed.

  (** The stored watermark is the exact historical maximum of written payloads and counters. *)
  Lemma F_wmark : forall db, inv db ->
    wmark db = fold_right N.max (N.max (nuses db) (ids db))
      (map Npos (index_counters db) ++ map Npos (decl_names db) ++
        map (fun c => match c with
          | Id i => Npos (xO i)
          | Val v => Npos (xI (V.encode v))
          end) (written_cells db)).
  Proof.
    reflexivity.
  Qed.

  (** Every slot index fits the stored counter and cell watermark. *)
  Lemma F_wmark_index : forall db s new, inv db ->
    (Npos (I.next (index s new db)) <= wmark db)%N /\
    I.max_cell_bits (index s new db) <= N.size_nat (wmark db).
  Proof.
    intros db s new Hinv. apply metadata_wmark_index. exact (inv_on_metadata db [] Hinv).
  Qed.

  (** Class sizes come from the size-based union-find. *)
  Lemma F_uf_bridge : forall db work x, inv_on db work ->
    repr db x = UnionFind.repr (uf_state db) x /\
    class_size db x = N.of_nat (UnionFind.size_of (uf_state db) x) /\
    UnionFind.wf (uf_state db).
  Proof.
    intros db work x Hinv. split; [reflexivity |]. split; [reflexivity |].
    exact (inv_on_forest_wf db work Hinv).
  Qed.

  (** Root classes are nonempty and bounded by allocation. *)
  Lemma F_class_size : forall db work x, inv_on db work ->
    (1 <= class_size db (repr db x))%N /\
    (class_size db (repr db x) <= N.max 1 (ids db))%N.
  Proof.
    intros db work x Hinv. unfold class_size, uf_state.
    pose proof (ConcreteUnionFindFacts.size_of_positive (db_forest db) (repr db x)) as Hpositive.
    pose proof (ConcreteUnionFindFacts.size_of_card_bound (db_forest db) (repr db x)
      (inv_on_forest_wf db work Hinv)) as Hbound.
    rewrite (inv_on_forest_card db work Hinv) in Hbound. split; [lia |].
    assert (Hbinary : (N.of_nat (UnionFind.size_of (db_forest db) (repr db x)) <=
      N.of_nat (Nat.max 1 (N.to_nat (ids db))))%N) by lia.
    rewrite Nat2N.inj_max, N2Nat.id in Hbinary. exact Hbinary.
  Qed.

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
  Proof.
    intros db Hinv.
    assert (Hpending : (db_npending db <= wmark db)%N).
    { eapply N.le_trans; [exact (inv_on_pending_bound db [] Hinv) | apply wmark_ids]. }
    pose proof (T_db_rebuild_fuel_unit db Hpending) as Hfuel.
    pose proof (unit_positive db) as Hpositive.
    time_unfold T_rebuild_fuel. unfold k_driver. nia.
  Qed.

  (** The [T_loopN_amort] driver retains the final database credit. *)
  Lemma T8a_loop_final : forall B U db, inv db -> (ids (rebuild db) <= B)%N ->
    unit (rebuild db) <= U ->
    (T_loopN rstep T_rstep (rebuild_fuel db) (db, []) +
      k_loop * N.of_nat U * rebuild_potential B (rebuild db) <=
      k_loop * N.of_nat U * rebuild_potential B db + k_stop * N.of_nat U +
      c_loopN * N.of_nat (N.size_nat (rebuild_fuel db) + 1))%N.
  Proof. Admitted. (* STUB *)

End DatabaseT.
