(** * Full solution checking

    The checker evaluates each row and checks every value written by the row.
    For example, a side contribution above its stored value rejects the candidate.
    Builds on: Fixpoint.Query, Fixpoint.SystemSig and Base.MapSig. *)

From Stdlib Require Import List NArith Lia.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.

Module CheckCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: CHECK_OPS L S.
  Definition look (m : kmap S.key L.t) (x : S.key) : L.t :=
    look_or S.key_code L.bot m x.

  Definition check_rows (p : S.prog) (rs : list S.row) (m : kmap S.key L.t) : bool :=
    forallb (fun r => row_ok L.leb (look m) (S.target p r)
      (eval_query (S.resume p) (look m) (S (length (S.deps p r))) (S.start p r))) rs.

  Definition check (p : S.prog) (m : kmap S.key L.t) : bool :=
    check_rows p (S.rows p) m.
End CheckCode.

Module Check (L : LATTICE) (S : SYSTEM L) <: CHECK L S.
  Include CheckCode L S.

  Lemma look_spec : forall m x, look m x = look_or S.key_code L.bot m x.
  Proof. reflexivity. Qed.

  Lemma check_rows_iff : forall p rs m,
    check_rows p rs m = true <-> S.post_on p rs (look m).
  Proof.
    intros p rs m; unfold check_rows, S.post_on, S.eval.
    apply forallb_forall.
  Qed.

  Lemma check_spec : forall p m, check p m = check_rows p (S.rows p) m.
  Proof. reflexivity. Qed.

  Lemma check_sound : forall p m, check p m = true -> S.post_solution p (look m).
  Proof.
    intros p m Hcheck; apply check_rows_iff; exact Hcheck.
  Qed.
End Check.

Module CheckT (L : LATTICE_T) (S : SYSTEM_T L) <: CHECK_T L S.
  Include Check L S.
  TimeFun look.
  TimeFun check_rows.
  TimeFun check.

  Definition c_lookup : N := (S.c_sys + PTrieT.c_trie + 2)%N.

  Definition c_chk : N := (128 * (c_lookup + S.c_sys + L.c_lat + 1))%N.

  (** A lookup pays once for the key encoding and once for trie traversal. *)
  Lemma T_look_bound : forall m x,
    (T_look m x <= c_lookup * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros m x.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) m) as Hget.
    unfold T_look, T_look_or, PTrieT.T_get in *.
    unfold c_lookup, S.key_bits in *.
    rewrite !Nat2N.inj_add in *.
    time_cbn_all.
    nia.
  Qed.

  (** The public checker constant includes the lookup bound. *)
  Lemma T_look_le : forall m x,
    (T_look m x <= c_chk * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros m x.
    pose proof (T_look_bound m x) as Hlook.
    unfold c_chk.
    nia.
  Qed.

  (** Universal checking charges each callback occurrence and constant list overhead. *)
  Lemma T_forallb_sum_le : forall A (f : A -> bool) T_f xs,
    (List.T_forallb f T_f xs <=
      fold_right (fun x total => T_f x + 2 + total)%N 1%N xs)%N.
  Proof.
    intros A f T_f xs.
    induction xs as [| x xs IH]; time_step.
  Qed.

  Definition row_unit (p : S.prog) (B : nat) : N :=
    (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1)%N.

  (** A listed output comparison fits the value and key portions of the row budget. *)
  Lemma T_compare_bound : forall p B m x a,
    (forall y, L.size (look m y) <= B) ->
    S.key_bits x <= S.kw p ->
    (N.of_nat (L.size a) <= S.row_work p B)%N ->
    (T_look m x + L.T_leb a (look m x) <=
      (c_lookup + L.c_lat + 1) * row_unit p B)%N.
  Proof.
    intros p B m x a Hsize Hbits Ha.
    pose proof (T_look_bound m x) as Hlook.
    pose proof (L.T_leb_le a (look m x)) as Hleb.
    specialize (Hsize x).
    unfold row_unit.
    rewrite !Nat2N.inj_add in *.
    assert (HsizeN : (N.of_nat (L.size (look m x)) <= N.of_nat B)%N) by lia.
    assert (HbitsN : (N.of_nat (S.key_bits x) <= N.of_nat (S.kw p))%N) by lia.
    nia.
  Qed.

  (** Every side occurrence is compared once, including repeated destination keys. *)
  Lemma T_sides_bound : forall p B m ss,
    (forall y, L.size (look m y) <= B) ->
    (forall x a, In (x, a) ss -> S.key_bits x <= S.kw p) ->
    Forall (fun xa => (N.of_nat (L.size (snd xa)) <= S.row_work p B)%N) ss ->
    (List.T_forallb (fun xa => L.leb (snd xa) (look m (fst xa)))
      (fun xa => 1 + (1 + (1 + T_look m (fst xa)) +
        L.T_leb (snd xa) (look m (fst xa))))%N ss <=
      ((c_lookup + L.c_lat + 1) * row_unit p B + 5) * N.of_nat (length ss) + 1)%N.
  Proof.
    intros p B m ss Hsize Hkeys Hvalues.
    induction ss as [| [x a] ss IH].
    - time_step.
    - inversion Hvalues as [| xa tail Ha Htail]; subst.
      assert (Hcompare := T_compare_bound p B m x a Hsize
        (Hkeys x a (or_introl eq_refl)) Ha).
      specialize (IH (fun y b Hin => Hkeys y b (or_intror Hin)) Htail).
      time_step.
  Qed.

  (** Comparing one row checks its primary result and all declared side occurrences. *)
  Lemma T_row_ok_bound : forall p B m r a ss,
    S.wf p -> In r (S.rows p) ->
    (forall y, L.size (look m y) <= B) -> S.eval p r (look m) = Some (a, ss) ->
    (T_row_ok L.leb L.T_leb (look m) (T_look m) (S.target p r) (Some (a, ss)) <=
      (c_lookup + L.c_lat + 6) * N.of_nat (length ss + 1) * row_unit p B)%N.
  Proof.
    intros p B m r a ss Hwf Hr Hsize Heval.
    destruct (S.eval_size_le p r (look m) B a ss Hwf Hr Hsize Heval)
      as [Ha Hss].
    assert (Htarget : S.key_bits (S.target p r) <= S.kw p).
    { apply (S.key_bits_le p r (S.target p r) Hwf Hr).
      unfold S.writes; apply in_or_app; left; now left. }
    assert (Hsides : forall x b, In (x, b) ss -> S.key_bits x <= S.kw p).
    { intros x b Hin.
      apply (S.key_bits_le p r x Hwf Hr).
      unfold S.writes; apply in_or_app; left; right.
      exact (S.sides_within p r (look m) a ss x b Hwf Hr Heval Hin). }
    pose proof (T_compare_bound p B m (S.target p r) a Hsize Htarget Ha) as Hcompare.
    pose proof (T_sides_bound p B m ss Hsize Hsides Hss) as Hsides_cost.
    assert (Hunit : (1 <= row_unit p B)%N) by (unfold row_unit; nia).
    unfold T_row_ok; time_simpl; time_cbn.
    rewrite Nat2N.inj_add; time_cbn.
    nia.
  Qed.

  (** The system's reachable-frame contract bounds every selected continuation. *)
  Lemma T_eval_bound : forall p B m r,
    S.wf p -> In r (S.rows p) -> (forall y, L.size (look m y) <= B) ->
    (T_eval_query (S.resume p) (S.T_resume p) (look m) (T_look m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) <=
      20 * (c_lookup + S.c_sys + 1) *
        N.of_nat (length (S.deps p r) + length (S.sides p r) + 1) * row_unit p B)%N.
  Proof.
    intros p B m r Hwf Hr Hsize.
    destruct (S.eval p r (look m)) as [[a ss]|] eqn:Heval.
    2: { exfalso; exact (S.eval_total p r (look m) Hwf Hr Heval). }
    pose proof (S.sides_count p r (look m) a ss Hwf Hr Heval) as Hcount.
    assert (Hread : forall n q acc x f,
      loop_fuel (eval_step (S.resume p) (look m)) n (S.start p r, nil) = inl (q, acc) ->
      fst (peel q acc) = inr (x, f) ->
      (T_look m x + S.T_resume p f (look m x) <=
        (c_lookup + S.c_sys) * row_unit p B)%N).
    { intros n q acc x f Hprefix Hask.
      pose proof (S.asks_within p r (look m) n q acc x f Hwf Hr Hprefix Hask) as Hdep.
      assert (Hbits : S.key_bits x <= S.kw p).
      { apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
      pose proof (T_look_bound m x) as Hlook.
      pose proof (S.T_resume_le p r (look m) B n q acc x f Hwf Hr Hsize Hprefix Hask)
        as Hresume.
      assert (HbitsN : (N.of_nat (S.key_bits x) <= N.of_nat (S.kw p))%N) by lia.
      unfold row_unit; rewrite Nat2N.inj_add in Hlook; time_cbn; nia. }
    pose proof (T_eval_query_le (S.resume p) (S.T_resume p) (look m) (T_look m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) a ss
      ((c_lookup + S.c_sys) * row_unit p B)%N Heval Hread) as Heval_cost.
    assert (HcountN : (N.of_nat (length ss) <= N.of_nat (length (S.sides p r)))%N)
      by lia.
    assert (Hunit : (1 <= row_unit p B)%N) by (unfold row_unit; nia).
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
    nia.
  Qed.

  Definition row_size (p : S.prog) (r : S.row) : nat :=
    length (S.deps p r) + length (S.sides p r) + 1.

  Definition c_row : N := (32 * (c_lookup + S.c_sys + L.c_lat + 1))%N.

  (** A row callback pays for metadata, evaluation and its output comparisons. *)
  Lemma T_row_bound : forall p B m r,
    S.wf p -> In r (S.rows p) -> (forall y, L.size (look m y) <= B) ->
    (1 + (S.T_target p r +
       (S.T_deps p r + Datatypes.T_length (S.deps p r) + S.T_start p r +
        T_eval_query (S.resume p) (S.T_resume p) (look m) (T_look m)
          (Datatypes.S (length (S.deps p r))) (S.start p r))) +
      T_row_ok L.leb L.T_leb (look m) (T_look m) (S.target p r) (S.eval p r (look m)) <=
      c_row * N.of_nat (row_size p r) * row_unit p B)%N.
  Proof.
    intros p B m r Hwf Hr Hsize.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (Datatypes.T_length_le (S.deps p r)) as Hlength.
    pose proof (S.T_start_le p r Hwf Hr) as Hstart.
    pose proof (S.row_work_mono p 0 B ltac:(lia)) as Hwork.
    pose proof (T_eval_bound p B m r Hwf Hr Hsize) as Heval_cost.
    destruct (S.eval p r (look m)) as [[a ss]|] eqn:Heval.
    2: { exfalso; exact (S.eval_total p r (look m) Hwf Hr Heval). }
    pose proof (T_row_ok_bound p B m r a ss Hwf Hr Hsize Heval) as Hcheck.
    pose proof (S.sides_count p r (look m) a ss Hwf Hr Heval) as Hcount.
    assert (HcountN : (N.of_nat (length ss) <= N.of_nat (length (S.sides p r)))%N)
      by lia.
    set (u := row_unit p B) in *.
    set (d := N.of_nat (row_size p r)).
    assert (Hd : (1 <= d)%N) by (unfold d, row_size; lia).
    assert (Hdeps_size : (N.of_nat (length (S.deps p r) + 1) <= d)%N)
      by (unfold d, row_size; lia).
    assert (Hsides_size : (N.of_nat (length ss + 1) <= d)%N)
      by (unfold d, row_size; lia).
    assert (Hu : (1 <= u)%N) by (unfold u, row_unit; nia).
    assert (Hkey_unit : (N.of_nat (S.kw p + 1) <= u)%N).
    { unfold u, row_unit; rewrite Nat2N.inj_add; nia. }
    assert (Hwork_unit : (S.row_work p 0 + 1 <= u)%N)
      by (unfold u, row_unit; nia).
    set (chunk := (d * u)%N).
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; clear -Hd Hu; nia).
    assert (Hunit_chunk : (u <= chunk)%N) by (unfold chunk; clear -Hd; nia).
    assert (Htarget_bound : (S.T_target p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Htarget|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hstart_bound : (S.T_start p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hstart|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hdeps_bound : (S.T_deps p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hdeps|].
      unfold chunk; rewrite N.mul_assoc.
      apply N.mul_le_mono; [now apply N.mul_le_mono_l|exact Hkey_unit]. }
    assert (Hlength_bound : (Datatypes.T_length (S.deps p r) <= chunk)%N).
    { rewrite Nat2N.inj_add in Hdeps_size; unfold chunk.
      clear -Hlength Hdeps_size Hu; nia. }
    assert (Hcheck_bound : (T_row_ok L.leb L.T_leb (look m) (T_look m)
      (S.target p r) (Some (a, ss)) <= (c_lookup + L.c_lat + 6) * chunk)%N).
    { eapply N.le_trans; [exact Hcheck|].
      unfold chunk; rewrite N.mul_assoc.
      apply N.mul_le_mono_r; now apply N.mul_le_mono_l. }
    fold (row_size p r) in Heval_cost.
    fold d in Heval_cost.
    replace (20 * (c_lookup + S.c_sys + 1) * d * u)%N with
      ((20 * (c_lookup + S.c_sys + 1)) * chunk)%N in Heval_cost
      by (unfold chunk; ring).
    replace (c_row * d * u)%N with (c_row * chunk)%N by (unfold chunk; ring).
    clear -Htarget_bound Hstart_bound Hdeps_bound Hlength_bound Hcheck_bound
      Heval_cost Hchunk.
    unfold c_row.
    nia.
  Qed.

  (** Row weights include one unit for every list occurrence, including duplicates. *)
  Lemma rows_length_le : forall p rs,
    length rs <= fold_right Nat.add 0%nat (List.map (row_size p) rs).
  Proof.
    intros p rs; unfold row_size; induction rs as [| r rs IH]; cbn; lia.
  Qed.

  (** A row sweep adds only constant overhead to the sum of its callback budgets. *)
  Lemma T_check_rows_bound : forall p rs m B, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x, L.size (look m x) <= B) ->
    (T_check_rows p rs m <= c_row *
      N.of_nat (fold_right Nat.add 0%nat (List.map (row_size p) rs)) * row_unit p B +
      2 * N.of_nat (length rs + 1))%N.
  Proof.
    intros p rs m B Hwf Hrows Hsize.
    induction rs as [| r rs IH].
    - unfold T_check_rows; time_step.
    - pose proof (T_row_bound p B m r Hwf (Hrows r (or_introl eq_refl)) Hsize) as Hrow.
      specialize (IH (fun r Hr => Hrows r (or_intror Hr))).
      unfold T_check_rows in *.
      unfold S.eval in Hrow.
      time_unfold @List.T_forallb.
      time_simpl; time_cbn.
      change (fun (f : S.frame) (a : L.t) => S.T_resume p f a)
        with (S.T_resume p) in *.
      change (fun x : S.key => T_look m x) with (T_look m) in *.
      change (fun a b : L.t => L.T_leb a b) with L.T_leb in *.
      rewrite !Nat2N.inj_add in *.
      nia.
  Qed.

  (** The checker sweep stays within the public per-row budget. *)
  Lemma T_check_rows_le : forall p rs m B, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (forall x, L.size (look m x) <= B) ->
    (T_check_rows p rs m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs) + 1)%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
  Proof.
    intros p rs m B Hwf Hrows Hsize.
    pose proof (T_check_rows_bound p rs m B Hwf Hrows Hsize) as Hcheck.
    pose proof (rows_length_le p rs) as Hlength.
    assert (HlengthN : (N.of_nat (length rs) <=
      N.of_nat (fold_right Nat.add 0%nat (List.map (row_size p) rs)))%N) by lia.
    fold (row_unit p B).
    change (T_check_rows p rs m <= c_chk *
      N.of_nat (fold_right Nat.add 0%nat (List.map (row_size p) rs) + 1) * row_unit p B)%N.
    assert (Hunit : (1 <= row_unit p B)%N) by (unfold row_unit; nia).
    unfold c_chk, c_row in *.
    rewrite !Nat2N.inj_add in *.
    nia.
  Qed.

  (** Whole-program checking also pays for enumeration of the program's rows. *)
  Lemma T_check_le : forall p m B, S.wf p ->
    (forall x, L.size (look m x) <= B) ->
    (T_check p m <= c_chk *
      N.of_nat ((fold_right Nat.add 0
        (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
          (S.rows p)) + 1)%nat) *
      (S.row_work p B + N.of_nat (S.kw p) + L.c_lat * N.of_nat (B + 1) + 1))%N.
  Proof.
    intros p m B Hwf Hsize.
    pose proof (T_check_rows_bound p (S.rows p) m B Hwf (fun r Hr => Hr) Hsize) as Hcheck.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    pose proof (rows_length_le p (S.rows p)) as Hlength.
    assert (HlengthN : (N.of_nat (length (S.rows p)) <=
      N.of_nat (fold_right Nat.add 0%nat (List.map (row_size p) (S.rows p))))%N) by lia.
    fold (row_unit p B).
    change (T_check p m <= c_chk *
      N.of_nat (fold_right Nat.add 0%nat (List.map (row_size p) (S.rows p)) + 1) *
      row_unit p B)%N.
    assert (Hunit : (1 <= row_unit p B)%N) by (unfold row_unit; nia).
    unfold T_check, c_chk, c_row in *.
    rewrite !Nat2N.inj_add in *.
    nia.
  Qed.
End CheckT.
