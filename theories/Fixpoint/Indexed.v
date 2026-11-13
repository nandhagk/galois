(** * Prepared row indexes

    Preparation numbers rows and indexes their declared writes.
    For example, repeated writes by one row occupy one index entry per key.
    Builds on: Fixpoint.IndexedSig and Base.Trie. *)

From Stdlib Require Import List PArith Arith NArith Bool Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig IndexedSig.

Module IndexedCode (L : LATTICE_OPS) (S : SYSTEM_OPS L) <: INDEXED_OPS L S.
  Definition prog := indexed S.prog S.row.
  Definition key := S.key.
  Definition row := (positive * S.row)%type.
  Definition frame := S.frame.
  Definition key_code := S.key_code.
  Definition key_eqb := S.key_eqb.
  Definition rows (p : prog) := numbered_rows p.
  Definition target (p : prog) (r : row) := S.target (program p) (snd r).
  Definition start (p : prog) (r : row) := S.start (program p) (snd r).
  Definition resume (p : prog) := S.resume (program p).
  Definition deps (p : prog) (r : row) := S.deps (program p) (snd r).
  Definition sides (p : prog) (r : row) := S.sides (program p) (snd r).
  Definition row_code (r : row) := fst r.
  Definition rows_of (p : prog) (x : key) :=
    match trie_get (key_code x) (write_index p) with
    | Some rs => rs
    | None => nil
    end.
  Fixpoint number_from (id : positive) (rs : list S.row) : list row :=
    match rs with
    | nil => nil
    | r :: rest => (id, r) :: number_from (Pos.succ id) rest
    end.
  Definition index_row p (r : row) idx :=
    let keys := fold_left (fun seen x => PTrieCode.set (key_code x) tt seen)
      (S.target p (snd r) :: S.sides p (snd r)) Empty in
    fold_right (fun entry acc =>
      let code := fst entry in
      let previous := match trie_get code acc with Some rs => rs | None => nil end in
      PTrieCode.set code (r :: previous) acc) idx (PTrieCode.elements keys).
  Definition prepare p :=
    let rs := number_from 1%positive (S.rows p) in
    Indexed S.prog S.row p rs (fold_right (index_row p) Empty rs).
End IndexedCode.

Module Indexed (L : LATTICE) (S : SYSTEM L) <: INDEXED L S.
  Include IndexedCode L S.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := S.wf (program p) /\ p = prepare (program p).

  (** Dropping row numbers recovers the input list, including repeated rows. *)
  Lemma number_from_snd : forall rs id,
    List.map snd (number_from id rs) = rs.
  Proof.
    induction rs as [|r rs IH]; intro id; cbn [number_from List.map snd].
    - reflexivity.
    - now rewrite IH.
  Qed.

  (** Every prepared row refers to a listed row of the underlying program. *)
  Lemma listed_original : forall p r, wf p -> In r (rows p) ->
    In (snd r) (S.rows (program p)).
  Proof.
    intros p r [_ Hprepare] Hin.
    apply in_map with (f := @snd positive S.row) in Hin.
    unfold rows in Hin; rewrite Hprepare in Hin.
    cbn [prepare numbered_rows] in Hin.
    now rewrite number_from_snd in Hin.
  Qed.

  (** Numbering does not alter query evaluation, even outside a prepared list. *)
  Lemma eval_original : forall p r look,
    eval p r look = S.eval (program p) (snd r) look.
  Proof.
    reflexivity.
  Qed.

  (** Key encodings are the underlying system's encodings. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    exact S.key_code_inj.
  Qed.

  (** Key equality is the underlying system's reflected equality. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact S.key_eqb_spec.
  Qed.

  (** Listed prepared rows terminate whenever the underlying program is well formed. *)
  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p r look Hwf Hin; rewrite eval_original.
    apply S.eval_total; [exact (proj1 Hwf)|].
    exact (listed_original p r Hwf Hin).
  Qed.

  (** Numbering preserves the declared-read frame property. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p r s u Hwf Hin Hreads; rewrite !eval_original.
    apply S.reads_within; [exact (proj1 Hwf)| |exact Hreads].
    exact (listed_original p r Hwf Hin).
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p r look n q acc x f Hwf Hin Hreach Hask.
    eapply S.asks_within; [exact (proj1 Hwf)| |exact Hreach|exact Hask].
    exact (listed_original p r Hwf Hin).
  Qed.

  (** Numbering preserves the declared side-write keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p r look a ss x b Hwf Hin Heval Hside.
    eapply S.sides_within; [exact (proj1 Hwf)| |exact Heval|exact Hside].
    exact (listed_original p r Hwf Hin).
  Qed.

  (** Numbering preserves the declared side-write occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p r look a ss Hwf Hin Heval.
    eapply S.sides_count; [exact (proj1 Hwf)| |exact Heval].
    exact (listed_original p r Hwf Hin).
  Qed.

  (** Every row number is at least the starting number of its suffix. *)
  Lemma number_from_lower : forall rs id r,
    In r (number_from id rs) -> Pos.to_nat id <= Pos.to_nat (fst r).
  Proof.
    induction rs as [|head rest IH]; intros id r Hin.
    - contradiction.
    - cbn [number_from] in Hin; destruct Hin as [<-|Hin].
      + cbn; lia.
      + specialize (IH (Pos.succ id) r Hin).
        rewrite Pos2Nat.inj_succ in IH; lia.
  Qed.

  (** A row number identifies its occurrence in the numbered list. *)
  Lemma number_from_inj : forall rs id a b,
    In a (number_from id rs) -> In b (number_from id rs) ->
    fst a = fst b -> a = b.
  Proof.
    induction rs as [|head rest IH]; intros id a b Ha Hb Hcode.
    - contradiction.
    - cbn [number_from] in Ha, Hb.
      destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb].
      + reflexivity.
      + pose proof (number_from_lower rest (Pos.succ id) b Hb) as Hlower.
        cbn [fst] in Hcode; rewrite <- Hcode, Pos2Nat.inj_succ in Hlower; lia.
      + pose proof (number_from_lower rest (Pos.succ id) a Ha) as Hlower.
        cbn [fst] in Hcode; rewrite Hcode, Pos2Nat.inj_succ in Hlower; lia.
      + exact (IH (Pos.succ id) a b Ha Hb Hcode).
  Qed.

  (** Numbered rows have distinct codes within each prepared program. *)
  Lemma row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof.
    intros p a b [_ Hprepare] Ha Hb Hcode.
    unfold rows in Ha, Hb; rewrite Hprepare in Ha, Hb.
    eapply number_from_inj; [exact Ha|exact Hb|exact Hcode].
  Qed.

  (** Inserting all declared keys retains precisely their codes. *)
  Lemma key_set_lookup : forall xs seen x,
    trie_get (key_code x)
      (fold_left (fun acc y => PTrieCode.set (key_code y) tt acc) xs seen) = Some tt <->
    In x xs \/ trie_get (key_code x) seen = Some tt.
  Proof.
    induction xs as [|y ys IH]; intros seen x; cbn [fold_left In].
    - tauto.
    - rewrite IH.
      destruct (key_eqb_spec x y) as [Heq|Hneq].
      + subst y; rewrite PTrie.get_set_same; cbn; tauto.
      + rewrite PTrie.get_set_other.
        * cbn; intuition congruence.
        * intro Hcode; apply Hneq, key_code_inj, Hcode.
  Qed.

  (** A bucket fold adds its row exactly at the enumerated key codes. *)
  Lemma bucket_fold_spec : forall entries idx code (r q : row),
    In q (match trie_get code
      (fold_right (fun entry acc =>
        let previous := match trie_get (fst entry) acc with Some rs => rs | None => nil end in
        PTrieCode.set (fst entry) (r :: previous) acc) idx entries) with
      | Some rs => rs
      | None => nil
      end) <->
    (q = r /\ In (code, tt) entries) \/
    In q (match trie_get code idx with Some rs => rs | None => nil end).
  Proof.
    induction entries as [|[other []] entries IH]; intros idx code r q.
    - cbn; tauto.
    - cbn [fold_right fst].
      destruct (Pos.eq_dec code other) as [->|Hneq].
      + rewrite PTrie.get_set_same; cbn [In].
        rewrite IH; intuition congruence.
      + rewrite PTrie.get_set_other by exact Hneq.
        rewrite IH; cbn [In]; intuition congruence.
  Qed.

  (** Indexing one row adds it at exactly its declared writes. *)
  Lemma index_row_spec : forall p r idx x q,
    In q (match trie_get (key_code x) (index_row p r idx) with
      | Some rs => rs
      | None => nil
      end) <->
    (q = r /\ In x (S.target p (snd r) :: S.sides p (snd r))) \/
    In q (match trie_get (key_code x) idx with Some rs => rs | None => nil end).
  Proof.
    intros p r idx x q; unfold index_row.
    rewrite bucket_fold_spec, PTrie.elements_spec, key_set_lookup, PTrie.get_empty.
    intuition discriminate.
  Qed.

  (** Folding the write index preserves all and only the listed writer occurrences. *)
  Lemma write_index_spec : forall p rs x r,
    In r (match trie_get (key_code x) (fold_right (index_row p) Empty rs) with
      | Some found => found
      | None => nil
      end) <->
    In r rs /\ In x (S.target p (snd r) :: S.sides p (snd r)).
  Proof.
    intros p rs; induction rs as [|head rest IH]; intros x r.
    - rewrite PTrie.get_empty; cbn; tauto.
    - cbn [fold_right]; rewrite index_row_spec, IH.
      cbn [In]; intuition congruence.
  Qed.

  (** A prepared index lists exactly the rows that may write the requested key. *)
  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof.
    intros p x r [_ Hprepare].
    rewrite Hprepare; unfold rows_of, rows, writes, target, sides.
    cbn [prepare program numbered_rows write_index].
    apply write_index_spec.
  Qed.
  Lemma prepare_program : forall p, program (prepare p) = p.
  Proof.
    reflexivity.
  Qed.
  Lemma prepare_rows : forall p, List.map snd (rows (prepare p)) = S.rows p.
  Proof.
    intro p; apply number_from_snd.
  Qed.
  Lemma eval_prepare : forall p r look, In r (rows (prepare p)) ->
    eval (prepare p) r look = S.eval p (snd r) look.
  Proof.
    reflexivity.
  Qed.
  Lemma wf_prepare : forall p, S.wf p -> wf (prepare p).
  Proof.
    intros p Hwf; split; [exact Hwf|reflexivity].
  Qed.
  (** Prepared targets agree with the original rows. *)
  Lemma prepare_target : forall p r, In r (rows (prepare p)) ->
    target (prepare p) r = S.target p (snd r).
  Proof.
    reflexivity.
  Qed.
  (** Prepared dependencies agree with the original rows. *)
  Lemma prepare_deps : forall p r, In r (rows (prepare p)) ->
    deps (prepare p) r = S.deps p (snd r).
  Proof.
    reflexivity.
  Qed.
  (** Prepared side declarations agree with the original rows. *)
  Lemma prepare_sides : forall p r, In r (rows (prepare p)) ->
    sides (prepare p) r = S.sides p (snd r).
  Proof.
    reflexivity.
  Qed.
  (** Preparation keeps precisely the original post-solutions. *)
  Lemma prepare_post : forall p look,
    post_solution (prepare p) look <-> S.post_solution p look.
  Proof.
    intros p look; split; intros Hpost r Hin.
    - rewrite <- prepare_rows in Hin.
      apply in_map_iff in Hin as [nr [Hrow Hnr]].
      subst r; exact (Hpost nr Hnr).
    - apply Hpost.
      rewrite <- prepare_rows.
      now apply in_map.
  Qed.
End Indexed.

Module IndexedT (L : LATTICE_T) (S : SYSTEM_T L) <: INDEXED_T L S.
  Include Indexed L S.
  Definition row_work (p : prog) (B : nat) : N := S.row_work (program p) B.
  Definition kw (p : prog) : nat := S.kw (program p).
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  TimeFun row_code.
  TimeFun rows_of.
  TimeFun number_from.
  TimeFun index_row.
  TimeFun prepare.

  Definition c_sys : N := (S.c_sys + 4)%N.
  Definition c_loc : N := (S.c_sys + PTrieT.c_trie + 6)%N.

  Lemma row_work_mono : forall p s s', s <= s' ->
    (row_work p s <= row_work p s')%N.
  Proof.
    intros p s s' Hle; apply S.row_work_mono, Hle.
  Qed.
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p r x Hwf Hin Hx.
    eapply S.key_bits_le; [exact (proj1 Hwf)| |exact Hx].
    exact (listed_original p r Hwf Hin).
  Qed.
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intro x; pose proof (S.T_key_code_le x) as Htime.
    unfold S.key_bits in Htime.
    unfold c_sys, key_bits, key_code; time_step.
  Qed.
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros a b; pose proof (S.T_key_eqb_le a b) as Htime.
    unfold S.key_bits in Htime.
    unfold c_sys, key_bits, key_code; time_step.
  Qed.
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p r look s a ss Hwf Hin Hsize Heval.
    eapply S.eval_size_le; [exact (proj1 Hwf)| |exact Hsize|exact Heval].
    exact (listed_original p r Hwf Hin).
  Qed.
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof.
    intros p Hwf; unfold c_sys; time_step.
  Qed.
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p r Hwf Hin.
    pose proof (S.T_target_le (program p) (snd r) (proj1 Hwf)
      (listed_original p r Hwf Hin)) as Htime.
    unfold c_sys, row_work; time_step.
  Qed.
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p r Hwf Hin.
    pose proof (S.T_start_le (program p) (snd r) (proj1 Hwf)
      (listed_original p r Hwf Hin)) as Htime.
    unfold c_sys, row_work; time_step.
  Qed.
  (** Resuming a frame that a listed row reaches pays for the sizes of the lookup values. *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p r look s n q acc x f Hwf Hin Hsize Hreach Hask.
    pose proof (S.T_resume_le (program p) (snd r) look s n q acc x f
      (proj1 Hwf) (listed_original p r Hwf Hin) Hsize Hreach Hask) as Htime.
    unfold c_sys, row_work; time_step.
  Qed.
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r Hwf Hin.
    pose proof (S.T_deps_le (program p) (snd r) (proj1 Hwf)
      (listed_original p r Hwf Hin)) as Htime.
    unfold c_sys, kw, deps; time_step.
  Qed.
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r Hwf Hin.
    pose proof (S.T_sides_le (program p) (snd r) (proj1 Hwf)
      (listed_original p r Hwf Hin)) as Htime.
    unfold c_sys, kw, sides; time_step.
  Qed.
  Lemma T_row_code_le : forall r,
    (T_row_code r <= c_loc * N.of_nat (Pos.size_nat (row_code r) + 1))%N.
  Proof.
    intro r; unfold c_loc; time_step.
  Qed.
  Lemma T_rows_of_le : forall p x, wf p ->
    (T_rows_of p x <= c_loc * N.of_nat (length (rows_of p x) + key_bits x + 1))%N.
  Proof.
    intros p x Hwf.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (list row) (key_code x) (write_index p)) as Hget.
    unfold PTrieT.T_get in Hget.
    unfold c_loc, key_bits, key_code.
    unfold T_rows_of, T_key_code; time_simpl; time_cbn.
    unfold S.key_bits, key_code in *.
    set (w := N.of_nat (length (rows_of p x) + Pos.size_nat (S.key_code x) + 1)).
    assert (Hwidth : (N.of_nat (Pos.size_nat (S.key_code x) + 1) <= w)%N).
    { unfold w; lia. }
    assert (Hunit : (1 <= w)%N) by (unfold w; lia).
    assert (Hcode' : (S.T_key_code x <= S.c_sys * w)%N).
    { eapply N.le_trans; [exact Hcode|apply N.mul_le_mono_l, Hwidth]. }
    assert (Hget' : (1 + T_trie_get (S.key_code x) (write_index p) <=
      PTrieT.c_trie * w)%N).
    { eapply N.le_trans; [exact Hget|apply N.mul_le_mono_l, Hwidth]. }
    rewrite !N.mul_add_distr_r; lia.
  Qed.

  (** One bits pay for the carry work of consecutive binary increments. *)
  Fixpoint number_credit (id : positive) : N :=
    match id with
    | xH => 1%N
    | xO rest => number_credit rest
    | xI rest => (number_credit rest + 1)%N
    end.

  (** Binary increment consumes at most two units plus released one-bit credit. *)
  Lemma T_succ_credit : forall id,
    (Pos.T_succ id + number_credit (Pos.succ id) <= 2 + number_credit id)%N.
  Proof.
    induction id as [id IH|id IH|]; time_step.
  Qed.

  (** Consecutive numbering has linear total carry work. *)
  Lemma T_number_from_le : forall rs id,
    (T_number_from id rs <= 3 * N.of_nat (length rs) + number_credit id + 1)%N.
  Proof.
    induction rs as [|r rs IH]; intro id.
    - time_step.
    - specialize (IH (Pos.succ id)).
      pose proof (T_succ_credit id) as Hsucc.
      time_step.
  Qed.

  (** A left fold needs callback bounds only for elements that it visits. *)
  Lemma T_fold_left_in : forall A B (f : A -> B -> A) Tf xs acc k,
    (forall state x, In x xs -> (Tf state x <= k)%N) ->
    (List.T_fold_left f Tf xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs; induction xs as [|x xs IH]; intros acc k Hcallback.
    - time_step.
    - pose proof (Hcallback acc x (or_introl eq_refl)) as Hhead.
      pose proof (IH (f acc x) k
        (fun state y Hy => Hcallback state y (or_intror Hy))) as Htail.
      time_step.
  Qed.

  (** A right fold needs callback bounds only for elements that it visits. *)
  Lemma T_fold_right_in : forall A B (f : B -> A -> A) Tf xs acc k,
    (forall x state, In x xs -> (Tf x state <= k)%N) ->
    (List.T_fold_right f Tf acc xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f Tf xs; induction xs as [|x xs IH]; intros acc k Hcallback.
    - time_step.
    - pose proof (Hcallback x (fold_right f acc xs) (or_introl eq_refl)) as Hhead.
      pose proof (IH acc k
        (fun y state Hy => Hcallback y state (or_intror Hy))) as Htail.
      time_step.
  Qed.

  (** Summing bounded occurrence weights costs at most their count times the bound. *)
  Lemma sum_map_le : forall A (f : A -> nat) xs bound,
    (forall x, In x xs -> f x <= bound) ->
    fold_right Nat.add 0 (List.map f xs) <= length xs * bound.
  Proof.
    intros A f xs; induction xs as [|x xs IH]; intros bound Hbound.
    - cbn; lia.
    - pose proof (Hbound x (or_introl eq_refl)) as Hhead.
      specialize (IH bound (fun y Hy => Hbound y (or_intror Hy))).
      cbn [List.map fold_right length]; nia.
  Qed.

  (** Every bit-code in the temporary key set came from an input occurrence. *)
  Lemma key_set_codes : forall xs seen code,
    trie_get code
      (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs seen) = Some tt <->
    In code (List.map key_code xs) \/ trie_get code seen = Some tt.
  Proof.
    induction xs as [|x xs IH]; intros seen code; cbn [fold_left List.map In].
    - tauto.
    - rewrite IH.
      destruct (Pos.eq_dec code (key_code x)) as [Heq|Hneq].
      + subst code; rewrite PTrie.get_set_same; intuition congruence.
      + rewrite PTrie.get_set_other by exact Hneq; intuition congruence.
  Qed.

  (** Enumerated key-set codes occur in the original list of codes. *)
  Lemma key_set_elements_incl : forall xs,
    incl
      (List.map fst (PTrieCode.elements
        (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty)))
      (List.map key_code xs).
  Proof.
    intros xs code Hin.
    apply in_map_iff in Hin as [[stored []] [Heq Hin]].
    cbn [fst] in Heq; subst stored.
    apply PTrie.elements_spec in Hin.
    rewrite key_set_codes, PTrie.get_empty in Hin.
    destruct Hin as [Hin|Hbad]; [exact Hin|discriminate].
  Qed.

  (** Deduplicating keys cannot increase their occurrence count. *)
  Lemma key_set_elements_length : forall xs,
    length (PTrieCode.elements
      (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty)) <=
    length xs.
  Proof.
    intro xs.
    assert (Hlength :
      length (List.map fst (PTrieCode.elements
        (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty))) <=
      length (List.map key_code xs)).
    { eapply NoDup_incl_length.
      - apply PTrie.elements_nodup.
      - apply key_set_elements_incl. }
    now rewrite !length_map in Hlength.
  Qed.

  (** Every enumerated code inherits the declared width bound. *)
  Lemma key_set_elements_bits : forall xs width,
    (forall x, In x xs -> S.key_bits x <= width) ->
    forall entry, In entry (PTrieCode.elements
      (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty)) ->
    Pos.size_nat (fst entry) <= width.
  Proof.
    intros xs width Hbits entry Hin.
    assert (Hcode : In (fst entry) (List.map key_code xs)).
    { apply key_set_elements_incl, in_map, Hin. }
    apply in_map_iff in Hcode as [x [Heq Hx]].
    rewrite <- Heq; exact (Hbits x Hx).
  Qed.

  (** Temporary key-set enumeration is charged to its input occurrences. *)
  Lemma key_set_weight : forall xs width,
    (forall x, In x xs -> S.key_bits x <= width) ->
    PTrieT.weight
      (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty) <=
    length xs * (width + 1).
  Proof.
    intros xs width Hbits.
    pose proof (key_set_elements_length xs) as Hlength.
    unfold PTrieT.weight.
    eapply Nat.le_trans with (m :=
      length (PTrieCode.elements
        (fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty)) * (width + 1)).
    - apply sum_map_le; intros entry Hin.
      pose proof (key_set_elements_bits xs width Hbits entry Hin) as Hwidth; lia.
    - nia.
  Qed.

  (** Building the temporary key set pays once per input key occurrence. *)
  Lemma T_key_set_le : forall xs seen width,
    (forall x, In x xs -> S.key_bits x <= width) ->
    (List.T_fold_left
      (fun acc x => PTrieCode.set (key_code x) tt acc)
      (fun acc x => 1 + (T_key_code x + PTrieCode.T_set (key_code x) tt acc)) xs seen <=
      (S.c_sys + PTrieT.c_trie + 8) * N.of_nat (length xs * (width + 1)) + 1)%N.
  Proof.
    intros xs seen width Hbits.
    assert (Hcallback : forall acc x, In x xs ->
      (1 + (T_key_code x + PTrieCode.T_set (key_code x) tt acc) <=
       (S.c_sys + PTrieT.c_trie + 6) * N.of_nat (width + 1))%N).
    { intros acc x Hin.
      pose proof (T_key_code_le x) as Hcode.
      pose proof (PTrieT.T_set_le unit (key_code x) tt acc) as Hset.
      pose proof (Hbits x Hin) as Hwidth.
      unfold c_sys, key_bits, S.key_bits, key_code in *; nia. }
    pose proof (T_fold_left_in _ _
      (fun acc x => PTrieCode.set (key_code x) tt acc) _ xs seen _ Hcallback) as Hfold.
    rewrite Nat2N.inj_mul; nia.
  Qed.

  (** Writing each distinct bucket pays for its key's lookup and insertion. *)
  Lemma T_bucket_fold_le : forall (entries : list (positive * unit))
      (idx : ptrie (list row)) (r : row) (width : nat),
    (forall entry, In entry entries -> Pos.size_nat (fst entry) <= width) ->
    (List.T_fold_right
      (fun entry acc =>
        let code := fst entry in
        let previous := match trie_get code acc with Some rs => rs | None => nil end in
        PTrieCode.set code (r :: previous) acc)
      (fun entry acc =>
        1 + (Datatypes.T_fst entry +
          (let code := fst entry in
           T_trie_get code acc +
             (let previous := match trie_get code acc with Some rs => rs | None => nil end in
              PTrieCode.T_set code (r :: previous) acc)))) idx entries <=
      (2 * PTrieT.c_trie + 5) * N.of_nat (length entries * (width + 1)) + 1)%N.
  Proof.
    intros entries idx r width Hbits.
    assert (Hcallback : forall entry acc, In entry entries ->
      (1 + (Datatypes.T_fst entry +
        (let code := fst entry in
         T_trie_get code acc +
          (let previous := match trie_get code acc with Some rs => rs | None => nil end in
           PTrieCode.T_set code (r :: previous) acc))) <=
       (2 * PTrieT.c_trie + 3) * N.of_nat (width + 1))%N).
    { intros entry acc Hin.
      pose proof (Hbits entry Hin) as Hwidth.
      pose proof (Datatypes.T_fst_le entry) as Hfst.
      pose proof (PTrieT.T_get_le (list row) (fst entry) acc) as Hget.
      pose proof (PTrieT.T_set_le (list row) (fst entry)
        (r :: match trie_get (fst entry) acc with Some rs => rs | None => nil end) acc)
        as Hset.
      change (1 + T_trie_get (fst entry) acc <=
        PTrieT.c_trie * N.of_nat (Pos.size_nat (fst entry) + 1))%N in Hget.
      cbn zeta; nia. }
    pose proof (T_fold_right_in _ _
      (fun entry acc =>
        let code := fst entry in
        let previous := match trie_get code acc with Some rs => rs | None => nil end in
        PTrieCode.set code (r :: previous) acc) _ entries idx _ Hcallback) as Hfold.
    rewrite Nat2N.inj_mul; nia.
  Qed.

  Definition k_prepare_row : N := (32 * (S.c_sys + PTrieT.c_trie + 1))%N.

  (** One row charges its metadata and all declared write occurrences. *)
  Lemma T_index_row_le : forall p r idx, S.wf p -> In (snd r) (S.rows p) ->
    (T_index_row p r idx <= k_prepare_row *
      (N.of_nat (length (S.deps p (snd r)) + length (S.sides p (snd r)) + 1) *
        N.of_nat (S.kw p + 1) + (S.row_work p 0 + 1)))%N.
  Proof.
    intros p r idx Hwf Hin.
    set (xs := S.target p (snd r) :: S.sides p (snd r)).
    set (keys := fold_left (fun acc x => PTrieCode.set (key_code x) tt acc) xs Empty).
    assert (Hbits : forall x, In x xs -> S.key_bits x <= S.kw p).
    { intros x Hx; eapply S.key_bits_le; [exact Hwf|exact Hin|].
      apply in_or_app; left; exact Hx. }
    pose proof (T_key_set_le xs Empty (S.kw p) Hbits) as Hkeys.
    pose proof (key_set_weight xs (S.kw p) Hbits) as Hweight.
    pose proof (key_set_elements_length xs) as Hlength.
    pose proof (T_bucket_fold_le (PTrieCode.elements keys) idx r (S.kw p)
      (key_set_elements_bits xs (S.kw p) Hbits)) as Hbuckets.
    pose proof (PTrieT.T_elements_le unit keys) as Helements.
    pose proof (S.T_target_le p (snd r) Hwf Hin) as Htarget.
    pose proof (S.T_sides_le p (snd r) Hwf Hin) as Hsides.
    fold keys in Hweight, Hlength.
    unfold k_prepare_row.
    time_unfold T_index_row.
    fold xs keys.
    time_simpl.
    cbn zeta.
    rewrite Nat2N.inj_mul in Hkeys, Hbuckets.
    assert (Hxs : length xs = length (S.sides p (snd r)) + 1) by
      (unfold xs; cbn; lia).
    rewrite Hxs in Hkeys, Hweight, Hlength.
    unfold Datatypes.T_fst in Hbuckets.
    cbn beta iota zeta in Hbuckets.
    set (d := N.of_nat
      (length (S.deps p (snd r)) + length (S.sides p (snd r)) + 1)) in *.
    set (w := N.of_nat (S.kw p + 1)) in *.
    assert (Hside_count : (N.of_nat (length (S.sides p (snd r)) + 1) <= d)%N).
    { unfold d; lia. }
    assert (Hentry_count : (N.of_nat (length (PTrieCode.elements keys)) <= d)%N).
    { unfold d; lia. }
    assert (Hweight' : (N.of_nat (PTrieT.weight keys) <= d * w)%N).
    { unfold d, w; rewrite <- Nat2N.inj_mul; apply time_of_nat_le; nia. }
    assert (Hkeys' :
      (List.T_fold_left
        (fun acc x => PTrieCode.set (key_code x) tt acc)
        (fun acc x => 1 + (T_key_code x + PTrieCode.T_set (key_code x) tt acc)) xs Empty <=
       (S.c_sys + PTrieT.c_trie + 8) * (d * w) + 1)%N).
    { eapply N.le_trans; [exact Hkeys|].
      apply N.add_le_mono_r, N.mul_le_mono_l, N.mul_le_mono_r, Hside_count. }
    assert (Helements' :
      (PTrieT.T_elements keys <= PTrieT.c_trie * (d * w + 1))%N).
    { eapply N.le_trans; [exact Helements|].
      apply N.mul_le_mono_l; rewrite Nat2N.inj_add; cbn [N.of_nat]; lia. }
    assert (Hsides' : (S.T_sides p (snd r) <= S.c_sys * (d * w))%N).
    { eapply N.le_trans; [exact Hsides|].
      rewrite <- N.mul_assoc; apply N.mul_le_mono_l, N.mul_le_mono_r, Hside_count. }
    assert (Hbucket_width :
      ((2 * PTrieT.c_trie + 5) *
        (N.of_nat (length (PTrieCode.elements keys)) * w) + 1 <=
       (2 * PTrieT.c_trie + 5) * (d * w) + 1)%N).
    { apply N.add_le_mono_r, N.mul_le_mono_l, N.mul_le_mono_r, Hentry_count. }
    pose proof (N.le_trans _ _ _ Hbuckets Hbucket_width) as Hbuckets'.
    assert (Hd : (1 <= d)%N) by (unfold d; lia).
    assert (Hw : (1 <= w)%N) by (unfold w; lia).
    assert (Hunit : (1 <= d * w)%N).
    { change (1 * 1 <= d * w)%N; apply N.mul_le_mono; assumption. }
    clear Hkeys Hweight Hlength Helements Hsides Hbuckets Hbucket_width
      Hside_count Hentry_count Hweight' Hbits Hxs Hwf Hin Hd Hw.
    set (u := (d * w)%N) in *; clearbody u.
    clear d w.
    nia.
  Qed.

  (** The outer fold sums actual row occurrences, including duplicates. *)
  Lemma T_numbered_index_le : forall p rs id idx, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (List.T_fold_right (index_row p) (T_index_row p) idx (number_from id rs) <=
      k_prepare_row *
        (N.of_nat (fold_right Nat.add 0%nat
          (List.map (fun r => (length (S.deps p r) + length (S.sides p r) + 1)%nat) rs)) *
          N.of_nat (S.kw p + 1) + N.of_nat (length rs) * (S.row_work p 0 + 1)) +
      N.of_nat (length rs) + 1)%N.
  Proof.
    intros p rs; induction rs as [|r rs IH]; intros id idx Hwf Hlisted.
    - time_step.
    - pose proof (IH (Pos.succ id) idx Hwf
        (fun row Hrow => Hlisted row (or_intror Hrow))) as Htail.
      pose proof (T_index_row_le p (id, r)
        (fold_right (index_row p) idx (number_from (Pos.succ id) rs))
        Hwf (Hlisted r (or_introl eq_refl))) as Hhead.
      cbn [number_from].
      time_step.
  Qed.

  Definition c_idx : N := (64 * (S.c_sys + PTrieT.c_trie + 1))%N.

  (** Preparation keeps the original key-width budget. *)
  Lemma prepare_kw : forall p, kw (prepare p) = S.kw p.
  Proof.
    reflexivity.
  Qed.
  (** Preparation keeps the original row-work budget. *)
  Lemma prepare_row_work : forall p s, row_work (prepare p) s = S.row_work p s.
  Proof.
    reflexivity.
  Qed.

  (** Preparation pays for rows, dependency occurrences and encoded keys. *)
  Lemma T_prepare_le : forall p, S.wf p ->
    (T_prepare p <= c_idx * (
      N.of_nat ((length (S.rows p) +
        fold_right Nat.add 0
          (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
            (S.rows p)) + 1)%nat) *
      N.of_nat (S.kw p + Nat.log2 (length (S.rows p)) + 1) +
      N.of_nat (length (S.rows p)) * (S.row_work p 0 + 1)))%N.
  Proof.
    intros p Hwf.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    pose proof (T_number_from_le (S.rows p) 1%positive) as Hnumber.
    pose proof (T_numbered_index_le p (S.rows p) 1%positive Empty Hwf
      (fun r Hr => Hr)) as Hindex.
    time_unfold T_prepare.
    cbn zeta.
    change (fun r idx => T_index_row p r idx) with (T_index_row p).
    change (T_number_from 1 (S.rows p) <= 3 * N.of_nat (length (S.rows p)) + 1 + 1)%N
      in Hnumber.
    set (count := N.of_nat (length (S.rows p))) in *.
    set (occurrences := N.of_nat (fold_right Nat.add 0%nat
      (List.map (fun r => (length (S.deps p r) + length (S.sides p r) + 1)%nat)
        (S.rows p)))) in *.
    set (width := N.of_nat (S.kw p + Nat.log2 (length (S.rows p)) + 1)).
    set (work := ((count + occurrences + 1) * width +
      count * (S.row_work p 0 + 1))%N).
    assert (Hwidth : (N.of_nat (S.kw p + 1) <= width)%N) by (unfold width; lia).
    assert (Hwidth_pos : (1 <= width)%N) by (unfold width; lia).
    assert (Hcount : (count + 1 <= work)%N).
    { pose proof (N.mul_le_mono_l 1 width (count + occurrences + 1) Hwidth_pos)
        as Hscaled.
      rewrite N.mul_1_r in Hscaled; unfold work; lia. }
    assert (Hrow_work :
      (occurrences * N.of_nat (S.kw p + 1) + count * (S.row_work p 0 + 1) <= work)%N).
    { unfold work; apply N.add_le_mono_r, N.mul_le_mono; [lia|exact Hwidth]. }
    assert (Hrows' : (S.T_rows p <= S.c_sys * work)%N).
    { eapply N.le_trans; [exact Hrows|].
      apply N.mul_le_mono_l; rewrite Nat2N.inj_add; unfold count in Hcount; lia. }
    assert (Hindex' :
      (List.T_fold_right (index_row p) (T_index_row p) Empty
        (number_from 1 (S.rows p)) <= (k_prepare_row + 1) * work)%N).
    { eapply N.le_trans; [exact Hindex|].
      pose proof (N.mul_le_mono_l _ _ k_prepare_row Hrow_work) as Hscaled.
      rewrite N.mul_add_distr_r; lia. }
    assert (Hnumber' : (T_number_from 1 (S.rows p) <= 3 * work)%N) by lia.
    assert (Hunit : (1 <= work)%N) by lia.
    rewrite !Nat2N.inj_add.
    change (1 + (S.T_rows p + T_number_from 1 (S.rows p) +
      List.T_fold_right (index_row p) (T_index_row p) Empty
        (number_from 1 (S.rows p))) <= c_idx * work)%N.
    eapply N.le_trans with (m := ((S.c_sys + k_prepare_row + 5) * work)%N).
    - rewrite !N.mul_add_distr_r in *; lia.
    - apply N.mul_le_mono_r; unfold c_idx, k_prepare_row; lia.
  Qed.
End IndexedT.

(** ** Finite inventory accounting shared by demand and edit *)

Import List.ListNotations.

Definition finite_sum {A} (f : A -> nat) (xs : list A) : nat :=
  fold_right Nat.add 0 (map f xs).

Definition finite_max {A} (f : A -> nat) (xs : list A) : nat :=
  fold_right Nat.max 0 (map f xs).

(** Every member's weight fits the maximum of the list. *)
Lemma finite_max_member : forall A (f : A -> nat) xs x,
  In x xs -> f x <= finite_max f xs.
Proof.
  intros A f xs; induction xs as [|y xs IH]; intros x Hin.
  - contradiction.
  - cbn [finite_max map fold_right]; destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** A bound on every member bounds the maximum of the list. *)
Lemma finite_max_bound : forall A (f : A -> nat) xs n,
  (forall x, In x xs -> f x <= n) -> finite_max f xs <= n.
Proof.
  intros A f xs; induction xs as [|x xs IH]; intros n Hbound.
  - change (0 <= n); apply Nat.le_0_l.
  - cbn [finite_max map fold_right]; apply Nat.max_lub.
    + apply Hbound; now left.
    + apply IH; intros y Hy; apply Hbound; now right.
Qed.

(** Equal summands on the enumerated support have equal sums. *)
Lemma finite_sum_ext : forall A (f g : A -> nat) xs,
  (forall x, In x xs -> f x = g x) -> finite_sum f xs = finite_sum g xs.
Proof.
  intros A f g xs; induction xs as [|x xs IH]; intro Heq; cbn [finite_sum map fold_right].
  - reflexivity.
  - rewrite (Heq x (or_introl eq_refl)); f_equal; apply IH.
    intros y Hy; apply Heq; now right.
Qed.

(** The zero summand has zero total. *)
Lemma finite_sum_zero : forall A (xs : list A), finite_sum (fun _ => 0) xs = 0.
Proof.
  intros A xs; induction xs; cbn [finite_sum map fold_right]; assumption || reflexivity.
Qed.

(** Unit weights count the list length. *)
Lemma finite_sum_one : forall A (xs : list A), finite_sum (fun _ => 1) xs = length xs.
Proof.
  intros A xs; induction xs as [|x xs IH].
  - reflexivity.
  - change (S (finite_sum (fun _ : A => 1) xs) = S (length xs)); now rewrite IH.
Qed.

(** Pointwise addition distributes over finite sums. *)
Lemma finite_sum_plus : forall A (f g : A -> nat) xs,
  finite_sum (fun x => f x + g x) xs = finite_sum f xs + finite_sum g xs.
Proof.
  intros A f g xs; induction xs as [|x xs IH].
  - reflexivity.
  - change ((f x + g x) + finite_sum (fun y => f y + g y) xs =
      (f x + finite_sum f xs) + (g x + finite_sum g xs)).
    rewrite IH; lia.
Qed.

(** The order of two finite sums can be exchanged. *)
Lemma finite_sum_swap : forall A B (f : A -> B -> nat) xs ys,
  finite_sum (fun x => finite_sum (f x) ys) xs =
  finite_sum (fun y => finite_sum (fun x => f x y) xs) ys.
Proof.
  intros A B f xs; induction xs as [|x xs IH]; intro ys.
  - change (0 = finite_sum (fun _ : B => 0) ys); symmetry; apply finite_sum_zero.
  - change (finite_sum (f x) ys + finite_sum (fun a => finite_sum (f a) ys) xs =
      finite_sum (fun y => f x y + finite_sum (fun a => f a y) xs) ys).
    rewrite finite_sum_plus, IH; reflexivity.
Qed.

(** Filtering counts the unit weights of the entries that pass. *)
Lemma filter_length_sum : forall A (test : A -> bool) xs,
  length (filter test xs) = finite_sum (fun x => if test x then 1 else 0) xs.
Proof.
  intros A test xs; induction xs as [|x xs IH]; cbn [filter finite_sum map fold_right].
  - reflexivity.
  - destruct (test x); cbn [length]; rewrite IH; reflexivity.
Qed.

Section Histograms.
  Context {A : Type} (eqb : A -> A -> bool).
  Hypothesis eqb_true : forall x y, eqb x y = true <-> x = y.

  (** An item's histogram count is positive exactly when the item occurs. *)
  Lemma histogram_count_pos : forall x items,
    0 < length (filter (eqb x) items) <-> In x items.
  Proof.
    intros x items; split.
    - intro Hpositive; destruct (filter (eqb x) items) as [|y rest] eqn:Hfilter.
      + cbn in Hpositive; lia.
      + assert (Hin : In y (filter (eqb x) items)) by (rewrite Hfilter; now left).
        apply filter_In in Hin as [Hin Heq].
        apply (proj1 (eqb_true x y)) in Heq; subst y; exact Hin.
    - intro Hin.
      assert (Hfilter : In x (filter (eqb x) items)).
      { apply filter_In; split; [exact Hin|apply (proj2 (eqb_true x x)); reflexivity]. }
      destruct (filter (eqb x) items); cbn in *; [contradiction|lia].
  Qed.

  (** An absent item has zero histogram count. *)
  Lemma histogram_count_zero : forall x items, ~ In x items ->
    length (filter (eqb x) items) = 0.
  Proof.
    intros x items Habsent.
    destruct (length (filter (eqb x) items)) eqn:Hlength; [reflexivity|].
    exfalso; apply Habsent; apply (proj1 (histogram_count_pos x items)); lia.
  Qed.

  (** An absent item contributes no unit weight on a support. *)
  Lemma histogram_unit_absent : forall support x, ~ In x support ->
    finite_sum (fun y => if eqb y x then 1 else 0) support = 0.
  Proof.
    induction support as [|y support IH]; intros x Habsent.
    - reflexivity.
    - change ((if eqb y x then 1 else 0) +
        finite_sum (fun z => if eqb z x then 1 else 0) support = 0).
      destruct (eqb y x) eqn:Heq.
      + apply (proj1 (eqb_true y x)) in Heq; subst y; exfalso; apply Habsent; now left.
      + apply IH; intro Hin; apply Habsent; now right.
  Qed.

  (** A duplicate-free support contributes one unit for each of its members. *)
  Lemma histogram_unit_once : forall support x, NoDup support -> In x support ->
    finite_sum (fun y => if eqb y x then 1 else 0) support = 1.
  Proof.
    intros support x Hnodup; induction Hnodup as [|y support Habsent Hnodup IH]; intro Hin.
    - contradiction.
    - change ((if eqb y x then 1 else 0) +
        finite_sum (fun z => if eqb z x then 1 else 0) support = 1).
      destruct Hin as [->|Hin].
      + rewrite (proj2 (eqb_true x x) eq_refl), histogram_unit_absent;
          [reflexivity|exact Habsent].
      + destruct (eqb y x) eqn:Heq.
        * apply (proj1 (eqb_true y x)) in Heq; subst y; contradiction.
        * apply IH; exact Hin.
  Qed.

  (** Summing a histogram on a duplicate-free support counts every included occurrence. *)
  Lemma histogram_length : forall support items, NoDup support -> incl items support ->
    fold_right Nat.add 0
      (map (fun key => length (filter (eqb key) items)) support) = length items.
  Proof.
    intros support items Hnodup Hincl.
    change (finite_sum (fun key => length (filter (eqb key) items)) support = length items).
    transitivity
      (finite_sum (fun key => finite_sum (fun item => if eqb key item then 1 else 0) items)
        support).
    - apply finite_sum_ext; intros key Hkey; apply filter_length_sum.
    - rewrite finite_sum_swap.
      transitivity (finite_sum (fun _ : A => 1) items).
      + apply finite_sum_ext; intros item Hitem; apply histogram_unit_once;
          [exact Hnodup|apply Hincl; exact Hitem].
      + apply finite_sum_one.
  Qed.
End Histograms.

(** Mapping a finite support composes its weight function. *)
Lemma finite_sum_map : forall A B (f : B -> nat) (g : A -> B) xs,
  finite_sum f (map g xs) = finite_sum (fun x => f (g x)) xs.
Proof.
  intros A B f g xs; unfold finite_sum; now rewrite map_map.
Qed.

(** A conditional fold is a sum of conditional nonnegative weights. *)
Lemma finite_fold_choice : forall A (test : A -> bool) (weight : A -> nat) xs,
  fold_right (fun x n => if test x then weight x + n else n) 0 xs =
    finite_sum (fun x => if test x then weight x else 0) xs.
Proof.
  intros A test weight xs; induction xs as [|x xs IH].
  - reflexivity.
  - cbn [fold_right finite_sum map]; destruct (test x); now rewrite IH.
Qed.

(** An absent identifier contributes nothing to an inventory sum. *)
Lemma selected_sum_miss : forall A (weight : A -> nat) xs id,
  ~ In id (map fst xs) ->
  finite_sum (fun entry => if Pos.eqb id (fst entry) then weight (snd entry) else 0) xs = 0.
Proof.
  intros A weight xs; induction xs as [|[q a] xs IH]; intros id Habsent.
  - reflexivity.
  - change ((if Pos.eqb id q then weight a else 0) +
      finite_sum (fun entry => if Pos.eqb id (fst entry)
        then weight (snd entry) else 0) xs = 0).
    destruct (Pos.eqb id q) eqn:Heq.
    + apply Pos.eqb_eq in Heq; subst q; exfalso; apply Habsent; now left.
    + apply IH; intro Hin; apply Habsent; now right.
Qed.

(** A unique listed identifier contributes precisely its stored payload weight. *)
Lemma selected_sum_hit : forall A (weight : A -> nat) xs id a,
  NoDup (map fst xs) -> In (id, a) xs ->
  finite_sum (fun entry => if Pos.eqb id (fst entry) then weight (snd entry) else 0) xs =
    weight a.
Proof.
  intros A weight xs; induction xs as [|[q b] xs IH]; intros id a Hnodup Hin.
  - contradiction.
  - inversion Hnodup as [|? ? Habsent Htail]; subst.
    change ((if Pos.eqb id q then weight b else 0) +
      finite_sum (fun entry => if Pos.eqb id (fst entry)
        then weight (snd entry) else 0) xs = weight a).
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst q b; rewrite Pos.eqb_refl.
      rewrite selected_sum_miss by exact Habsent; lia.
    + assert (Hneq : Pos.eqb id q = false).
      { apply Pos.eqb_neq; intro Heq; subst q; apply Habsent.
        apply in_map_iff; exists (id, a); auto. }
      rewrite Hneq; apply IH; assumption.
Qed.

(** A trie inventory sum selected by one identifier is its lookup weight. *)
Lemma trie_selected_sum : forall A (m : PTrieCode.t A) id (weight : A -> nat),
  finite_sum
    (fun entry => if Pos.eqb id (fst entry) then weight (snd entry) else 0)
    (PTrieCode.elements m) =
  match PTrieCode.get id m with Some a => weight a | None => 0 end.
Proof.
  intros A m id weight; destruct (PTrieCode.get id m) as [a|] eqn:Hget.
  - apply selected_sum_hit; [apply PTrie.elements_nodup|].
    now apply PTrie.elements_spec.
  - apply selected_sum_miss; intros Hin.
    apply in_map_iff in Hin as [[q a] [Heq Hin]]; cbn in Heq; subst q.
    apply PTrie.elements_spec in Hin; rewrite Hget in Hin; discriminate Hin.
Qed.
