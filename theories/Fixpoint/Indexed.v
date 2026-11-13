(** * Prepared row indexes

    Preparation numbers rows and indexes their declared writes.
    For example, repeated writes by one row occupy one index entry per key.
    Builds on: Fixpoint.IndexedSig and Base.Trie. *)

From Stdlib Require Import List PArith Arith NArith Bool Lia.
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

  Definition c_idx : N := 1. (* STUB *)

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

  Lemma T_prepare_le : forall p, S.wf p ->
    (T_prepare p <= c_idx * (
      N.of_nat ((length (S.rows p) +
        fold_right Nat.add 0
          (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1)
            (S.rows p)) + 1)%nat) *
      N.of_nat (S.kw p + Nat.log2 (length (S.rows p)) + 1) +
      N.of_nat (length (S.rows p)) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)
End IndexedT.
