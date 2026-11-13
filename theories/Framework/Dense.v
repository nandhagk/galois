(** * Dense dataflow systems

    Dense rows seed boundary facts and transfer them along graph edges.
    For example, a forward flow reads its source and contributes to its destination.
    Builds on: Framework.DenseSig, Fixpoint.SystemSig and Program.SemanticsSig. *)

From Stdlib Require Import List Relation_Operators Bool PeanoNat NArith Lia.
From Argent Require Import Loop Time Tactics Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import DenseSig.
Import List.ListNotations.

Module DenseCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    <: SYSTEM_OPS L.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition key_eqb := N.eqb.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with
    | Seed n => n
    | Flow e => match T.dir with Forward => C.dst p e | Backward => C.src p e end
    end.
  Definition start p (r : row) : query key L.t frame :=
    match r with
    | Seed n => Ret (T.boundary p n)
    | Flow e => Ask (match T.dir with Forward => C.src p e | Backward => C.dst p e end) e
    end.
  Definition resume p (e : frame) a : query key L.t frame := Ret (T.transfer p e a).
  Definition deps p (r : row) : list key :=
    match r with
    | Seed _ => []
    | Flow e => [match T.dir with Forward => C.src p e | Backward => C.dst p e end]
    end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End DenseCode.

Module Dense (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    <: SYSTEM L <: DENSE_SYSTEM P N E C L T.
  Include DenseCode P N E C L T.
  Include SYSTEM_SPEC L.

  Definition wf (_ : prog) := True.

  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. exact N.encode_inj. Qed.

  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact N.eqb_spec.
  Qed.

  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [a|e] look [|[|n]] q acc x f _ _ Hrun Hask;
      cbn [loop_fuel start eval_step peel resume fst snd] in Hrun;
      try discriminate; inversion Hrun; subst;
      cbn [peel fst] in Hask; try discriminate.
    inversion Hask; subst; cbn [deps]; left; reflexivity.
  Qed.

  Lemma eval_total : forall p r look, wf p -> In r (rows p) -> eval p r look <> None.
  Proof. intros p [n|e] look _ _; discriminate. Qed.

  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [n|e] s u _ _ Hread; [reflexivity|].
    change (Some (T.transfer p e (s (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), (@nil (key * L.t))) = Some (T.transfer p e (u (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), (@nil (key * L.t)))).
    rewrite Hread by (simpl; auto); reflexivity.
  Qed.

  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [n|e] look a ss x b _ _ Heval Hin;
      unfold eval, deps, start, resume in Heval; simpl in Heval;
      inversion Heval; subst; contradiction.
  Qed.

  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p [n|e] look a ss _ _ Heval;
      unfold eval, deps, start, resume in Heval; simpl in Heval;
      inversion Heval; subst; reflexivity.
  Qed.

  Lemma rows_spec : forall p, rows p = map Seed (C.entries p) ++ map Flow (C.edges p).
  Proof. reflexivity. Qed.
  Lemma target_seed : forall p n, target p (Seed n) = n.
  Proof. reflexivity. Qed.
  Lemma target_flow : forall p e, target p (Flow e) =
    match T.dir with Forward => C.dst p e | Backward => C.src p e end.
  Proof. reflexivity. Qed.
  Lemma eval_seed : forall p n look, eval p (Seed n) look = Some (T.boundary p n, nil).
  Proof. reflexivity. Qed.
  Lemma eval_flow : forall p e look, eval p (Flow e) look = Some
    (T.transfer p e (look (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), nil).
  Proof. reflexivity. Qed.
End Dense.

Module DenseSound (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P) (K : FLOW_LINK P N E C L T M).
  Module S := Dense P N E C L T.
  Include Dense P N E C L T.
  Module Sound <: DENSE_SOUND P N E C L T S M K.
  (** A forward post-solution contains each reachable concrete state. *)
  Lemma covers : forall p look, T.dir = Forward -> post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> K.gamma (look (K.point s)) s.
  Proof.
    intros p look Hdir Hpost s Hreach.
    induction Hreach as [s Hinitial|s t Hreach IH Hstep].
    - destruct (K.init_sound p s Hinitial) as [Hentry Hgamma].
      assert (Hrow : In (Seed (K.point s)) (rows p)).
      { unfold rows; apply in_or_app; left; apply in_map; exact Hentry. }
      specialize (Hpost _ Hrow).
      rewrite eval_seed, target_seed in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      exact (K.gamma_mono _ _ _ Hpost Hgamma).
    - destruct (K.step_sound p s t _ Hreach Hstep IH)
        as [e [Hedge [Hsrc [Hdst Hgamma]]]].
      assert (Hrow : In (Flow e) (rows p)).
      { unfold rows; apply in_or_app; right; apply in_map; exact Hedge. }
      specialize (Hpost _ Hrow).
      rewrite eval_flow, target_flow, Hdir, Hsrc, Hdst in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      exact (K.gamma_mono _ _ _ Hpost Hgamma).
  Qed.
  End Sound.
  Include Sound.
End DenseSound.

Module DenseBackwardSound (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P) (K : BACKWARD_LINK P N E C L T M).
  Module S := Dense P N E C L T.
  Include Dense P N E C L T.
  Module Sound <: DENSE_BACKWARD_SOUND P N E C L T S M K.
  (** Backward post-solutions cover finite suffixes ending at a terminal state. *)
  Lemma covers_backward : forall p look, T.dir = Backward -> post_solution p look ->
    forall s t, clos_refl_trans M.state (M.step p) s t -> K.terminal p t ->
      K.gamma (look (K.point s)) s.
  Proof.
    intros p look Hdir Hpost s t Hpath Hterminal.
    assert (Hend : K.gamma (look (K.point t)) t).
    { destruct (K.terminal_sound p t Hterminal) as [Hentry Hgamma].
      assert (Hrow : In (Seed (K.point t)) (rows p)).
      { unfold rows; apply in_or_app; left; apply in_map; exact Hentry. }
      specialize (Hpost _ Hrow).
      rewrite eval_seed, target_seed in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      exact (K.gamma_mono _ _ _ Hpost Hgamma). }
    clear Hterminal; revert Hend.
    induction Hpath as [s t Hstep|s|s u t Hleft IHleft Hright IHright]; intro Hgamma.
    - destruct (K.step_sound p s t _ Hstep Hgamma)
        as [e [Hedge [Hsrc [Hdst Htransfer]]]].
      assert (Hrow : In (Flow e) (rows p)).
      { unfold rows; apply in_or_app; right; apply in_map; exact Hedge. }
      specialize (Hpost _ Hrow).
      rewrite eval_flow, target_flow, Hdir, Hsrc, Hdst in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      exact (K.gamma_mono _ _ _ Hpost Htransfer).
    - exact Hgamma.
    - apply IHleft; apply IHright; exact Hgamma.
  Qed.
  End Sound.
  Include Sound.
End DenseBackwardSound.

Module DenseT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (L : LATTICE_T) (T : FLOW_T P N E L)
    <: DENSE_T P N E C L T.
  Include Dense P N E C L T.
  Definition row_work := T.flow_work.
  Definition kw (p : prog) : nat := fold_right Nat.max 0
    (List.map N.bits (C.entries p ++
      flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))).
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  Definition c_sys : N := (N.c_key + 2 * C.c_cfg + T.c_flow + 10)%N.
  (** Step budgets grow with the size of abstract values. *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof.
    exact T.flow_work_mono.
  Qed.

  (** Each listed key fits the maximum of the list's code widths. *)
  Local Lemma bits_max : forall xs x, In x xs ->
    N.bits x <= fold_right Nat.max 0 (map N.bits xs).
  Proof.
    induction xs as [|y xs IH]; intros x Hin; [contradiction|].
    cbn [map fold_right]; destruct Hin as [<-|Hin].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.
  (** The program key budget covers all declared reads and writes. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p [n|e] x _ Hrow Hkey; unfold key_bits, key_code, kw.
    all: apply bits_max; unfold rows in Hrow;
      apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
      apply in_map_iff in Hrow; destruct Hrow as [r [Heq Hin]];
      inversion Heq; subst.
    - cbn [writes sides target deps app] in Hkey.
      destruct Hkey as [<-|[]]; apply in_or_app; left; exact Hin.
    - apply in_or_app; right; apply in_flat_map; exists e; split; [exact Hin|].
      cbn [writes sides target deps app] in Hkey.
      destruct T.dir; cbn in Hkey; cbn; tauto.
  Qed.
  (** Encoding costs are linear in the resulting code size. *)
  Lemma T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intro x; time_unfold T_key_code.
    pose proof (N.T_encode_le x) as Htime.
    change (T_key_code x <= c_sys * N.of_nat (N.bits x + 1))%N.
    unfold T_key_code, c_sys; nia.
  Qed.
  (** Equality costs are bounded by the first key's code size. *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros a b; time_unfold T_key_eqb.
    pose proof (N.T_eqb_le a b) as Htime.
    unfold c_sys, key_bits, key_code; unfold N.bits in Htime; nia.
  Qed.
  (** Enumerating rows costs linear time in the output length. *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Target lookup fits the row budget. *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Starting a row fits the row budget. *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Resuming a frame that a listed row reaches pays for the sizes of the lookup values. *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Dependency enumeration pays for every key occurrence. *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Side enumeration pays for every key occurrence. *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Row output sizes fit the transfer budget. *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof. Admitted. (* STUB *)
End DenseT.
