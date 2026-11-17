(** * Abstract interpretation of ordered actions

    Interpreter rows apply abstract assignments, havoc and guards in source order.
    For example, a guard after an assignment observes the assigned value.

    Main results
    - [rows_complexity] Listing the rows is linear in their number, O(n) for n rows.
    - [start_complexity] Starting a row is linear in the row budget at the empty value.
    - [deps_complexity] Listing the dependencies of a row is linear in their number times
      the key width.
    - [target_complexity] The target of a listed row fits the row budget at the empty value.
    - [sides_complexity] Listing the sides of a row is linear in their number times the key
      width.

    Builds on: Framework.InterpSig, States.StateSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List Bool PeanoNat NArith Lia.
From Argent Require Import Time Tactics Std Loop Complexity.
Import ComplexityNotations.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import DenseSig InterpSig.
Import List.ListNotations.

Module InterpCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN_OPS X L V) <: SYSTEM_OPS D.
  Definition prog := P.t.
  Definition key := N.t.
  Definition row := dense_row N.t E.t.
  Definition frame := E.t.
  Definition key_code := N.encode.
  Definition key_eqb := N.eqb.
  Definition rows p : list row := map Seed (C.entries p) ++ map Flow (C.edges p).
  Definition target p (r : row) : key :=
    match r with Seed n => n | Flow e => C.dst p e end.
  Definition start p (r : row) : query key D.t frame :=
    match r with Seed _ => Ret D.top | Flow e => Ask (C.src p e) e end.
  Definition resume p (e : frame) st : query key D.t frame :=
    Ret (fold_left (fun st a =>
      match a with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) (A.actions p e) st).
  Definition deps p (r : row) : list key :=
    match r with Seed _ => [] | Flow e => [C.src p e] end.
  Definition sides (_ : prog) (_ : row) : list key := [].
End InterpCode.

Module Interp (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN X L V)
    <: SYSTEM D <: INTERP_SYSTEM P N E C X L V A D.
  Include InterpCode P N E C X L V A D.
  Include SYSTEM_SPEC D.

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
    assert (Hsrc : s (C.src p e) = u (C.src p e)) by (apply Hread; simpl; auto).
    unfold eval, deps, start, resume, eval_query, eval_step; simpl; now rewrite Hsrc.
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
  Lemma target_flow : forall p e, target p (Flow e) = C.dst p e.
  Proof. reflexivity. Qed.
  Lemma eval_seed : forall p n look, eval p (Seed n) look = Some (D.top, nil).
  Proof. reflexivity. Qed.
  Lemma eval_flow : forall p e look, eval p (Flow e) look = Some
    (fold_left (fun st a =>
      match a with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) (A.actions p e) (look (C.src p e)), nil).
  Proof. reflexivity. Qed.
End Interp.

Module InterpSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (A : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) (M : SEMANTICS P) (K : INTERP_LINK P N E C X L A M).
  Module S := Interp P N E C X L V A D.
  Include Interp P N E C X L V A D.
  Module Sound <: INTERP_SOUND P N E C X L V A D S M K.

  (** An ordered abstract fold contains every endpoint of its concrete actions. *)
  Local Lemma actions_sound : forall st acts out a,
    exec_all L.eval L.holds X.eqb st acts out -> D.gamma a st ->
    D.gamma (fold_left (fun st act =>
      match act with
      | Assign x ex => D.assign x ex st
      | Havoc x => D.havoc x st
      | Assume g es => D.assume g es st
      end) acts a) out.
  Proof.
    intros st acts out a Hexec; revert a.
    induction Hexec as [st|st act mid acts out Hfirst Htail IH]; intros a Hgamma.
    - exact Hgamma.
    - cbn [fold_left]; apply IH.
      destruct Hfirst as [st x ex v Heval|st x v|st g es vs Heval Hguard].
      + eapply D.assign_sound; eassumption.
      + apply D.havoc_sound; exact Hgamma.
      + eapply D.assume_sound; eassumption.
  Qed.

  (** A post-solution contains the store of every reachable concrete state. *)
  Lemma covers : forall p look, post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> D.gamma (look (K.point s)) (K.store s).
  Proof.
    intros p look Hpost s Hreach.
    induction Hreach as [s Hinitial|s t Hreach IH Hstep].
    - assert (Hrow : In (Seed (K.point s)) (rows p)).
      { unfold rows; apply in_or_app; left; apply in_map.
        exact (K.init_entry p s Hinitial). }
      specialize (Hpost _ Hrow).
      rewrite eval_seed, target_seed in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      eapply D.gamma_mono; [exact Hpost|apply D.gamma_top].
    - destruct (K.step_edge p s t Hstep) as [e [Hedge [Hsrc [Hdst Hexec]]]].
      assert (Hrow : In (Flow e) (rows p)).
      { unfold rows; apply in_or_app; right; apply in_map; exact Hedge. }
      specialize (Hpost _ Hrow).
      rewrite eval_flow, target_flow, Hsrc, Hdst in Hpost.
      cbn [row_ok forallb] in Hpost; rewrite Bool.andb_true_r in Hpost.
      eapply D.gamma_mono; [exact Hpost|].
      eapply actions_sound; [exact Hexec|exact IH].
  Qed.
  End Sound.
  Include Sound.
End InterpSound.

Module InterpT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V)
    (B : INTERP_ENVELOPE P E X L V A D) <: INTERP_T P N E C X L V A D B.
  Include Interp P N E C X L V A D.
  Include INTERP_COST_SPEC P N E C X L V A D B.
  Definition row_work := interp_work.
  Definition kw := interp_kw.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  Definition c_sys : N := (N.c_key + 2 * C.c_cfg + A.c_actions + D.c_state + 20)%N.

  Definition apply_action (st : D.t) (act : action L.op L.guard X.t) : D.t :=
    match act with
    | Assign x ex => D.assign x ex st
    | Havoc x => D.havoc x st
    | Assume g es => D.assume g es st
    end.
  TimeFun apply_action.

  Definition apply_actions (acts : list (action L.op L.guard X.t)) (st : D.t) : D.t :=
    fold_left apply_action acts st.
  TimeFun apply_actions.

  Definition c_fold : N := (D.c_state + 3)%N.

  (** Enlarging the initial size enlarges the iterated size envelope. *)
  Local Lemma state_extent_mono : forall p n s t, s <= t ->
    state_extent p n s <= state_extent p n t.
  Proof.
    intros p n; induction n as [|n IH]; intros s t Hle; cbn [state_extent].
    - exact Hle.
    - apply IH; apply Nat.max_le_compat; [exact Hle|].
      apply B.next_size_mono; exact Hle.
  Qed.

  (** The size envelope includes the initial state even when no action runs. *)
  Local Lemma state_extent_ge : forall p n s, s <= state_extent p n s.
  Proof.
    intros p n; induction n as [|n IH]; intro s; cbn [state_extent].
    - reflexivity.
    - eapply Nat.le_trans; [apply Nat.le_max_l|apply IH].
  Qed.

  (** The work envelope grows with its initial state-size bound. *)
  Local Lemma fold_work_mono : forall p n s t, s <= t ->
    (fold_work p n s <= fold_work p n t)%N.
  Proof.
    intros p n; induction n as [|n IH]; intros s t Hle.
    - reflexivity.
    - pose proof (B.primitive_work_mono p s t Hle) as Hwork.
      assert (Hnext : Nat.max s (B.next_size p s) <= Nat.max t (B.next_size p t)).
      { apply Nat.max_le_compat; [exact Hle|apply B.next_size_mono; exact Hle]. }
      specialize (IH _ _ Hnext); cbn [fold_work]; lia.
  Qed.

  (** Every fold budget pays for its final empty-list call. *)
  Local Lemma fold_work_pos : forall p n s, (1 <= fold_work p n s)%N.
  Proof.
    intros p n; induction n as [|n IH]; intro s.
    - reflexivity.
    - specialize (IH (Nat.max s (B.next_size p s))); cbn [fold_work]; lia.
  Qed.

  (** A listed action's output fits the primitive size envelope. *)
  Local Lemma apply_action_size : forall p e act st s,
    In act (A.actions p e) -> D.size st <= s ->
    D.size (apply_action st act) <= B.next_size p s.
  Proof.
    intros p e [x ex|x|g es] st s Hact Hsize; unfold apply_action.
    - eapply B.assign_size_le; eassumption.
    - eapply B.havoc_size_le; eassumption.
    - eapply B.assume_size_le; eassumption.
  Qed.

  (** A listed action's derived time fits the primitive work envelope. *)
  Local Lemma T_apply_action_le : forall p e act st s,
    In act (A.actions p e) -> D.size st <= s ->
    (T_apply_action st act <= (D.c_state + 1) * (B.primitive_work p s + 1))%N.
  Proof.
    intros p e [x ex|x|g es] st s Hact Hsize.
    - pose proof (B.assign_work_le p e x ex st s Hact Hsize) as Hwork; time_step.
    - pose proof (B.havoc_work_le p e x st s Hact Hsize) as Hwork; time_step.
    - pose proof (B.assume_work_le p e g es st s Hact Hsize) as Hwork; time_step.
  Qed.

  (** A bounded list of listed actions stays inside the iterated size envelope. *)
  Local Lemma apply_actions_size : forall p e n acts st s,
    length acts <= n -> incl acts (A.actions p e) -> D.size st <= s ->
    D.size (apply_actions acts st) <= state_extent p n s.
  Proof.
    intros p e n; induction n as [|n IH]; intros [|act acts] st s Hlen Hin Hsize.
    - exact Hsize.
    - cbn [length] in Hlen; lia.
    - eapply Nat.le_trans; [exact Hsize|apply state_extent_ge].
    - change (D.size (apply_actions acts (apply_action st act)) <=
        state_extent p n (Nat.max s (B.next_size p s))).
      apply IH.
      + cbn [length] in Hlen; lia.
      + intros a Ha; apply Hin; right; exact Ha.
      + eapply Nat.le_trans; [eapply apply_action_size|apply Nat.le_max_r].
        * apply Hin; left; reflexivity.
        * exact Hsize.
  Qed.

  (** A bounded list of listed actions fits the iterated derived-time envelope. *)
  Local Lemma T_apply_actions_le : forall p e n acts st s,
    length acts <= n -> incl acts (A.actions p e) -> D.size st <= s ->
    (T_apply_actions acts st <= c_fold * fold_work p n s)%N.
  Proof.
    intros p e n; induction n as [|n IH]; intros [|act acts] st s Hlen Hin Hsize.
    - unfold c_fold; time_unfold T_apply_actions; time_unfold List.T_fold_left;
        time_cbn; lia.
    - cbn [length] in Hlen; lia.
    - pose proof (fold_work_pos p (S n) s) as Hwork.
      unfold c_fold; time_unfold T_apply_actions; time_unfold List.T_fold_left;
        time_cbn; nia.
    - assert (Hact : In act (A.actions p e)) by (apply Hin; left; reflexivity).
      assert (Hnext : D.size (apply_action st act) <= Nat.max s (B.next_size p s)).
      { eapply Nat.le_trans; [eapply apply_action_size; eassumption|apply Nat.le_max_r]. }
      assert (Hlen1 : length acts <= n) by (cbn [length] in Hlen; lia).
      assert (Hin1 : incl acts (A.actions p e)) by
        (intros a Ha; apply Hin; right; exact Ha).
      specialize (IH acts (apply_action st act) _ Hlen1 Hin1 Hnext).
      pose proof (T_apply_action_le p e act st s Hact Hsize) as Hact_time.
      unfold T_apply_actions in IH.
      time_unfold T_apply_actions; time_unfold List.T_fold_left; time_cbn.
      unfold c_fold in *; nia.
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

  (** Step budgets grow with the size of abstract values. *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof.
    intros p s s' Hle.
    pose proof (state_extent_mono p (max_actions p) s s' Hle) as Hsize.
    pose proof (fold_work_mono p (max_actions p) s s' Hle) as Hwork.
    unfold row_work, interp_work; lia.
  Qed.
  (** The program key budget covers all declared reads and writes. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p [n|e] x _ Hrow Hkey; unfold key_bits, key_code, kw, interp_kw.
    all: apply bits_max; unfold rows in Hrow;
      apply in_app_or in Hrow; destruct Hrow as [Hrow|Hrow];
      apply in_map_iff in Hrow; destruct Hrow as [r [Heq Hin]];
      inversion Heq; subst.
    - cbn [writes sides target deps app] in Hkey.
      destruct Hkey as [<-|[]]; apply in_or_app; left; exact Hin.
    - apply in_or_app; right; apply in_flat_map; exists e; split; [exact Hin|].
      cbn [writes sides target deps app] in Hkey; cbn in Hkey; cbn; tauto.
  Qed.
  (** Encoding costs are linear in the resulting code size. *)
  Lemma T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intro x; time_unfold T_key_code.
    pose proof (N.T_encode_le x) as Htime.
    unfold c_sys, key_bits, key_code; unfold N.bits in Htime; nia.
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
  Proof.
    intros p _; unfold c_sys; time_step.
    pose proof (ListDef.T_map_le (@Seed N.t E.t) (fun _ => 1%N) 1%N
      (C.entries p) (fun _ => N.le_refl 1)) as Hseed.
    pose proof (ListDef.T_map_le (@Flow N.t E.t) (fun _ => 1%N) 1%N
      (C.edges p) (fun _ => N.le_refl 1)) as Hflow.
    unfold rows; rewrite length_app; rewrite !length_map in *; nia.
  Qed.
  (** Target lookup fits the row budget. *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [n|e] _ _; unfold c_sys; time_step.
  Qed.
  (** Starting a row fits the row budget. *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [n|e] _ _; unfold c_sys; time_step.
  Qed.
  (** Resuming a frame that a listed row reaches pays for the sizes of the lookup values. *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, D.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p r look s n q acc x f _ _ Hsize _ _.
    pose proof (T_apply_actions_le p f (max_actions p) (A.actions p f) (look x) s
      (B.actions_length_le p f) (incl_refl _) (Hsize x)) as Hfold.
    pose proof (A.T_actions_le p f) as Hactions.
    pose proof (B.actions_length_le p f) as Hlen.
    time_unfold T_resume; time_cbn.
    unfold T_apply_actions, T_apply_action, apply_action in Hfold.
    unfold c_sys, c_fold, row_work, interp_work, max_actions in *; nia.
  Qed.
  (** Dependency enumeration pays for every key occurrence. *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof.
    intros p [n|e] _ _; unfold c_sys; time_step.
  Qed.
  (** Side enumeration pays for every key occurrence. *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof.
    intros p r _ _; unfold c_sys; time_step.
  Qed.
  (** Row output sizes fit the transfer budget. *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, D.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (D.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (D.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p [n|e] look s a ss _ _ Hsize Heval.
    - rewrite eval_seed in Heval; inversion Heval; subst; split; [|constructor].
      unfold row_work, interp_work; lia.
    - rewrite eval_flow in Heval; inversion Heval; subst; split; [|constructor].
      pose proof (apply_actions_size p e (max_actions p) (A.actions p e)
        (look (C.src p e)) s (B.actions_length_le p e) (incl_refl _)
        (Hsize (C.src p e))) as Hfold.
      change (D.size (apply_actions (A.actions p e) (look (C.src p e))) <=
        state_extent p (max_actions p) s) in Hfold.
      unfold apply_actions, apply_action in Hfold.
      unfold row_work, interp_work; lia.
  Qed.
  (** Listing the rows is linear in their number. *)
  Lemma rows_complexity : T_rows p ∈ 𝑂(N.of_nat (length (rows p))) for p | wf p.
  Proof.
    eapply bigO_intro with (c := c_sys).
    intros p Hwf.
    change (T_rows p <= c_sys * N.of_nat (length (rows p)) + c_sys)%N.
    pose proof (T_rows_le p Hwf) as Htime.
    rewrite Nat2N.inj_add in Htime; nia.
  Qed.

  (** Starting a listed row fits its work budget at the empty value. *)
  Lemma start_complexity :
    T_start p r ∈ 𝑂(row_work p 0) for (p, r) | wf p /\ In r (rows p).
  Proof.
    eapply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_start p r <= c_sys * row_work p 0 + c_sys)%N.
    pose proof (T_start_le p r Hwf Hrow) as Htime; nia.
  Qed.

  (** Listing dependencies is linear in their number times the key width. *)
  Lemma deps_complexity :
    T_deps p r ∈ 𝑂(N.of_nat ((length (deps p r) + 1) * (kw p + 1)))
      for (p, r) | wf p /\ In r (rows p).
  Proof.
    eapply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_deps p r <=
      c_sys * N.of_nat ((length (deps p r) + 1) * (kw p + 1)) + c_sys)%N.
    pose proof (T_deps_le p r Hwf Hrow) as Htime.
    rewrite Nat2N.inj_mul; nia.
  Qed.

  (** Finding a listed row's target fits its work budget at the empty value. *)
  Lemma target_complexity :
    T_target p r ∈ 𝑂(row_work p 0) for (p, r) | wf p /\ In r (rows p).
  Proof.
    eapply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_target p r <= c_sys * row_work p 0 + c_sys)%N.
    pose proof (T_target_le p r Hwf Hrow) as Htime; nia.
  Qed.

  (** Listing side writes is linear in their number times the key width. *)
  Lemma sides_complexity :
    T_sides p r ∈ 𝑂(N.of_nat ((length (sides p r) + 1) * (kw p + 1)))
      for (p, r) | wf p /\ In r (rows p).
  Proof.
    eapply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_sides p r <=
      c_sys * N.of_nat ((length (sides p r) + 1) * (kw p + 1)) + c_sys)%N.
    pose proof (T_sides_le p r Hwf Hrow) as Htime.
    rewrite Nat2N.inj_mul; nia.
  Qed.
End InterpT.
