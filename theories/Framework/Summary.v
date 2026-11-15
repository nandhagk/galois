(** * Function summary constraints

    Local rows and call rows compute summary contributions.
    For example, a call row emits its callee entry as a side contribution.
    Builds on: Framework.SummarySig and Fixpoint.Query. *)

From Stdlib Require Import List Bool NArith Lia.
From Argent Require Import Time Std Loop.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CallsSig SemanticsSig.
From Galois.Framework Require Import SummarySig.

Module SummaryCode (P : TYPE) (F Site : KEY_OPS) (CL : CALLS_OPS P F Site)
    (L : LATTICE_OPS) (B : BODY_OPS P F Site L) <: SUMMARY_OPS P F Site L.
  Definition prog := P.t.
  Definition key := F.t.
  Definition row := summary_row F.t Site.t.
  Definition frame := (Site.t * F.t)%type.
  Definition key_code := F.encode.
  Definition key_eqb := F.eqb.
  Definition rows p : list row := map SummaryLocal (CL.functions p) ++
    map (fun sg => SummaryCall (fst sg) (snd sg)) (CL.calls p).
  Definition target p (r : row) : key := match r with
    | SummaryLocal f => f
    | SummaryCall site _ => CL.caller_of p site
    end.
  Definition start p (r : row) : query key L.t frame := match r with
    | SummaryLocal f => Ret (B.local p f)
    | SummaryCall site g => Side g (B.entry p site g) (Ask g (site, g))
    end.
  Definition resume p (f : frame) a : query key L.t frame :=
    Ret (B.via_call p (fst f) (snd f) a).
  Definition deps (_ : prog) (r : row) : list key := match r with
    | SummaryLocal _ => nil
    | SummaryCall _ g => g :: nil
    end.
  Definition sides (_ : prog) (r : row) : list key := match r with
    | SummaryLocal _ => nil
    | SummaryCall _ g => g :: nil
    end.
End SummaryCode.

Module Summary (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L) <: SUMMARY P F Site CL L B.
  Include SummaryCode P F Site CL L B.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := CL.wf p.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    exact F.encode_inj.
  Qed.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact F.eqb_spec.
  Qed.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p [f|site g] look Hwf Hr; discriminate.
  Qed.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [f|site g] s u Hwf Hr Hagree; [reflexivity|].
    change (Some (B.via_call p site g (s g), (g, B.entry p site g) :: nil) =
      Some (B.via_call p site g (u g), (g, B.entry p site g) :: nil)).
    rewrite (Hagree g (or_introl eq_refl)); reflexivity.
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [g|site g] look [|[|n]] q acc x f Hwf Hr Hloop Hpeel;
      cbn [start resume eval_step peel loop_fuel fst snd] in Hloop;
      try discriminate;
      injection Hloop as <- <-;
      cbn [peel fst snd] in Hpeel; try discriminate.
    injection Hpeel as <- <-; now left.
  Qed.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [f|site g] look a ss x b Hwf Hr Heval Hin.
    - change (Some (B.local p f, nil) = Some (a, ss)) in Heval.
      injection Heval as <- <-; contradiction.
    - change (Some (B.via_call p site g (look g), (g, B.entry p site g) :: nil) =
        Some (a, ss)) in Heval.
      injection Heval as <- <-; destruct Hin as [Heq|[]].
      injection Heq as <- <-; now left.
  Qed.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p [f|site g] look a ss Hwf Hr Heval.
    - change (Some (B.local p f, nil) = Some (a, ss)) in Heval.
      injection Heval as <- <-; reflexivity.
    - change (Some (B.via_call p site g (look g), (g, B.entry p site g) :: nil) =
        Some (a, ss)) in Heval.
      injection Heval as <- <-; reflexivity.
  Qed.
  (** Function keys use the client's encoding. *)
  Lemma key_code_spec : key_code = F.encode.
  Proof.
    reflexivity.
  Qed.
  (** Function keys use the client's equality test. *)
  Lemma key_eqb_specification : key_eqb = F.eqb.
  Proof.
    reflexivity.
  Qed.
  (** Local rows precede calls in function, site and resolver order. *)
  Lemma rows_spec : forall p, CL.wf p -> rows p = map SummaryLocal (CL.functions p) ++
    flat_map (fun f => flat_map (fun site => map (SummaryCall site) (CL.resolve p site))
      (CL.sites_of p f)) (CL.functions p).
  Proof.
    intros p Hwf; unfold rows; rewrite (CL.calls_spec p Hwf).
    f_equal; induction (CL.functions p) as [|f fs IH]; cbn [flat_map map].
    - reflexivity.
    - rewrite map_app, IH; f_equal.
      induction (CL.sites_of p f) as [|site sites IHsite]; cbn [flat_map map].
      + reflexivity.
      + rewrite map_app, IHsite, map_map; reflexivity.
  Qed.
  (** A local row targets its own function. *)
  Lemma target_local : forall p f, target p (SummaryLocal f) = f.
  Proof.
    reflexivity.
  Qed.
  (** A lifted row targets its call site's caller. *)
  Lemma target_call : forall p site g, target p (SummaryCall site g) = CL.caller_of p site.
  Proof.
    reflexivity.
  Qed.
  (** Local summaries have no side contributions. *)
  Lemma eval_local : forall p f look,
    eval p (SummaryLocal f) look = Some (B.local p f, nil).
  Proof.
    reflexivity.
  Qed.
  (** Calls lift their callee summary and contribute a callee entry fact. *)
  Lemma eval_call : forall p site g look, eval p (SummaryCall site g) look =
    Some (B.via_call p site g (look g), (g, B.entry p site g) :: nil).
  Proof.
    reflexivity.
  Qed.
End Summary.

Module SummaryT (P : TYPE) (F Site : KEY_T) (CL : CALLS_T P F Site)
    (L : LATTICE_T) (B : BODY_T P F Site L)
    <: SUMMARY_T P F Site CL L B.
  Include Summary P F Site CL L B.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  Definition row_work p s := (B.body_work p s + N.of_nat
    (fold_right Nat.max 0%nat (map (fun sg => Site.bits (fst sg)) (CL.calls p))))%N.
  Definition kw := CL.function_width.
  Definition c_sys : N := 1%N. (* STUB *)
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof. Admitted. (* STUB *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof. Admitted. (* STUB *)
End SummaryT.

Module SummarySound (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L) (A : SUMMARY P F Site CL L B)
    (M : SEMANTICS P) (K : CALLS_LINK P F Site CL M)
    (SL : SUMMARY_LINK P F Site CL L B M K)
    <: SUMMARY_SOUND P F Site CL L B A M K SL.
  (** Each reachable stack records the resolver links that created its frames. *)
  Lemma reachable_linked : forall p s, CL.wf p ->
    reachable (M.initial p) (M.step p) s ->
    frames_linked (CL.sites_of p) (CL.caller_of p) (CL.resolve p)
      (K.here s) (K.frames s).
  Proof.
    intros p s Hwf Hreach; induction Hreach as [s Hinitial|s t Hreach IH Hstep].
    - rewrite (proj2 (K.initial_roots p s Hinitial)); exact I.
    - destruct (K.step_shape p s t Hreach Hstep) as
        [[Hhere Hstack]|[[site [Hsite [Hcallee Hstack]]]|[f [site [Hstack Hhere]]]]].
      + rewrite Hhere, Hstack; exact IH.
      + rewrite Hstack; cbn [frames_linked].
        split; [exact (proj1 (CL.sites_caller p (K.here s) site Hwf Hsite))|].
        split; [exact Hsite|]. split; assumption.
      + rewrite Hstack in IH; cbn [frames_linked] in IH.
        destruct IH as [_ [_ [_ Htail]]]; now rewrite Hhere.
  Qed.

  (** A post-solution bounds the local summary of every listed function. *)
  Lemma local_bound : forall p look f, CL.wf p -> A.post_solution p look ->
    In f (CL.functions p) -> L.leb (B.local p f) (look f) = true.
  Proof.
    intros p look f Hwf Hpost Hf.
    assert (Hrow : In (SummaryLocal f) (A.rows p)).
    { rewrite (A.rows_spec p Hwf); apply in_or_app; left; now apply in_map. }
    specialize (Hpost (SummaryLocal f) Hrow).
    rewrite A.target_local, A.eval_local in Hpost.
    cbn [row_ok] in Hpost; now apply andb_true_iff in Hpost as [Hpost _].
  Qed.

  (** A listed call bounds both its lifted summary and its callee entry fact. *)
  Lemma call_bounds : forall p look f site g,
    CL.wf p -> A.post_solution p look -> In f (CL.functions p) ->
    In site (CL.sites_of p f) -> In g (CL.resolve p site) ->
    L.leb (B.via_call p site g (look g)) (look (CL.caller_of p site)) = true /\
    L.leb (B.entry p site g) (look g) = true.
  Proof.
    intros p look f site g Hwf Hpost Hf Hsite Hg.
    assert (Hrow : In (SummaryCall site g) (A.rows p)).
    { rewrite (A.rows_spec p Hwf); apply in_or_app; right.
      apply in_flat_map; exists f; split; [exact Hf|].
      apply in_flat_map; exists site; split; [exact Hsite|now apply in_map]. }
    specialize (Hpost (SummaryCall site g) Hrow).
    rewrite A.target_call, A.eval_call in Hpost.
    cbn [row_ok forallb fst snd] in Hpost.
    apply andb_true_iff in Hpost as [Hcall Hentry].
    apply andb_true_iff in Hentry as [Hentry _]; now split.
  Qed.

  (** Coverage lifts from the current callee through any linked stack suffix. *)
  Lemma frames_cover : forall p look s t, CL.wf p -> A.post_solution p look ->
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    forall stack g,
      frames_linked (CL.sites_of p) (CL.caller_of p) (CL.resolve p) g stack ->
      incl stack (K.frames s) -> SL.gamma_step (look g) s t ->
      forall f, In f (g :: map fst stack) -> SL.gamma_step (look f) s t.
  Proof.
    intros p look s t Hwf Hpost Hreach Hstep stack.
    induction stack as [|[caller site] rest IH]; intros g Hlinked Hstack Hcover f Hin.
    - destruct Hin as [<-|[]]; exact Hcover.
    - cbn [frames_linked] in Hlinked.
      destruct Hlinked as [Hcaller [Hsite [Htarget Hlinked]]].
      destruct Hin as [<-|Hin]; [exact Hcover|].
      apply (IH caller Hlinked) with (f := f).
      + intros frame Hframe; apply Hstack; now right.
      + eapply SL.step_mono.
        * rewrite <- Hcaller; exact (proj1 (call_bounds p look caller site g
            Hwf Hpost (proj2 (CL.sites_caller p caller site Hwf Hsite)) Hsite Htarget)).
        * apply (SL.call_sound p s t site g (look g) Hreach Hstep).
          -- rewrite Hcaller; apply Hstack; now left.
          -- exact Hcover.
      + exact Hin.
  Qed.

  Lemma covers : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t f, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In f (K.active s) -> SL.gamma_step (look f) s t.
  Proof.
    intros p look Hwf Hpost s t f Hreach Hstep Hin.
    eapply (frames_cover p look s t Hwf Hpost Hreach Hstep
      (K.frames s) (K.here s)).
    - exact (reachable_linked p s Hwf Hreach).
    - apply incl_refl.
    - eapply SL.step_mono.
      + apply (local_bound p look (K.here s) Hwf Hpost).
        apply (K.frames_listed p s Hreach); now left.
      + exact (SL.local_sound p s t Hreach Hstep).
    - exact Hin.
  Qed.
  Lemma covers_entry : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t site, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In site (CL.sites_of p (K.here s)) -> In (K.here t) (CL.resolve p site) ->
      K.frames t = (K.here s, site) :: K.frames s -> SL.gamma_entry (look (K.here t)) t.
  Proof.
    intros p look Hwf Hpost s t site Hreach Hstep Hsite Htarget Hstack.
    eapply SL.entry_mono.
    - exact (proj2 (call_bounds p look (K.here s) site (K.here t)
        Hwf Hpost (K.frames_listed p s Hreach (K.here s) (or_introl eq_refl))
        Hsite Htarget)).
    - exact (SL.entry_sound p s t site Hreach Hstep Hsite Htarget Hstack).
  Qed.
  Lemma covers_finished : forall p look f s t, CL.wf p -> A.post_solution p look ->
    covered_run (M.step p)
      (fun u _ => reachable (M.initial p) (M.step p) u /\ In f (K.active u)) s t ->
    covered_run (M.step p) (SL.gamma_step (look f)) s t.
  Proof.
    intros p look f s t Hwf Hpost Hrun.
    induction Hrun as [s|s u t Hstep [Hreach Hin] Hrun IH].
    - constructor.
    - econstructor; [exact Hstep| |exact IH].
      exact (covers p look Hwf Hpost s u f Hreach Hstep Hin).
  Qed.
End SummarySound.
