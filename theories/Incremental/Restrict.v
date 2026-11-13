(** * Seeded restrictions of local systems

    A restricted program stores the original program, frozen values and selected rows.
    For example, selecting no source rows still retains any seed rows.
    Shared footprint and binding helpers support checked demand and invalidation.
    Builds on: RestrictSig, SystemSig, CheckSig, MapSig and Trie. *)

From Stdlib Require Import List Bool Arith PArith NArith Lia Sorting.Permutation.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig.
From Galois.Incremental Require Import RestrictSig.

Import List.ListNotations.

Record restricted_program (P K A R : Type) := {
  original : P;
  seeds : list (K * A);
  selected : list R
}.

TimeFun original.
TimeFun seeds.
TimeFun selected.

Module RestrictedCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L) <: SYSTEM_OPS L.
  Definition prog := restricted_program S.prog S.key L.t S.row.
  Definition key := S.key.
  Definition row := (S.row + (S.key * L.t))%type.
  Definition frame := S.frame.
  Definition key_code := S.key_code.
  Definition key_eqb := S.key_eqb.
  Definition rows (p : prog) : list row :=
    map (fun r => inl r) (selected _ _ _ _ p) ++ map (fun xv => inr xv) (seeds _ _ _ _ p).
  Definition target (p : prog) (r : row) : key :=
    match r with
    | inl r => S.target (original _ _ _ _ p) r
    | inr xv => fst xv
    end.
  Definition start (p : prog) (r : row) : query key L.t frame :=
    match r with
    | inl r => S.start (original _ _ _ _ p) r
    | inr xv => Ret (snd xv)
    end.
  Definition resume (p : prog) (f : frame) (a : L.t) : query key L.t frame :=
    S.resume (original _ _ _ _ p) f a.
  Definition deps (p : prog) (r : row) : list key :=
    match r with
    | inl r => S.deps (original _ _ _ _ p) r
    | inr _ => []
    end.
  Definition sides (p : prog) (r : row) : list key :=
    match r with
    | inl r => S.sides (original _ _ _ _ p) r
    | inr _ => []
    end.
End RestrictedCode.

Module RestrictCode (L : LATTICE_OPS) (S : LOCAL_SYSTEM_OPS L).
  Module RS := RestrictedCode L S.
  Module Code <: RESTRICT_OPS L S RS.
    Definition mk (p : S.prog) (fz : list (S.key * L.t)) (rs : list S.row) : RS.prog :=
      {| original := p; seeds := fz; selected := rs |}.
  End Code.
End RestrictCode.

Module Restricted (L : LATTICE) (S : LOCAL_SYSTEM L) <: SYSTEM L.
  Include RestrictedCode L S.
  Include SYSTEM_SPEC L.
  (* spec: wf *)
  Definition wf (p : prog) : Prop := S.wf (original _ _ _ _ p) /\
    Forall (fun r => In r (S.rows (original _ _ _ _ p))) (selected _ _ _ _ p).

  (** Original rows occur exactly where they occur in the selected list. *)
  Lemma rows_original : forall p r,
    In (inl r) (rows p) <-> In r (selected _ _ _ _ p).
  Proof.
    intros p r; unfold rows; rewrite in_app_iff; split.
    - intros [Hin|Hin]; apply in_map_iff in Hin as [row [Heq Hin]].
      + injection Heq as Heq; subst row; exact Hin.
      + discriminate Heq.
    - intro Hin; left; apply in_map; exact Hin.
  Qed.

  (** Seed rows occur exactly where their bindings occur in the seed list. *)
  Lemma rows_seed : forall p xv,
    In (inr xv) (rows p) <-> In xv (seeds _ _ _ _ p).
  Proof.
    intros p xv; unfold rows; rewrite in_app_iff; split.
    - intros [Hin|Hin]; apply in_map_iff in Hin as [row [Heq Hin]].
      + discriminate Heq.
      + injection Heq as Heq; subst row; exact Hin.
    - intro Hin; right; apply in_map; exact Hin.
  Qed.

  (** Well-formed restrictions select only rows declared by their source program. *)
  Lemma original_listed : forall p r, wf p -> In (inl r) (rows p) ->
    In r (S.rows (original _ _ _ _ p)).
  Proof.
    intros p r [_ Hselected] Hin.
    apply rows_original in Hin; rewrite Forall_forall in Hselected.
    exact (Hselected r Hin).
  Qed.

  (** Restricting an original row preserves its complete evaluation. *)
  Lemma eval_original : forall p r look,
    eval p (inl r) look = S.eval (original _ _ _ _ p) r look.
  Proof.
    reflexivity.
  Qed.

  (** A seed returns its frozen value and produces no side contributions. *)
  Lemma eval_seed : forall p x v look, eval p (inr (x, v)) look = Some (v, []).
  Proof.
    reflexivity.
  Qed.

  (** Seed rows terminate before they can reach a read frame. *)
  Lemma seed_no_ask : forall p xv look n q acc x f,
    loop_fuel (eval_step (resume p) look) n (start p (inr xv), nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> False.
  Proof.
    intros p [y v] look [|n] q acc x f Hrun Hask.
    - inversion Hrun; subst; discriminate Hask.
    - discriminate Hrun.
  Qed.

  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    exact S.key_code_inj.
  Qed.

  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    exact S.key_eqb_spec.
  Qed.

  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p [r|[x v]] look Hwf Hin.
    - rewrite eval_original; apply S.eval_total.
      + exact (proj1 Hwf).
      + exact (original_listed p r Hwf Hin).
    - rewrite eval_seed; discriminate.
  Qed.

  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [r|[x v]] s u Hwf Hin Hagree.
    - rewrite !eval_original; apply S.reads_within.
      + exact (proj1 Hwf).
      + exact (original_listed p r Hwf Hin).
      + exact Hagree.
    - rewrite !eval_seed; reflexivity.
  Qed.

  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p [r|xv] look n q acc x f Hwf Hin Hrun Hask.
    - exact (S.asks_within (original _ _ _ _ p) r look n q acc x f
        (proj1 Hwf) (original_listed p r Hwf Hin) Hrun Hask).
    - exfalso; exact (seed_no_ask p xv look n q acc x f Hrun Hask).
  Qed.

  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p [r|[y v]] look a ss x b Hwf Hin Heval Hside.
    - rewrite eval_original in Heval.
      exact (S.sides_within (original _ _ _ _ p) r look a ss x b
        (proj1 Hwf) (original_listed p r Hwf Hin) Heval Hside).
    - rewrite eval_seed in Heval; inversion Heval; subst; contradiction.
  Qed.

  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p [r|[x v]] look a ss Hwf Hin Heval.
    - rewrite eval_original in Heval.
      exact (S.sides_count (original _ _ _ _ p) r look a ss
        (proj1 Hwf) (original_listed p r Hwf Hin) Heval).
    - rewrite eval_seed in Heval; inversion Heval; subst; reflexivity.
  Qed.

End Restricted.

Module RestrictedT (L : LATTICE_T) (S : LOCAL_SYSTEM_T L) <: SYSTEM_T L.
  Include Restricted L S.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
  (* spec: row_work kw *)
  Definition row_work (p : prog) (s : nat) : N :=
    (S.row_work (original _ _ _ _ p) s +
      N.of_nat (fold_right (fun xv n => Nat.max (L.size (snd xv)) n) 0%nat
        (seeds _ _ _ _ p)) + 1)%N.
  Definition kw (p : prog) : nat :=
    fold_right (fun xv n => Nat.max (S.key_bits (fst xv)) n)
      (S.kw (original _ _ _ _ p)) (seeds _ _ _ _ p).
  Definition c_sys : N := (S.c_sys + 8)%N.

  (** Folding maxima preserves the initial lower bound. *)
  Lemma max_fold_base : forall A (measure : A -> nat) xs base,
    base <= fold_right (fun x n => Nat.max (measure x) n) base xs.
  Proof.
    intros A measure xs; induction xs as [|x xs IH]; intro base.
    - reflexivity.
    - cbn [fold_right]; eapply Nat.le_trans; [apply IH|apply Nat.le_max_r].
  Qed.

  (** The folded maximum bounds every listed element's measure. *)
  Lemma max_fold_member : forall A (measure : A -> nat) xs base x,
    In x xs -> measure x <= fold_right (fun y n => Nat.max (measure y) n) base xs.
  Proof.
    intros A measure xs; induction xs as [|y xs IH]; intros base x Hin.
    - contradiction.
    - cbn [fold_right]; destruct Hin as [<-|Hin].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH base x Hin)|apply Nat.le_max_r].
  Qed.

  (** The restricted width retains the source program's key budget. *)
  Lemma original_kw_le : forall p, S.kw (original _ _ _ _ p) <= kw p.
  Proof.
    intro p; apply max_fold_base.
  Qed.

  (** The restricted width covers each frozen key. *)
  Lemma seed_key_bits_le : forall p xv, In xv (seeds _ _ _ _ p) ->
    S.key_bits (fst xv) <= kw p.
  Proof.
    intros p xv Hin.
    exact (max_fold_member _ (fun binding => S.key_bits (fst binding))
      (seeds _ _ _ _ p) (S.kw (original _ _ _ _ p)) xv Hin).
  Qed.

  (** The restricted row budget retains the source program's work allowance. *)
  Lemma original_row_work_le : forall p s,
    (S.row_work (original _ _ _ _ p) s <= row_work p s)%N.
  Proof.
    intros p s; unfold row_work; lia.
  Qed.

  (** Every frozen value fits the added maximum-size allowance. *)
  Lemma seed_value_size_le : forall p xv s, In xv (seeds _ _ _ _ p) ->
    (N.of_nat (L.size (snd xv)) <= row_work p s)%N.
  Proof.
    intros p xv s Hin.
    pose proof (max_fold_member _ (fun binding => L.size (snd binding))
      (seeds _ _ _ _ p) 0 xv Hin) as Hsize.
    unfold row_work; lia.
  Qed.

  (** Step budgets grow with the size of abstract values. *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof.
    intros p s s' Hle.
    pose proof (S.row_work_mono (original _ _ _ _ p) s s' Hle) as Hwork.
    unfold row_work; lia.
  Qed.

  (** The program key budget covers all declared reads and writes. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p [r|[y v]] x Hwf Hin Hkey.
    - eapply Nat.le_trans; [|apply original_kw_le].
      exact (S.key_bits_le (original _ _ _ _ p) r x
        (proj1 Hwf) (original_listed p r Hwf Hin) Hkey).
    - cbn [writes target sides deps] in Hkey.
      destruct Hkey as [<-|Hfalse]; [|contradiction].
      exact (seed_key_bits_le p (y, v) (proj1 (rows_seed p (y, v)) Hin)).
  Qed.
  (** Encoding costs are linear in the resulting code size. *)
  Lemma T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intro x; pose proof (S.T_key_code_le x) as Htime.
    unfold S.key_bits in Htime.
    unfold c_sys, key_bits, key_code; time_step.
  Qed.

  (** Equality costs are bounded by the first key's code size. *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros a b; pose proof (S.T_key_eqb_le a b) as Htime.
    unfold S.key_bits in Htime.
    unfold c_sys, key_bits, key_code; time_step.
  Qed.

  (** Enumerating rows costs linear time in the output length. *)
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof.
    intros p Hwf.
    pose proof (ListDef.T_map_le (fun r : S.row => @inl S.row (S.key * L.t) r)
      (fun _ => 1%N) 1%N (selected _ _ _ _ p) (fun _ => N.le_refl 1)) as Hselected.
    pose proof (ListDef.T_map_le (fun xv : S.key * L.t => @inr S.row (S.key * L.t) xv)
      (fun _ => 1%N) 1%N (seeds _ _ _ _ p) (fun _ => N.le_refl 1)) as Hseeds.
    pose proof (Datatypes.T_app_le
      (map (fun r : S.row => @inl S.row (S.key * L.t) r) (selected _ _ _ _ p))
      (map (fun xv : S.key * L.t => @inr S.row (S.key * L.t) xv)
        (seeds _ _ _ _ p))) as Happend.
    rewrite length_map in Happend.
    unfold c_sys, rows; rewrite length_app, !length_map; time_step.
  Qed.

  (** Target lookup fits the row budget. *)
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [r|xv] Hwf Hin.
    - pose proof (S.T_target_le (original _ _ _ _ p) r
        (proj1 Hwf) (original_listed p r Hwf Hin)) as Htime.
      unfold c_sys, row_work; time_step.
    - unfold c_sys, row_work; time_step.
  Qed.

  (** Starting a row fits the row budget. *)
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [r|xv] Hwf Hin.
    - pose proof (S.T_start_le (original _ _ _ _ p) r
        (proj1 Hwf) (original_listed p r Hwf Hin)) as Htime.
      unfold c_sys, row_work; time_step.
    - unfold c_sys, row_work; time_step.
  Qed.

  (** Resuming a frame that a listed row reaches pays for the sizes of the lookup values. *)
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p [r|xv] look s n q acc x f Hwf Hin Hsize Hreach Hask.
    - pose proof (S.T_resume_le (original _ _ _ _ p) r look s n q acc x f
        (proj1 Hwf) (original_listed p r Hwf Hin) Hsize Hreach Hask) as Htime.
      unfold c_sys, row_work; time_step.
    - exfalso; exact (seed_no_ask p xv look n q acc x f Hreach Hask).
  Qed.

  (** Positive occurrence and width budgets absorb the two inherited-wrapper calls. *)
  Lemma enumeration_time_le : forall clock count width,
    (1 <= count)%N -> (1 <= width)%N -> (clock <= S.c_sys * count * width)%N ->
    (1 + (1 + clock) <= c_sys * count * width)%N.
  Proof.
    intros clock count width Hcount Hwidth Htime.
    assert (Hunit : (1 <= count * width)%N).
    { change (1 * 1 <= count * width)%N; apply N.mul_le_mono; assumption. }
    unfold c_sys; rewrite !N.mul_add_distr_r.
    repeat rewrite <- N.mul_assoc in Htime |- *.
    lia.
  Qed.

  (** Dependency enumeration pays for every key occurrence. *)
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof.
    intros p [r|xv] Hwf Hin.
    - pose proof (S.T_deps_le (original _ _ _ _ p) r
        (proj1 Hwf) (original_listed p r Hwf Hin)) as Htime.
      pose proof (original_kw_le p) as Hwidth.
      assert (Htime' : (S.T_deps (original _ _ _ _ p) r <=
        S.c_sys * N.of_nat (length (S.deps (original _ _ _ _ p) r) + 1) *
          N.of_nat (kw p + 1))%N).
      { eapply N.le_trans; [exact Htime|apply N.mul_le_mono_l; lia]. }
      unfold T_deps; time_simpl; time_cbn.
      apply enumeration_time_le; [lia|lia|exact Htime'].
    - unfold c_sys, deps; time_step.
  Qed.

  (** Side enumeration pays for every key occurrence. *)
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) * N.of_nat (kw p + 1))%N.
  Proof.
    intros p [r|xv] Hwf Hin.
    - pose proof (S.T_sides_le (original _ _ _ _ p) r
        (proj1 Hwf) (original_listed p r Hwf Hin)) as Htime.
      pose proof (original_kw_le p) as Hwidth.
      assert (Htime' : (S.T_sides (original _ _ _ _ p) r <=
        S.c_sys * N.of_nat (length (S.sides (original _ _ _ _ p) r) + 1) *
          N.of_nat (kw p + 1))%N).
      { eapply N.le_trans; [exact Htime|apply N.mul_le_mono_l; lia]. }
      unfold T_sides; time_simpl; time_cbn.
      apply enumeration_time_le; [lia|lia|exact Htime'].
    - unfold c_sys, sides; time_step.
  Qed.

  (** Row output sizes fit the transfer budget. *)
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p [r|[x v]] look s a ss Hwf Hin Hsize Heval.
    - rewrite eval_original in Heval.
      destruct (S.eval_size_le (original _ _ _ _ p) r look s a ss
        (proj1 Hwf) (original_listed p r Hwf Hin) Hsize Heval) as [Hvalue Hsides].
      split.
      + eapply N.le_trans; [exact Hvalue|apply original_row_work_le].
      + eapply Forall_impl; [|exact Hsides].
        intros binding Hbound; eapply N.le_trans; [exact Hbound|apply original_row_work_le].
    - rewrite eval_seed in Heval; injection Heval as Hvalue Hsides; subst a ss; split.
      + exact (seed_value_size_le p (x, v) s (proj1 (rows_seed p (x, v)) Hin)).
      + constructor.
  Qed.

End RestrictedT.

Module Restrict (L : LATTICE) (S : LOCAL_SYSTEM L).
  Module RS := Restricted L S.
  Module Impl <: RESTRICT L S RS.
    Module C := RestrictCode L S.
    Include C.Code.
    Include RESTRICT_SPEC L S RS.

    (** Restricted post-solutions accept every selected row and every frozen value. *)
    Lemma restrict_post : forall p fz rs s, RS.post_solution (mk p fz rs) s ->
      (forall r, In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true) /\
      (forall x v, In (x, v) fz -> L.leb v (s x) = true).
    Proof.
      intros p fz rs s Hpost; split.
      - intros r Hin.
        pose proof (Hpost (inl r) (proj2 (RS.rows_original (mk p fz rs) r) Hin)) as Hrow.
        rewrite RS.eval_original in Hrow; exact Hrow.
      - intros x v Hin.
        pose proof (Hpost (inr (x, v))
          (proj2 (RS.rows_seed (mk p fz rs) (x, v)) Hin)) as Hseed.
        rewrite RS.eval_seed in Hseed; apply Bool.andb_true_iff in Hseed as [Hseed _].
        exact Hseed.
    Qed.

    (** A source post-solution above the seeds satisfies every restricted row. *)
    Lemma restrict_complete : forall p fz rs s, S.post_solution p s ->
      (forall r, In r rs -> In r (S.rows p)) ->
      (forall x v, In (x, v) fz -> L.leb v (s x) = true) ->
      RS.post_solution (mk p fz rs) s.
    Proof.
      intros p fz rs s Hpost Hlisted Hseeds [r|[x v]] Hin.
      - apply RS.rows_original in Hin; rewrite RS.eval_original.
        exact (Hpost r (Hlisted r Hin)).
      - apply RS.rows_seed in Hin; rewrite RS.eval_seed.
        apply Bool.andb_true_iff; split; [exact (Hseeds x v Hin)|reflexivity].
    Qed.

    (** Source monotonicity transfers to selected rows and constant seed rows. *)
    Lemma mk_monotone : forall p fz rs, S.monotone p ->
      (forall r, In r rs -> In r (S.rows p)) -> RS.monotone (mk p fz rs).
    Proof.
      intros p fz rs Hmono Hlisted [r|[x v]] s u Hin Hbelow.
      - apply RS.rows_original in Hin; rewrite !RS.eval_original.
        exact (Hmono r s u (Hlisted r Hin) Hbelow).
      - rewrite !RS.eval_seed; split; [apply L.leb_refl|constructor].
    Qed.

    (** Selecting declared source rows establishes the restricted well-formedness invariant. *)
    Lemma mk_wf : forall p fz rs, S.wf p ->
      (forall r, In r rs -> In r (S.rows p)) -> RS.wf (mk p fz rs).
    Proof.
      intros p fz rs Hwf Hlisted; split; [exact Hwf|].
      apply Forall_forall; exact Hlisted.
    Qed.

  End Impl.
End Restrict.

Module RestrictT (L : LATTICE_T) (S : LOCAL_SYSTEM_T L).
  Module RS := RestrictedT L S.
  Module Impl <: RESTRICT_ALL L S RS.
    Module Plain := Restrict L S.
    Include Plain.Impl.
    TimeFun mk.
    Definition c_res : N := 1.

    (** Restricted key budgets cover the original program and frozen keys. *)
    Lemma mk_kw : forall p fz rs,
      RS.kw (mk p fz rs) <= fold_right (fun xv n => Nat.max (S.key_bits (fst xv)) n)
        (S.kw p) fz.
    Proof.
      reflexivity.
    Qed.

    (** Restricted row work adds the largest frozen value to the source row budget. *)
    Lemma mk_row_work : forall p fz rs s,
      (RS.row_work (mk p fz rs) s <= S.row_work p s +
        N.of_nat (fold_right (fun xv n => Nat.max (L.size (snd xv)) n) 0%nat fz) + 1)%N.
    Proof.
      reflexivity.
    Qed.

    (** Constructing the restriction record fits the public selected-data budget. *)
    Lemma T_mk_le : forall p fz rs,
      (T_mk p fz rs <= c_res *
        N.of_nat ((fold_right Nat.add 0
          (map (fun r => Pos.size_nat (S.row_code r) + 1) rs) +
         fold_right Nat.add 0
          (map (fun xv => S.key_bits (fst xv) + L.size (snd xv) + 1) fz) + 1)%nat))%N.
    Proof.
      intros p fz rs; unfold c_res; time_step.
    Qed.

    (** Restricted post-solutions accept every primary and side write of a selected row. *)
    Lemma restrict_writes : forall p fz rs s r, RS.post_solution (mk p fz rs) s ->
      In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true.
    Proof.
      intros p fz rs s r Hpost Hin.
      exact (proj1 (restrict_post p fz rs s Hpost) r Hin).
    Qed.

  End Impl.
End RestrictT.

(** * Finite footprint closure

    Each successful iteration removes one pending occurrence and inserts its allowed outputs.
    A budget equal to the input occurrence count therefore suffices for saturation. *)

(** An edit footprint invalidates its stored outputs when any trigger is removed. *)
Record edit_footprint (K : Type) := {
  edit_triggers : list K;
  edit_outputs : list K
}.

Arguments edit_triggers {K}.
Arguments edit_outputs {K}.

TimeFun edit_triggers.
TimeFun edit_outputs.

Record footprint_result (K A : Type) := {
  footprint_seen : list K;
  footprint_selected : list A;
  footprint_pending : list A
}.

Arguments footprint_seen {K A}.
Arguments footprint_selected {K A}.
Arguments footprint_pending {K A}.

Section Closure.
  Context {K A : Type}.
  Variable eqb : K -> K -> bool.
  Variable triggers outputs : A -> list K.
  Variable allowed : K -> bool.

  Definition footprint_mem (x : K) (seen : list K) : bool := existsb (eqb x) seen.

  Definition footprint_put (x : K) (seen : list K) : list K :=
    if allowed x && negb (footprint_mem x seen) then x :: seen else seen.

  Fixpoint footprint_adds (xs seen : list K) : list K :=
    match xs with
    | [] => seen
    | x :: xs' => footprint_adds xs' (footprint_put x seen)
    end.

  Definition footprint_active (seen : list K) (a : A) : bool :=
    existsb (fun x => footprint_mem x seen) (triggers a).

  Fixpoint footprint_pick (seen : list K) (pending : list A) : option (A * list A) :=
    match pending with
    | [] => None
    | a :: rest =>
      if footprint_active seen a then Some (a, rest)
      else match footprint_pick seen rest with
        | None => None
        | Some (b, rest') => Some (b, a :: rest')
        end
    end.

  Fixpoint footprint_close (fuel : nat) (seen : list K) (pending : list A)
      : footprint_result K A :=
    match fuel with
    | O => {| footprint_seen := seen; footprint_selected := []; footprint_pending := pending |}
    | S fuel' =>
      match footprint_pick seen pending with
      | None =>
        {| footprint_seen := seen; footprint_selected := []; footprint_pending := pending |}
      | Some (a, rest) =>
        let result := footprint_close fuel' (footprint_adds (outputs a) seen) rest in
        {| footprint_seen := footprint_seen result;
           footprint_selected := a :: footprint_selected result;
           footprint_pending := footprint_pending result |}
      end
    end.

  Definition footprint_run (seen : list K) (pending : list A) : footprint_result K A :=
    footprint_close (length pending) seen pending.

  Hypothesis eqb_spec : forall x y, eqb x y = true <-> x = y.

  (** Boolean membership reflects key membership. *)
  Lemma footprint_mem_spec : forall x seen, footprint_mem x seen = true <-> In x seen.
  Proof.
    intros x seen; unfold footprint_mem; rewrite existsb_exists; split.
    - intros [y [Hy Heq]]; apply eqb_spec in Heq; subst y; exact Hy.
    - intro Hx; exists x; split; [exact Hx | apply eqb_spec; reflexivity].
  Qed.

  (** Inserting one allowed key preserves all previous keys. *)
  Lemma footprint_put_spec : forall x y seen,
    In y (footprint_put x seen) <-> In y seen \/ (y = x /\ allowed x = true).
  Proof.
    intros x y seen; unfold footprint_put.
    destruct (allowed x) eqn:Hallowed; cbn.
    - destruct (footprint_mem x seen) eqn:Hmem; cbn.
      + apply footprint_mem_spec in Hmem; split.
        * intro Hy; left; exact Hy.
        * intros [Hy | [-> _]]; assumption.
      + cbn; intuition congruence.
    - split; [intro Hy; left; exact Hy | intros [Hy | [_ Hfalse]]].
      + exact Hy.
      + discriminate Hfalse.
  Qed.

  (** Adding a list inserts precisely its allowed keys. *)
  Lemma footprint_adds_spec : forall xs seen y,
    In y (footprint_adds xs seen) <-> In y seen \/ (In y xs /\ allowed y = true).
  Proof.
    induction xs as [|x xs IH]; intros seen y; cbn [footprint_adds].
    - cbn; tauto.
    - rewrite IH, footprint_put_spec; cbn; split.
      + intros [[Hy | [-> Hallowed]] | [Hy Hallowed]]; tauto.
      + intros [Hy | [[-> | Hy] Hallowed]]; tauto.
  Qed.

  (** Adding keys keeps a duplicate-free accumulator duplicate-free. *)
  Lemma footprint_adds_nodup : forall xs seen,
    NoDup seen -> NoDup (footprint_adds xs seen).
  Proof.
    induction xs as [|x xs IH]; intros seen Hseen; cbn [footprint_adds].
    - exact Hseen.
    - apply IH; unfold footprint_put.
      destruct (allowed x && negb (footprint_mem x seen)) eqn:Hadd.
      + apply andb_true_iff in Hadd as [_ Hmem]; apply negb_true_iff in Hmem.
        constructor; [|exact Hseen].
        intro Hin; apply footprint_mem_spec in Hin; congruence.
      + exact Hseen.
  Qed.

  (** A footprint is active precisely when one trigger is present. *)
  Lemma footprint_active_spec : forall seen a,
    footprint_active seen a = true <-> exists x, In x (triggers a) /\ In x seen.
  Proof.
    intros seen a; unfold footprint_active; rewrite existsb_exists; split.
    - intros [x [Hx Hmem]]; exists x; split; [exact Hx | apply footprint_mem_spec; exact Hmem].
    - intros [x [Hx Hmem]]; exists x; split; [exact Hx | apply footprint_mem_spec; exact Hmem].
  Qed.

  (** Growing the accumulated keys preserves activation. *)
  Lemma footprint_active_mono : forall seen seen' a,
    incl seen seen' -> footprint_active seen a = true -> footprint_active seen' a = true.
  Proof.
    intros seen seen' a Hinc Hactive; apply footprint_active_spec in Hactive.
    destruct Hactive as [x [Htrigger Hseen]]; apply footprint_active_spec.
    exists x; split; [exact Htrigger | apply Hinc; exact Hseen].
  Qed.

  (** Selection removes exactly one activated occurrence, without comparing items. *)
  Lemma footprint_pick_some : forall seen pending a rest,
    footprint_pick seen pending = Some (a, rest) ->
    footprint_active seen a = true /\ Permutation pending (a :: rest).
  Proof.
    intros seen pending; induction pending as [|b pending IH]; intros a rest Hpick.
    - discriminate Hpick.
    - cbn [footprint_pick] in Hpick; destruct (footprint_active seen b) eqn:Hactive.
      + inversion Hpick; subst; split; [exact Hactive | apply Permutation_refl].
      + destruct (footprint_pick seen pending) as [[c remaining]|] eqn:Hrest;
          [|discriminate Hpick].
        inversion Hpick; subst; destruct (IH _ _ eq_refl) as [Hc Hperm].
        split; [exact Hc |].
        eapply Permutation_trans; [apply perm_skip; exact Hperm | apply perm_swap].
  Qed.

  (** A failed selection means that every pending footprint is inactive. *)
  Lemma footprint_pick_none : forall seen pending,
    footprint_pick seen pending = None ->
    forall a, In a pending -> footprint_active seen a = false.
  Proof.
    intros seen pending; induction pending as [|b pending IH]; intros Hpick a Hin.
    - contradiction Hin.
    - cbn [footprint_pick] in Hpick; destruct (footprint_active seen b) eqn:Hactive;
        [discriminate Hpick |].
      destruct (footprint_pick seen pending) as [[c rest]|] eqn:Hrest;
        [discriminate Hpick |].
      destruct Hin as [<- | Hin]; [exact Hactive | apply IH; assumption].
  Qed.

  (** Saturation never removes an accumulated key. *)
  Lemma footprint_close_seed : forall fuel seen pending,
    incl seen (footprint_seen (footprint_close fuel seen pending)).
  Proof.
    induction fuel as [|fuel IH]; intros seen pending; cbn [footprint_close]; [apply incl_refl |].
    destruct (footprint_pick seen pending) as [[a rest]|] eqn:Hpick;
      cbn [footprint_seen]; [|apply incl_refl].
    intros x Hx; apply IH; apply footprint_adds_spec; left; exact Hx.
  Qed.

  (** Selected and remaining items partition the original occurrences. *)
  Lemma footprint_close_partition : forall fuel seen pending,
    Permutation pending
      (footprint_selected (footprint_close fuel seen pending) ++
       footprint_pending (footprint_close fuel seen pending)).
  Proof.
    induction fuel as [|fuel IH]; intros seen pending; cbn [footprint_close];
      [apply Permutation_refl |].
    destruct (footprint_pick seen pending) as [[a rest]|] eqn:Hpick;
      cbn [footprint_selected footprint_pending]; [|apply Permutation_refl].
    apply footprint_pick_some in Hpick as [_ Hperm].
    eapply Permutation_trans; [exact Hperm | apply perm_skip; apply IH].
  Qed.

  (** Every selected item remains active at the final accumulator. *)
  Lemma footprint_close_selected : forall fuel seen pending a,
    In a (footprint_selected (footprint_close fuel seen pending)) ->
    footprint_active (footprint_seen (footprint_close fuel seen pending)) a = true.
  Proof.
    induction fuel as [|fuel IH]; intros seen pending a Hin; cbn [footprint_close] in *;
      [contradiction Hin |].
    destruct (footprint_pick seen pending) as [[b rest]|] eqn:Hpick;
      cbn [footprint_selected footprint_seen] in *; [|contradiction Hin].
    destruct Hin as [<- | Hin]; [|apply IH; exact Hin].
    apply footprint_pick_some in Hpick as [Hactive _].
    eapply footprint_active_mono; [|exact Hactive].
    intros x Hx; apply footprint_close_seed; apply footprint_adds_spec; left; exact Hx.
  Qed.

  (** All allowed outputs of a selected item remain accumulated. *)
  Lemma footprint_close_outputs : forall fuel seen pending a x,
    In a (footprint_selected (footprint_close fuel seen pending)) ->
    In x (outputs a) -> allowed x = true ->
    In x (footprint_seen (footprint_close fuel seen pending)).
  Proof.
    induction fuel as [|fuel IH]; intros seen pending a x Hin Houtput Hallowed;
      cbn [footprint_close] in *; [contradiction Hin |].
    destruct (footprint_pick seen pending) as [[b rest]|] eqn:Hpick;
      cbn [footprint_selected footprint_seen] in *; [|contradiction Hin].
    destruct Hin as [<- | Hin].
    - apply footprint_close_seed; apply footprint_adds_spec; right; split; assumption.
    - eapply IH; eassumption.
  Qed.

  (** Every accumulated key is a seed or an allowed selected output. *)
  Lemma footprint_close_provenance : forall fuel seen pending x,
    In x (footprint_seen (footprint_close fuel seen pending)) ->
    In x seen \/ exists a, In a (footprint_selected (footprint_close fuel seen pending)) /\
      In x (outputs a) /\ allowed x = true.
  Proof.
    induction fuel as [|fuel IH]; intros seen pending x Hin; cbn [footprint_close] in *.
    - left; exact Hin.
    - destruct (footprint_pick seen pending) as [[a rest]|] eqn:Hpick;
        cbn [footprint_selected footprint_seen] in *; [|left; exact Hin].
      destruct (IH _ _ _ Hin) as [Hseed | [b [Hb Houtput]]].
      + apply footprint_adds_spec in Hseed as [Hseed | Houtput].
        * left; exact Hseed.
        * right; exists a; split; [left; reflexivity | exact Houtput].
      + right; exists b; split; [right; exact Hb | exact Houtput].
  Qed.

  (** Saturation preserves duplicate-free accumulated keys. *)
  Lemma footprint_close_nodup : forall fuel seen pending,
    NoDup seen -> NoDup (footprint_seen (footprint_close fuel seen pending)).
  Proof.
    induction fuel as [|fuel IH]; intros seen pending Hseen; cbn [footprint_close];
      [exact Hseen |].
    destruct (footprint_pick seen pending) as [[a rest]|]; cbn [footprint_seen];
      [apply IH; apply footprint_adds_nodup; exact Hseen | exact Hseen].
  Qed.

  (** One unit of fuel per pending occurrence suffices for final inactivity. *)
  Lemma footprint_close_inactive : forall fuel seen pending,
    length pending <= fuel -> forall a,
    In a (footprint_pending (footprint_close fuel seen pending)) ->
    footprint_active (footprint_seen (footprint_close fuel seen pending)) a = false.
  Proof.
    induction fuel as [|fuel IH]; intros seen pending Hfuel a Hin.
    - destruct pending; [contradiction Hin | cbn in Hfuel; lia].
    - cbn [footprint_close] in *.
      destruct (footprint_pick seen pending) as [[b rest]|] eqn:Hpick;
        cbn [footprint_pending footprint_seen] in *.
      + apply IH with (pending := rest); [|exact Hin].
        apply footprint_pick_some in Hpick as [_ Hperm].
        apply Permutation_length in Hperm; cbn in Hperm; lia.
      + eapply footprint_pick_none; eassumption.
  Qed.

  (** The selected count and remaining count sum to the initial footprint count. *)
  Lemma footprint_close_count : forall fuel seen pending,
    length (footprint_selected (footprint_close fuel seen pending)) +
    length (footprint_pending (footprint_close fuel seen pending)) = length pending.
  Proof.
    intros fuel seen pending; pose proof (footprint_close_partition fuel seen pending) as Hperm.
    apply Permutation_length in Hperm; rewrite length_app in Hperm; symmetry; exact Hperm.
  Qed.

  (** Full saturation includes every allowed output of an activated input footprint. *)
  Lemma footprint_run_closed : forall seen pending a x,
    In a pending -> footprint_active (footprint_seen (footprint_run seen pending)) a = true ->
    In x (outputs a) -> allowed x = true ->
    In x (footprint_seen (footprint_run seen pending)).
  Proof.
    intros seen pending a x Ha Hactive Houtput Hallowed; unfold footprint_run in *.
    pose proof (footprint_close_partition (length pending) seen pending) as Hperm.
    apply (Permutation_in _ Hperm) in Ha; apply in_app_iff in Ha as [Ha | Ha].
    - eapply footprint_close_outputs; eassumption.
    - pose proof (footprint_close_inactive (length pending) seen pending
        (le_n _) a Ha) as Hinactive; congruence.
  Qed.

  (** Allowed seeds produce an entirely allowed final accumulator. *)
  Lemma footprint_close_allowed : forall fuel seen pending,
    (forall x, In x seen -> allowed x = true) ->
    forall x, In x (footprint_seen (footprint_close fuel seen pending)) -> allowed x = true.
  Proof.
    intros fuel seen pending Hseen x Hin.
    apply footprint_close_provenance in Hin as [Hin | [a [_ [_ Hallowed]]]].
    - apply Hseen; exact Hin.
    - exact Hallowed.
  Qed.
End Closure.

TimeFun footprint_seen.
TimeFun footprint_selected.
TimeFun footprint_pending.
TimeFun footprint_mem.
TimeFun footprint_put.
TimeFun footprint_adds.
TimeFun footprint_active.
TimeFun footprint_pick.
TimeFun footprint_close.
TimeFun footprint_run.

(** * Shared keyed bindings for checked regions *)

Module SourceBindingsCode (L : LATTICE_OPS) (S : SYSTEM_OPS L)
    (Checker : CHECK_OPS L S).
  (** Validated lookup ignores a cell whose payload key differs from the query. *)
  Definition lookup (m : kmap S.key L.t) (x : S.key) : option L.t :=
    match PTrieCode.get (S.key_code x) m with
    | Some (stored_key, v) => if S.key_eqb x stored_key then Some v else None
    | None => None
    end.

  (** Boolean membership uses the source system key comparison. *)
  Definition mem (x : S.key) (xs : list S.key) : bool := existsb (S.key_eqb x) xs.

  (** Key deduplication retains one occurrence of every listed key. *)
  Fixpoint unique (xs : list S.key) : list S.key :=
    match xs with
    | [] => []
    | x :: rest => if mem x rest then unique rest else x :: unique rest
    end.

  (** Seed restoration overwrites the candidate at every listed frozen key. *)
  Definition restore (fz : list (S.key * L.t)) (m : kmap S.key L.t)
      : kmap S.key L.t :=
    fold_left (fun acc xv => PTrieCode.set (S.key_code (fst xv)) xv acc) fz m.

  (** Filling stores every requested key explicitly, including bottom values. *)
  Fixpoint fill (xs : list S.key) (m base : kmap S.key L.t) : kmap S.key L.t :=
    match xs with
    | [] => base
    | x :: rest =>
        PTrieCode.set (S.key_code x) (x, Checker.look m x) (fill rest m base)
    end.

  (** Pruning removes only cells whose stored path disagrees with their payload key. *)
  Fixpoint prune_values (cells : list (positive * (S.key * L.t)))
      (m : kmap S.key L.t) : kmap S.key L.t :=
    match cells with
    | [] => m
    | (path, (x, v)) :: rest =>
        let remaining := if Pos.eqb path (S.key_code x) then m else PTrieCode.remove path m in
        prune_values rest remaining
    end.

  (** Removing a key list deletes its encoded cells from any payload trie. *)
  Definition remove_keys {A} (xs : list S.key) (m : PTrieCode.t A) : PTrieCode.t A :=
    fold_left (fun acc x => PTrieCode.remove (S.key_code x) acc) xs m.

End SourceBindingsCode.

Module SourceBindingFacts (L : LATTICE) (S : SYSTEM L)
    (Checker : CHECK_OPS L S).
  Module Bindings := SourceBindingsCode L S Checker.

  (** The source key comparison reflects equality. *)
  Lemma key_eqb_true : forall x y, S.key_eqb x y = true <-> x = y.
  Proof.
    intros x y; destruct (S.key_eqb_spec x y); split; intro H; congruence.
  Qed.

  (** Boolean key membership reflects list membership. *)
  Lemma mem_spec : forall x xs, Bindings.mem x xs = true <-> In x xs.
  Proof.
    intros x xs; unfold Bindings.mem; rewrite existsb_exists; split.
    - intros [y [Hy Heq]].
      destruct (S.key_eqb_spec x y) as [->|Hneq]; [exact Hy|discriminate Heq].
    - intro Hx; exists x; split; [exact Hx|].
      destruct (S.key_eqb_spec x x); congruence.
  Qed.

  (** Inserting a canonical cell changes exactly its own validated lookup. *)
  Lemma lookup_set : forall m x y v,
    Bindings.lookup (PTrieCode.set (S.key_code y) (y, v) m) x =
      if S.key_eqb x y then Some v else Bindings.lookup m x.
  Proof.
    intros m x y v; destruct (S.key_eqb_spec x y) as [->|Hneq].
    - unfold Bindings.lookup; rewrite PTrie.get_set_same.
      destruct (S.key_eqb_spec y y); congruence.
    - unfold Bindings.lookup; rewrite PTrie.get_set_other; [reflexivity|].
      intro Hcode; apply Hneq, S.key_code_inj, Hcode.
  Qed.

  (** Removing a trie path changes exactly queries with that encoded path. *)
  Lemma lookup_remove : forall m path x,
    Bindings.lookup (PTrieCode.remove path m) x =
      if Pos.eqb (S.key_code x) path then None else Bindings.lookup m x.
  Proof.
    intros m path x; destruct (Pos.eqb (S.key_code x) path) eqn:Hpath.
    - apply Pos.eqb_eq in Hpath; unfold Bindings.lookup.
      rewrite Hpath, PTrie.get_remove_same; reflexivity.
    - apply Pos.eqb_neq in Hpath; unfold Bindings.lookup.
      rewrite PTrie.get_remove_other by exact Hpath; reflexivity.
  Qed.

  (** A mismatched payload is absent from validated lookup at its stored path. *)
  Lemma malformed_lookup : forall original path y v x,
    PTrieCode.get path original = Some (y, v) ->
    Pos.eqb path (S.key_code y) = false -> S.key_code x = path ->
    Bindings.lookup original x = None.
  Proof.
    intros original path y v x Hget Hbad Hpath; subst path.
    unfold Bindings.lookup; rewrite Hget.
    destruct (S.key_eqb_spec x y) as [->|Hneq]; [|reflexivity].
    rewrite Pos.eqb_refl in Hbad; discriminate Hbad.
  Qed.

  (** Pruning malformed original cells preserves every validated lookup. *)
  Lemma prune_values_lookup : forall cells original current,
    (forall path y v, In (path, (y, v)) cells ->
      PTrieCode.get path original = Some (y, v)) ->
    (forall x, Bindings.lookup current x = Bindings.lookup original x) ->
    forall x, Bindings.lookup (Bindings.prune_values cells current) x = Bindings.lookup original x.
  Proof.
    induction cells as [|[path [y v]] rest IH]; intros original current Hcells Hagree x.
    - exact (Hagree x).
    - cbn [Bindings.prune_values].
      destruct (Pos.eqb path (S.key_code y)) eqn:Hvalid.
      + apply (IH original current).
        * intros q z w Hin; apply Hcells; now right.
        * exact Hagree.
      + apply (IH original (PTrieCode.remove path current)).
        * intros q z w Hin; apply Hcells; now right.
        * intro z; rewrite lookup_remove.
          destruct (Pos.eqb (S.key_code z) path) eqn:Hpath.
          -- symmetry; eapply malformed_lookup.
             ++ apply Hcells; now left.
             ++ exact Hvalid.
             ++ now apply Pos.eqb_eq.
          -- exact (Hagree z).
  Qed.

  (** Filling returns the candidate value exactly at the listed keys. *)
  Lemma fill_lookup : forall xs m base x,
    Bindings.lookup (Bindings.fill xs m base) x =
      if Bindings.mem x xs then Some (Checker.look m x) else Bindings.lookup base x.
  Proof.
    induction xs as [|y rest IH]; intros m base x; cbn [Bindings.fill Bindings.mem].
    - reflexivity.
    - rewrite lookup_set, IH.
      change (Bindings.mem x (y :: rest)) with (S.key_eqb x y || Bindings.mem x rest)%bool.
      destruct (S.key_eqb_spec x y) as [->|Hneq]; reflexivity.
  Qed.

  (** Deduplication preserves key membership. *)
  Lemma unique_spec : forall xs x, In x (Bindings.unique xs) <-> In x xs.
  Proof.
    induction xs as [|y rest IH]; intro x; cbn [Bindings.unique].
    - reflexivity.
    - destruct (Bindings.mem y rest) eqn:Hmem.
      + rewrite IH; cbn [In]; split; [now right|].
        intros [->|Hin]; [now apply mem_spec in Hmem|exact Hin].
      + cbn [In]; rewrite IH; reflexivity.
  Qed.

  (** Deduplication lists each key at most once. *)
  Lemma unique_nodup : forall xs, NoDup (Bindings.unique xs).
  Proof.
    induction xs as [|x rest IH]; cbn [Bindings.unique].
    - constructor.
    - destruct (Bindings.mem x rest) eqn:Hmem; [exact IH|].
      constructor; [|exact IH].
      intro Hin.
      pose proof (proj1 (unique_spec rest x) Hin) as Hrest.
      pose proof (proj2 (mem_spec x rest) Hrest) as Htrue.
      congruence.
  Qed.

  (** A canonical insertion supplies its value to raw candidate lookup. *)
  Lemma raw_set : forall m x y v,
    look_or S.key_code L.bot (PTrieCode.set (S.key_code y) (y, v) m) x =
      if S.key_eqb x y then v else look_or S.key_code L.bot m x.
  Proof.
    intros m x y v; destruct (S.key_eqb_spec x y) as [->|Hneq].
    - unfold look_or; rewrite PTrie.get_set_same; reflexivity.
    - unfold look_or; rewrite PTrie.get_set_other; [reflexivity|].
      intro Hcode; apply Hneq, S.key_code_inj, Hcode.
  Qed.

  (** Coherent later seed updates preserve an already restored value. *)
  Lemma restore_preserves : forall fz m x v,
    (forall y w, In (y, w) fz -> y = x -> w = v) ->
    look_or S.key_code L.bot m x = v ->
    look_or S.key_code L.bot (Bindings.restore fz m) x = v.
  Proof.
    induction fz as [|[y w] rest IH]; intros m x v Hcoherent Hlook.
    - exact Hlook.
    - cbn [Bindings.restore fold_left fst].
      apply IH.
      + intros z a Hin Heq; apply (Hcoherent z a); [now right|exact Heq].
      + rewrite raw_set.
        destruct (S.key_eqb_spec x y) as [->|Hneq]; [|exact Hlook].
        apply (Hcoherent y w); [now left|reflexivity].
  Qed.

  (** A coherent seed list restores every listed value exactly. *)
  Lemma restore_hit : forall fz m x v,
    (forall w, In (x, w) fz -> w = v) -> In (x, v) fz ->
    look_or S.key_code L.bot (Bindings.restore fz m) x = v.
  Proof.
    induction fz as [|[y w] rest IH]; intros m x v Hcoherent Hin.
    - contradiction.
    - cbn [Bindings.restore fold_left fst].
      destruct Hin as [Heq|Hin].
      + inversion Heq; subst y w.
        apply restore_preserves.
        * intros z a Hz ->; apply Hcoherent; now right.
        * rewrite raw_set; destruct (S.key_eqb_spec x x); congruence.
      + apply IH.
        * intros a Ha; apply Hcoherent; now right.
        * exact Hin.
  Qed.

  (** Encoded key comparison agrees with the source key comparison. *)
  Lemma key_code_eqb : forall x y,
    Pos.eqb (S.key_code x) (S.key_code y) = S.key_eqb x y.
  Proof.
    intros x y; destruct (S.key_eqb_spec x y) as [->|Hneq].
    - apply Pos.eqb_refl.
    - apply Pos.eqb_neq; intro Hcodes; apply Hneq; apply S.key_code_inj; exact Hcodes.
  Qed.

  (** Deleting a key list removes exactly its validated bindings. *)
  Lemma lookup_remove_keys : forall bad m x,
    Bindings.lookup (Bindings.remove_keys bad m) x =
      if Bindings.mem x bad then None else Bindings.lookup m x.
  Proof.
    induction bad as [|y bad IH]; intros m x.
    - reflexivity.
    - change (Bindings.lookup (Bindings.remove_keys bad (PTrieCode.remove (S.key_code y) m)) x =
        if (S.key_eqb x y || Bindings.mem x bad)%bool then None else Bindings.lookup m x).
      rewrite IH, lookup_remove, key_code_eqb.
      destruct (S.key_eqb x y), (Bindings.mem x bad); reflexivity.
  Qed.

  (** Restoring bounded seeds preserves a pointwise bound on the raw candidate lookup. *)
  Lemma restore_below : forall fz m upper,
    (forall x, L.leb (look_or S.key_code L.bot m x) (upper x) = true) ->
    (forall x v, In (x, v) fz -> L.leb v (upper x) = true) ->
    forall x, L.leb (look_or S.key_code L.bot (Bindings.restore fz m) x) (upper x) = true.
  Proof.
    induction fz as [|[y v] rest IH]; intros m upper Hmap Hseeds x.
    - exact (Hmap x).
    - cbn [Bindings.restore fold_left fst].
      apply IH.
      + intro z; rewrite raw_set.
        destruct (S.key_eqb_spec z y) as [->|Hneq].
        * apply (Hseeds y v); now left.
        * exact (Hmap z).
      + intros z w Hin; apply (Hseeds z w); now right.
  Qed.
End SourceBindingFacts.

(** * Agreement on declared row support *)

Module SourceRowFacts (L : LATTICE) (S : SYSTEM L).
  (** Pointwise Boolean agreement on a list preserves its universal check. *)
  Lemma forallb_same : forall A (xs : list A) f g,
    (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
  Proof.
    intros A xs; induction xs as [|x rest IH]; intros f g Hagree; cbn [forallb].
    - reflexivity.
    - rewrite (Hagree x (or_introl eq_refl)); f_equal.
      apply IH; intros y Hy; apply Hagree; now right.
  Qed.

  (** A listed row observes only its declared reads and writes. *)
  Lemma row_look_transport : forall p r a b,
    S.wf p -> In r (S.rows p) ->
    (forall x, In x (S.writes p r ++ S.deps p r) -> a x = b x) ->
    row_ok L.leb a (S.target p r) (S.eval p r a) =
      row_ok L.leb b (S.target p r) (S.eval p r b).
  Proof.
    intros p r a b Hwf Hr Hagree.
    assert (Heval : S.eval p r a = S.eval p r b).
    { apply S.reads_within; [exact Hwf|exact Hr|].
      intros x Hx; apply Hagree; apply in_or_app; now right. }
    rewrite Heval.
    destruct (S.eval p r b) as [[v ss]|] eqn:Hout; cbn [row_ok]; [|reflexivity].
    assert (Htarget : a (S.target p r) = b (S.target p r)).
    { apply Hagree; unfold S.writes; apply in_or_app; left; now left. }
    rewrite Htarget; f_equal; apply forallb_same.
    intros [x w] Hside; cbn [fst snd]; rewrite Hagree; [reflexivity|].
    unfold S.writes; apply in_or_app; left; right.
    eapply S.sides_within; eauto.
  Qed.
End SourceRowFacts.

(** * Global extensions of checked supports *)

Module SourceTopFacts (L : LATTICE) (Top : HAS_TOP L) (S : SYSTEM L).
  Module Rows := SourceRowFacts L S.

  (** The Boolean support contains every write and read of a row touching it. *)
  Definition support_closed (p : S.prog) (E : S.key -> bool) : Prop :=
    forall r y x, In r (S.rows p) -> In y (S.writes p r) -> E y = true ->
      In x (S.writes p r ++ S.deps p r) -> E x = true.

  Definition top_extend (E : S.key -> bool) (s : S.key -> L.t) (x : S.key) : L.t :=
    if E x then s x else Top.top.

  (** Supported keys retain their supplied values. *)
  Lemma top_extend_on : forall E s x, E x = true -> top_extend E s x = s x.
  Proof.
    intros E s x HE; unfold top_extend; now rewrite HE.
  Qed.

  (** Unsupported keys receive top. *)
  Lemma top_extend_off : forall E s x, E x = false -> top_extend E s x = Top.top.
  Proof.
    intros E s x HE; unfold top_extend; now rewrite HE.
  Qed.

  (** A row with no supported write is accepted when all its targets receive top. *)
  Lemma top_extend_row_absent : forall p E s r,
    S.wf p -> In r (S.rows p) ->
    (forall x, In x (S.writes p r) -> E x = false) ->
    row_ok L.leb (top_extend E s) (S.target p r) (S.eval p r (top_extend E s)) = true.
  Proof.
    intros p E s r Hwf Hr Habsent.
    destruct (S.eval p r (top_extend E s)) as [[a ss]|] eqn:Hout.
    - cbn [row_ok]; apply andb_true_iff; split.
      + unfold top_extend.
        rewrite (Habsent (S.target p r) (or_introl eq_refl)); apply Top.top_greatest.
      + apply (proj2 (@forallb_forall _ _ _)); intros [x b] Hside; cbn [fst snd].
        assert (Hx : In x (S.writes p r)).
        { unfold S.writes; right; eapply S.sides_within; eassumption. }
        unfold top_extend; rewrite (Habsent x Hx); apply Top.top_greatest.
    - exfalso; apply (S.eval_total p r (top_extend E s) Hwf Hr); exact Hout.
  Qed.

  (** Accepted rows touching a closed support suffice for a global top extension. *)
  Lemma top_extend_post : forall p E s,
    S.wf p -> support_closed p E ->
    (forall r y, In r (S.rows p) -> In y (S.writes p r) -> E y = true ->
      row_ok L.leb s (S.target p r) (S.eval p r s) = true) ->
    S.post_solution p (top_extend E s).
  Proof.
    intros p E s Hwf Hclosed Hpost r Hr.
    destruct (existsb E (S.writes p r)) eqn:Hactive.
    - apply existsb_exists in Hactive as [y [Hy HE]].
      pose proof (Hpost r y Hr Hy HE) as Hrow.
      assert (Hagree : forall x, In x (S.writes p r ++ S.deps p r) ->
        s x = top_extend E s x).
      { intros x Hx; symmetry; apply top_extend_on; exact (Hclosed r y x Hr Hy HE Hx). }
      rewrite (Rows.row_look_transport p r s (top_extend E s) Hwf Hr Hagree) in Hrow.
      exact Hrow.
    - apply top_extend_row_absent; [exact Hwf|exact Hr|].
      intros x Hx; destruct (E x) eqn:HE; [|reflexivity].
      assert (Hexists : existsb E (S.writes p r) = true).
      { apply existsb_exists; exists x; split; assumption. }
      congruence.
  Qed.
End SourceTopFacts.

(** ** Canonical inventories for validated source bindings *)

Module SourceBindingInventory (L : LATTICE) (S : SYSTEM L)
    (Checker : CHECK_OPS L S).
  Include SourceBindingFacts L S Checker.

  Definition canonical (m : kmap S.key L.t) : Prop :=
    forall path x v, PTrieCode.get path m = Some (x, v) -> path = S.key_code x.

  Definition raw_keys (m : kmap S.key L.t) : list S.key :=
    map (fun binding => fst (snd binding)) (PTrieCode.elements m).

  (** A validated inventory ignores a cell stored away from its payload key. *)
  Definition valid_keys (m : kmap S.key L.t) : list S.key :=
    map (fun binding => fst (snd binding))
      (filter (fun binding => Pos.eqb (fst binding)
        (S.key_code (fst (snd binding)))) (PTrieCode.elements m)).

  (** Guarded lookup accepts exactly a payload carrying the queried key. *)
  Lemma raw_lookup_cell : forall m x v,
    Bindings.lookup m x = Some v <->
    PTrieCode.get (S.key_code x) m = Some (x, v).
  Proof.
    intros m x v; unfold Bindings.lookup.
    destruct (PTrieCode.get (S.key_code x) m) as [[y w]|] eqn:Hget.
    - destruct (S.key_eqb_spec x y) as [->|Hneq].
      + split; intro Heq; now inversion Heq.
      + split; intro Heq; [discriminate Heq|congruence].
    - split; intro Heq; discriminate Heq.
  Qed.

  Lemma valid_keys_dom : forall m x,
    In x (valid_keys m) <-> exists v, Bindings.lookup m x = Some v.
  Proof.
    intros m x; unfold valid_keys; split.
    - intros Hin; apply in_map_iff in Hin as [[path [y v]] [Heq Hin]].
      cbn in Heq; subst y; apply filter_In in Hin as [Hin Hpath].
      apply Pos.eqb_eq in Hpath; cbn [fst snd] in Hpath; subst path.
      apply PTrie.elements_spec in Hin; exists v; now apply raw_lookup_cell.
    - intros [v Hlookup]; apply raw_lookup_cell in Hlookup.
      apply in_map_iff; exists (S.key_code x, (x, v)); split; [reflexivity|].
      apply filter_In; split; [now apply PTrie.elements_spec|].
      cbn [fst snd]; apply Pos.eqb_refl.
  Qed.

  Lemma valid_keys_nodup : forall m, NoDup (valid_keys m).
  Proof.
    intro m; unfold valid_keys.
    apply NoDup_map_inv with (f := S.key_code).
    assert (Hcodes : map S.key_code
      (map (fun binding => fst (snd binding))
        (filter (fun binding => Pos.eqb (fst binding)
          (S.key_code (fst (snd binding)))) (PTrieCode.elements m))) =
      map fst (filter (fun binding => Pos.eqb (fst binding)
        (S.key_code (fst (snd binding)))) (PTrieCode.elements m))).
    { rewrite map_map; apply map_ext_in; intros [path [x v]] Hin; cbn [fst snd] in *.
      apply filter_In in Hin as [_ Hpath]; apply Pos.eqb_eq in Hpath.
      cbn [fst snd] in Hpath; now symmetry. }
    rewrite Hcodes; clear Hcodes.
    assert (Hcells : NoDup (map fst (PTrieCode.elements m)))
      by apply PTrie.elements_nodup.
    remember (PTrieCode.elements m) as cells eqn:Hcells_eq.
    clear Hcells_eq; induction cells as [|cell rest IH].
    - constructor.
    - inversion Hcells as [|? ? Habsent Hrest]; subst.
      cbn [filter map].
      destruct (Pos.eqb (fst cell) (S.key_code (fst (snd cell)))).
      + constructor; [|apply IH; exact Hrest].
        intro Hin; apply Habsent.
        apply in_map_iff in Hin as [other [Heq Hother]].
        apply in_map_iff; exists other; split; [exact Heq|].
        now apply filter_In in Hother as [Hother _].
      + apply IH; exact Hrest.
  Qed.

  (** Every canonical inventory key is present, and every present key is listed. *)
  Lemma raw_keys_dom : forall m, canonical m -> forall x,
    In x (raw_keys m) <-> exists v, Bindings.lookup m x = Some v.
  Proof.
    intros m Hcanonical x; unfold raw_keys; split.
    - intros Hin; apply in_map_iff in Hin as [[path [y v]] [Heq Hin]].
      cbn in Heq; subst y; apply PTrie.elements_spec in Hin.
      pose proof (Hcanonical path x v Hin) as Hpath; subst path.
      exists v; now apply raw_lookup_cell.
    - intros [v Hlookup]; apply raw_lookup_cell in Hlookup.
      apply in_map_iff; exists (S.key_code x, (x, v)); split; [reflexivity|].
      now apply PTrie.elements_spec.
  Qed.

  (** Encoding a canonical key inventory recovers the distinct trie paths. *)
  Lemma raw_keys_codes : forall m, canonical m ->
    map S.key_code (raw_keys m) = map fst (PTrieCode.elements m).
  Proof.
    intros m Hcanonical; unfold raw_keys; rewrite map_map; apply map_ext_in.
    intros [path [x v]] Hin; cbn; symmetry; apply (Hcanonical path x v).
    now apply PTrie.elements_spec.
  Qed.

  Lemma raw_keys_nodup : forall m, canonical m -> NoDup (raw_keys m).
  Proof.
    intros m Hcanonical; apply NoDup_map_inv with (f := S.key_code).
    rewrite raw_keys_codes by exact Hcanonical; apply PTrie.elements_nodup.
  Qed.

  (** A duplicate-free mapped list identifies equal fibers uniquely. *)
  Lemma nodup_map_fiber : forall A B (f : A -> B) xs a b,
    NoDup (map f xs) -> In a xs -> In b xs -> f a = f b -> a = b.
  Proof.
    intros A B f xs; induction xs as [|head rest IH]; intros a b Hnodup Ha Hb Heq.
    - contradiction.
    - inversion Hnodup as [|? ? Hnot Hrest]; subst.
      destruct Ha as [->|Ha], Hb as [->|Hb]; [reflexivity| | |].
      + exfalso; apply Hnot; rewrite Heq; now apply in_map.
      + exfalso; apply Hnot; rewrite <- Heq; now apply in_map.
      + eapply IH; eauto.
  Qed.

  (** The public inventory/domain and uniqueness laws already force canonical cells. *)
  Lemma canonical_of_inventory : forall m,
    (forall x, In x (raw_keys m) <-> exists v, Bindings.lookup m x = Some v) ->
    NoDup (raw_keys m) -> canonical m.
  Proof.
    intros m Hdom Hnodup path x v Hget.
    assert (Hin : In (path, (x, v)) (PTrieCode.elements m)).
    { now apply PTrie.elements_spec. }
    assert (Hx : In x (raw_keys m)).
    { unfold raw_keys; apply in_map_iff; exists (path, (x, v)); auto. }
    apply Hdom in Hx as [w Hw]; apply raw_lookup_cell in Hw.
    assert (Hother : In (S.key_code x, (x, w)) (PTrieCode.elements m)).
    { now apply PTrie.elements_spec. }
    pose proof (nodup_map_fiber _ _ (fun binding => fst (snd binding))
      (PTrieCode.elements m) (path, (x, v)) (S.key_code x, (x, w))
      Hnodup Hin Hother eq_refl) as Heq.
    now inversion Heq.
  Qed.

  Lemma canonical_empty : canonical (@PTrieCode.empty (S.key * L.t)).
  Proof.
    intros path x v Hget; rewrite PTrie.get_empty in Hget; discriminate Hget.
  Qed.

  (** Pruning removes cells without changing any surviving raw payload. *)
  Lemma prune_values_submap : forall cells m path xv,
    PTrieCode.get path (Bindings.prune_values cells m) = Some xv ->
    PTrieCode.get path m = Some xv.
  Proof.
    induction cells as [|[q [x v]] rest IH]; intros m path xv Hget.
    - exact Hget.
    - cbn [Bindings.prune_values] in Hget.
      destruct (Pos.eqb q (S.key_code x)) eqn:Hvalid.
      + exact (IH m path xv Hget).
      + apply IH in Hget.
        destruct (Pos.eqb path q) eqn:Hpath.
        * apply Pos.eqb_eq in Hpath; subst path.
          rewrite PTrie.get_remove_same in Hget; discriminate Hget.
        * apply Pos.eqb_neq in Hpath.
          now rewrite PTrie.get_remove_other in Hget by exact Hpath.
  Qed.

  Lemma prune_values_absent : forall cells m path,
    PTrieCode.get path m = None ->
    PTrieCode.get path (Bindings.prune_values cells m) = None.
  Proof.
    intros cells m path Hnone.
    destruct (PTrieCode.get path (Bindings.prune_values cells m)) as [xv|] eqn:Hget.
    - apply prune_values_submap in Hget; rewrite Hnone in Hget; discriminate Hget.
    - reflexivity.
  Qed.

  (** Every malformed listed cell is removed, independently of the starting payload. *)
  Lemma prune_values_deletes : forall cells path x v m,
    In (path, (x, v)) cells -> Pos.eqb path (S.key_code x) = false ->
    PTrieCode.get path (Bindings.prune_values cells m) = None.
  Proof.
    induction cells as [|[q [y w]] rest IH]; intros path x v m Hin Hbad.
    - contradiction.
    - cbn [Bindings.prune_values]; destruct Hin as [Heq|Hin].
      + inversion Heq; subst q y w; rewrite Hbad.
        apply prune_values_absent; apply PTrie.get_remove_same.
      + destruct (Pos.eqb q (S.key_code y)); eapply IH; eauto.
  Qed.

  Lemma prune_values_canonical : forall m,
    canonical (Bindings.prune_values (PTrieCode.elements m) m).
  Proof.
    intros m path x v Hget.
    pose proof (prune_values_submap _ _ _ _ Hget) as Horiginal.
    apply PTrie.elements_spec in Horiginal.
    destruct (Pos.eqb path (S.key_code x)) eqn:Hpath.
    - now apply Pos.eqb_eq.
    - pose proof (prune_values_deletes _ path x v m Horiginal Hpath) as Hnone.
      rewrite Hnone in Hget; discriminate Hget.
  Qed.

  Lemma prune_values_raw_keys_subset : forall cells m x,
    In x (raw_keys (Bindings.prune_values cells m)) -> In x (raw_keys m).
  Proof.
    intros cells m x Hin; unfold raw_keys in *.
    apply in_map_iff in Hin as [[path [y v]] [Heq Hin]].
    apply in_map_iff; exists (path, (y, v)); split; [exact Heq|].
    apply PTrie.elements_spec; apply prune_values_submap with (cells := cells).
    now apply PTrie.elements_spec.
  Qed.

  (** Filling arbitrary candidate values stores only canonical payloads. *)
  Lemma fill_canonical : forall xs m base,
    canonical base -> canonical (Bindings.fill xs m base).
  Proof.
    induction xs as [|y rest IH]; intros m base Hcanonical path x v Hget.
    - exact (Hcanonical path x v Hget).
    - cbn [Bindings.fill] in Hget.
      destruct (Pos.eqb path (S.key_code y)) eqn:Hpath.
      + apply Pos.eqb_eq in Hpath; subst path.
        rewrite PTrie.get_set_same in Hget; inversion Hget; reflexivity.
      + apply Pos.eqb_neq in Hpath.
        rewrite PTrie.get_set_other in Hget by exact Hpath.
        exact (IH m base Hcanonical path x v Hget).
  Qed.

  Lemma fill_raw_keys : forall xs m base, canonical base -> forall x,
    In x (raw_keys (Bindings.fill xs m base)) <-> In x xs \/ In x (raw_keys base).
  Proof.
    intros xs m base Hcanonical x.
    rewrite (raw_keys_dom (Bindings.fill xs m base)
      (fill_canonical xs m base Hcanonical) x); split.
    - intros [v Hget]; rewrite fill_lookup in Hget.
      destruct (Bindings.mem x xs) eqn:Hmem.
      + left; now apply mem_spec.
      + right; apply (proj2 (raw_keys_dom base Hcanonical x)); now exists v.
    - intros [Hin|Hin].
      + exists (Checker.look m x); rewrite fill_lookup.
        rewrite (proj2 (mem_spec x xs) Hin); reflexivity.
      + apply (proj1 (raw_keys_dom base Hcanonical x)) in Hin as [v Hget].
        destruct (Bindings.mem x xs) eqn:Hmem.
        * exists (Checker.look m x); now rewrite fill_lookup, Hmem.
        * exists v; now rewrite fill_lookup, Hmem.
  Qed.

  (** Raw deletion changes only the selected trie path. *)
  Lemma raw_remove : forall A path (m : PTrieCode.t A) q,
    PTrieCode.get q (PTrieCode.remove path m) =
      if Pos.eqb q path then None else PTrieCode.get q m.
  Proof.
    intros A path m q; destruct (Pos.eqb q path) eqn:Hpath.
    - apply Pos.eqb_eq in Hpath; subst q; apply PTrie.get_remove_same.
    - apply Pos.eqb_neq in Hpath; now apply PTrie.get_remove_other.
  Qed.

  Lemma raw_remove_keys : forall A bad (m : PTrieCode.t A) path,
    PTrieCode.get path (Bindings.remove_keys bad m) =
      if existsb (fun x => Pos.eqb path (S.key_code x)) bad
      then None else PTrieCode.get path m.
  Proof.
    intros A bad; induction bad as [|y rest IH]; intros m path.
    - reflexivity.
    - change (PTrieCode.get path
        (Bindings.remove_keys rest (PTrieCode.remove (S.key_code y) m)) =
        if (Pos.eqb path (S.key_code y) ||
          existsb (fun x => Pos.eqb path (S.key_code x)) rest)%bool
        then None else PTrieCode.get path m).
      rewrite IH, raw_remove.
      destruct (Pos.eqb path (S.key_code y)),
        (existsb (fun x => Pos.eqb path (S.key_code x)) rest); reflexivity.
  Qed.

  Lemma raw_get_remove_keys : forall A bad (m : PTrieCode.t A) x,
    PTrieCode.get (S.key_code x) (Bindings.remove_keys bad m) =
      if Bindings.mem x bad then None else PTrieCode.get (S.key_code x) m.
  Proof.
    intros A bad m x; rewrite raw_remove_keys; unfold Bindings.mem.
    assert (Htest : existsb (fun y => Pos.eqb (S.key_code x) (S.key_code y)) bad =
      existsb (S.key_eqb x) bad).
    { induction bad as [|y rest IH]; cbn [existsb]; [reflexivity|].
      now rewrite key_code_eqb, IH. }
    now rewrite Htest.
  Qed.

  Lemma remove_keys_submap : forall A bad (m : PTrieCode.t A) path a,
    PTrieCode.get path (Bindings.remove_keys bad m) = Some a ->
    PTrieCode.get path m = Some a.
  Proof.
    intros A bad m path a Hget; rewrite raw_remove_keys in Hget.
    destruct (existsb (fun x => Pos.eqb path (S.key_code x)) bad);
      [discriminate Hget|exact Hget].
  Qed.

  Lemma remove_keys_canonical : forall bad m,
    canonical m -> canonical (Bindings.remove_keys bad m).
  Proof.
    intros bad m Hcanonical path x v Hget; apply (Hcanonical path x v).
    now apply remove_keys_submap in Hget.
  Qed.

  Lemma raw_keys_remove_subset : forall bad m x,
    In x (raw_keys (Bindings.remove_keys bad m)) -> In x (raw_keys m).
  Proof.
    intros bad m x Hin; unfold raw_keys in *.
    apply in_map_iff in Hin as [[path [y v]] [Heq Hin]].
    apply in_map_iff; exists (path, (y, v)); split; [exact Heq|].
    apply PTrie.elements_spec; apply remove_keys_submap with (bad := bad).
    now apply PTrie.elements_spec.
  Qed.
End SourceBindingInventory.

(** An empty accumulated set activates no footprint. *)
Lemma footprint_active_empty : forall K A (eqb : K -> K -> bool) (triggers : A -> list K) a,
  footprint_active eqb triggers [] a = false.
Proof.
  intros K A eqb triggers a; unfold footprint_active, footprint_mem.
  induction (triggers a); cbn [existsb]; assumption || reflexivity.
Qed.

(** Selection finds no item when the accumulated set is empty. *)
Lemma footprint_pick_empty : forall K A (eqb : K -> K -> bool) (triggers : A -> list K) xs,
  footprint_pick eqb triggers [] xs = None.
Proof.
  intros K A eqb triggers xs; induction xs as [|a rest IH]; cbn [footprint_pick].
  - reflexivity.
  - rewrite footprint_active_empty, IH; reflexivity.
Qed.

(** Saturation without seed keys retains an empty accumulated set. *)
Lemma footprint_close_empty : forall K A (eqb : K -> K -> bool)
    (triggers outputs : A -> list K) allowed fuel xs,
  footprint_seen (footprint_close eqb triggers outputs allowed fuel [] xs) = [].
Proof.
  intros K A eqb triggers outputs allowed fuel xs; destruct fuel; cbn [footprint_close].
  - reflexivity.
  - rewrite footprint_pick_empty; reflexivity.
Qed.
