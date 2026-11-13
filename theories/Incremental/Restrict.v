(** * Seeded restrictions of local systems

    A restricted program stores the original program, frozen values and selected rows.
    For example, selecting no source rows still retains any seed rows.
    Builds on: RestrictSig. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Std Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
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
  Definition c_sys : N := 1. (* STUB *)
  (** Step budgets grow with the size of abstract values. *)
  Lemma row_work_mono : forall p s s', s <= s' -> (row_work p s <= row_work p s')%N.
  Proof. Admitted. (* STUB *)
  (** The program key budget covers all declared reads and writes. *)
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof. Admitted. (* STUB *)
  (** Encoding costs are linear in the resulting code size. *)
  Lemma T_key_code_le : forall x, (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof. Admitted. (* STUB *)
  (** Equality costs are bounded by the first key's code size. *)
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof. Admitted. (* STUB *)
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
    Definition c_res : N := 1. (* STUB *)
  (** Restricted key budgets cover the original program and frozen keys. *)
  Lemma mk_kw : forall p fz rs,
    RS.kw (mk p fz rs) <= fold_right (fun xv n => Nat.max (S.key_bits (fst xv)) n)
      (S.kw p) fz.
  Proof. Admitted. (* STUB *)
  (** Restricted row work adds the largest frozen value to the source row budget. *)
  Lemma mk_row_work : forall p fz rs s,
    (RS.row_work (mk p fz rs) s <= S.row_work p s +
      N.of_nat (fold_right (fun xv n => Nat.max (L.size (snd xv)) n) 0%nat fz) + 1)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_mk_le : forall p fz rs,
    (T_mk p fz rs <= c_res *
      N.of_nat ((fold_right Nat.add 0
        (map (fun r => Pos.size_nat (S.row_code r) + 1) rs) +
       fold_right Nat.add 0
        (map (fun xv => S.key_bits (fst xv) + L.size (snd xv) + 1) fz) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)

    (** Restricted post-solutions accept every primary and side write of a selected row. *)
    Lemma restrict_writes : forall p fz rs s r, RS.post_solution (mk p fz rs) s ->
      In r rs -> row_ok L.leb s (S.target p r) (S.eval p r s) = true.
    Proof.
      intros p fz rs s r Hpost Hin.
      exact (proj1 (restrict_post p fz rs s Hpost) r Hin).
    Qed.

  End Impl.
End RestrictT.
