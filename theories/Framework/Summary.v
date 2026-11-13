(** * Function summary constraints

    Local rows and call rows compute summary contributions.
    For example, a call row emits its callee entry as a side contribution.
    Builds on: Framework.SummarySig and Fixpoint.Query. *)

From Stdlib Require Import List Bool NArith.
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
  Proof. Admitted. (* STUB *)
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted. (* STUB *)
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted. (* STUB *)
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted. (* STUB *)
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof. Admitted. (* STUB *)
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted. (* STUB *)
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted. (* STUB *)
  (** Function keys use the client's encoding. *)
  Lemma key_code_spec : key_code = F.encode.
  Proof. Admitted. (* STUB *)
  (** Function keys use the client's equality test. *)
  Lemma key_eqb_specification : key_eqb = F.eqb.
  Proof. Admitted. (* STUB *)
  (** Local rows precede calls in function, site and resolver order. *)
  Lemma rows_spec : forall p, CL.wf p -> rows p = map SummaryLocal (CL.functions p) ++
    flat_map (fun f => flat_map (fun site => map (SummaryCall site) (CL.resolve p site))
      (CL.sites_of p f)) (CL.functions p).
  Proof. Admitted. (* STUB *)
  (** A local row targets its own function. *)
  Lemma target_local : forall p f, target p (SummaryLocal f) = f.
  Proof. Admitted. (* STUB *)
  (** A lifted row targets its call site's caller. *)
  Lemma target_call : forall p site g, target p (SummaryCall site g) = CL.caller_of p site.
  Proof. Admitted. (* STUB *)
  (** Local summaries have no side contributions. *)
  Lemma eval_local : forall p f look,
    eval p (SummaryLocal f) look = Some (B.local p f, nil).
  Proof. Admitted. (* STUB *)
  (** Calls lift their callee summary and contribute a callee entry fact. *)
  Lemma eval_call : forall p site g look, eval p (SummaryCall site g) look =
    Some (B.via_call p site g (look g), (g, B.entry p site g) :: nil).
  Proof. Admitted. (* STUB *)
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
  Lemma covers : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t f, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In f (K.active s) -> SL.gamma_step (look f) s t.
  Proof. Admitted. (* CONVERT: sound: The variable frames_cover was not found *)
  Lemma covers_entry : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t site, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In site (CL.sites_of p (K.here s)) -> In (K.here t) (CL.resolve p site) ->
      K.frames t = (K.here s, site) :: K.frames s -> SL.gamma_entry (look (K.here t)) t.
  Proof. Admitted. (* STUB *)
  Lemma covers_finished : forall p look f s t, CL.wf p -> A.post_solution p look ->
    covered_run (M.step p)
      (fun u _ => reachable (M.initial p) (M.step p) u /\ In f (K.active u)) s t ->
    covered_run (M.step p) (SL.gamma_step (look f)) s t.
  Proof. Admitted. (* STUB *)
End SummarySound.
