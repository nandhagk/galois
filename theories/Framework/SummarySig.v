(** * Function summary constraints

    Local rows and lifted callee rows describe activity in every active function.
    For example, a recursive call reads its callee summary and contributes its entry fact.
    Builds on: Program.CallsSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import SemanticsSig CallsSig.

Inductive summary_row (F Site : Type) :=
  | SummaryLocal (function : F)
  | SummaryCall (site : Site) (callee : F).

Arguments SummaryLocal {F Site}.
Arguments SummaryCall {F Site}.

(** Runs retain the same predicate on each concrete transition. *)
Inductive covered_run {S} (step covered : S -> S -> Prop) : S -> S -> Prop :=
  | Covered_refl : forall s, covered_run step covered s s
  | Covered_next : forall s u t, step s u -> covered s u ->
      covered_run step covered u t -> covered_run step covered s t.

Module Type BODY_OPS (P : TYPE) (F Site : KEY_OPS) (L : LATTICE_OPS).
  Parameter local : P.t -> F.t -> L.t.
  Parameter via_call : P.t -> Site.t -> F.t -> L.t -> L.t.
  Parameter entry : P.t -> Site.t -> F.t -> L.t.
End BODY_OPS.

Module Type BODY_TIME (P : TYPE) (F Site : KEY_T) (L : LATTICE_T)
    (Import B : BODY_OPS P F Site L).
  Parameter T_local : P.t -> F.t -> N.
  Parameter T_via_call : P.t -> Site.t -> F.t -> L.t -> N.
  Parameter T_entry : P.t -> Site.t -> F.t -> N.
End BODY_TIME.

Module Type BODY_T (P : TYPE) (F Site : KEY_T) (L : LATTICE_T) :=
  BODY_OPS P F Site L <+ BODY_TIME P F Site L.

Module Type SUMMARY_OPS (P : TYPE) (F Site : KEY_OPS) (L : LATTICE_OPS).
  Include SYSTEM_OPS L
    with Definition prog := P.t
    with Definition key := F.t
    with Definition row := summary_row F.t Site.t
    with Definition frame := (Site.t * F.t)%type.
End SUMMARY_OPS.

Module Type SUMMARY_LAWS (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L)
    (Import A : SUMMARY_OPS P F Site L) (Import AS : SYSTEM_SPEC L A).
  (** Function keys use the client's encoding. *)
  Parameter key_code_spec : key_code = F.encode.
  (** Function keys use the client's equality test. *)
  Parameter key_eqb_specification : key_eqb = F.eqb.
  (** Local rows precede calls in function, site and resolver order. *)
  Parameter rows_spec : forall p, rows p = map SummaryLocal (CL.functions p) ++
    flat_map (fun f => flat_map (fun site => map (SummaryCall site) (CL.resolve p site))
      (CL.sites_of p f)) (CL.functions p).
  (** A local row targets its own function. *)
  Parameter target_local : forall p f, target p (SummaryLocal f) = f.
  (** A lifted row targets its call site's caller. *)
  Parameter target_call : forall p site g, target p (SummaryCall site g) = CL.caller_of p site.
  (** Local summaries have no side contributions. *)
  Parameter eval_local : forall p f look,
    eval p (SummaryLocal f) look = Some (B.local p f, nil).
  (** Calls lift their callee summary and contribute a callee entry fact. *)
  Parameter eval_call : forall p site g look, eval p (SummaryCall site g) look =
    Some (B.via_call p site g (look g), (g, B.entry p site g) :: nil).
End SUMMARY_LAWS.

Module Type SUMMARY (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L) :=
  SUMMARY_OPS P F Site L <+ SYSTEM_SPEC L <+ SYSTEM_LAWS L <+
  SUMMARY_LAWS P F Site CL L B.

Module Type SUMMARY_TIME (P : TYPE) (F Site : KEY_T) (CL : CALLS_T P F Site)
    (L : LATTICE_T) (B : BODY_T P F Site L)
    (Import A : SUMMARY P F Site CL L B).
  Include SYSTEM_TIME L A.
  (* SIG-QUESTION: CALLS_T readers need numeric budgets or a prepared presentation.
     T_resume calls B.via_call on an arbitrary lattice value, but BODY_T supplies
     no work bound as a function of that value's size. *)
End SUMMARY_TIME.

Module Type SUMMARY_T (P : TYPE) (F Site : KEY_T) (CL : CALLS_T P F Site)
    (L : LATTICE_T) (B : BODY_T P F Site L) :=
  SUMMARY P F Site CL L B <+ SUMMARY_TIME P F Site CL L B.

Module Type SUMMARY_LINK (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L) (M : SEMANTICS P)
    (K : CALLS_LINK P F Site CL M).
  Parameter gamma_step : L.t -> M.state -> M.state -> Prop.
  Parameter gamma_entry : L.t -> M.state -> Prop.
  (** Abstract inclusion retains concrete transition coverage. *)
  Parameter step_mono : forall a b s t,
    L.leb a b = true -> gamma_step a s t -> gamma_step b s t.
  (** Abstract inclusion retains concrete call-entry coverage. *)
  Parameter entry_mono : forall a b s,
    L.leb a b = true -> gamma_entry a s -> gamma_entry b s.
  (** The active function's local summary describes its concrete transition. *)
  Parameter local_sound : forall p s t,
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    gamma_step (B.local p (K.here s)) s t.
  (** Lifting retains the same transition at its actual suspended call site. *)
  Parameter call_sound : forall p s t site g a,
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    In (CL.caller_of p site, site) (K.frames s) ->
    gamma_step a s t -> gamma_step (B.via_call p site g a) s t.
  (** A pushed resolved call satisfies its supplied entry fact. *)
  Parameter entry_sound : forall p s t site,
    reachable (M.initial p) (M.step p) s -> M.step p s t ->
    In site (CL.sites_of p (K.here s)) -> In (K.here t) (CL.resolve p site) ->
    K.frames t = (K.here s, site) :: K.frames s ->
    gamma_entry (B.entry p site (K.here t)) t.
End SUMMARY_LINK.

Module Type SUMMARY_SOUND (P : TYPE) (F Site : KEY) (CL : CALLS P F Site)
    (L : LATTICE) (B : BODY_OPS P F Site L) (A : SUMMARY P F Site CL L B)
    (M : SEMANTICS P) (K : CALLS_LINK P F Site CL M)
    (SL : SUMMARY_LINK P F Site CL L B M K).
  (** Every active caller's summary describes the same concrete transition. *)
  Parameter covers : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t f, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In f (K.active s) -> SL.gamma_step (look f) s t.
  (** Each actual resolved call entry satisfies the callee's post-solution fact. *)
  Parameter covers_entry : forall p look, CL.wf p -> A.post_solution p look ->
    forall s t site, reachable (M.initial p) (M.step p) s -> M.step p s t ->
      In site (CL.sites_of p (K.here s)) -> In (K.here t) (CL.resolve p site) ->
      K.frames t = (K.here s, site) :: K.frames s -> SL.gamma_entry (look (K.here t)) t.
  (** Finished activity that keeps a callee active is covered at every transition. *)
  Parameter covers_finished : forall p look f s t, CL.wf p -> A.post_solution p look ->
    covered_run (M.step p)
      (fun u _ => reachable (M.initial p) (M.step p) u /\ In f (K.active u)) s t ->
    covered_run (M.step p) (SL.gamma_step (look f)) s t.
End SUMMARY_SOUND.
