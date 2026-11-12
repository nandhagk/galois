(** * IDE micro-function path edges

    Rules compose symbolic functions along balanced paths.
    For example, a return combines the caller, call, callee and return functions.
    Builds on: Framework.IdeSig and Framework.Ifds. *)

From Stdlib Require Import List Bool NArith PArith.
From Argent Require Import Time Std Loop.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig Ifds IdeSig.

Module IdeCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (V : LATTICE_OPS) (M : MICRO_OPS V) (FL : IDE_FLOW_OPS P N E F V M)
    <: IDE_OPS P N E F V M.
  Definition prog := P.t.
  Definition key := path_edge N.t F.t.
  Definition row := path_row N.t E.t F.t.
  Definition frame := path_frame N.t E.t F.t M.t.
  Definition key_code := path_edge_code N.encode F.encode.
  Definition key_eqb (x y : key) :=
    F.eqb (fst x) (fst y) && N.eqb (fst (snd x)) (fst (snd y)) &&
      F.eqb (snd (snd x)) (snd (snd y)).
  Definition rows p : list row := path_number 1%positive
    (path_rules Site.eqb (I.kind p) (C.dst p) (FL.facts p) (FL.flow p)
      (FL.seeds p) (C.edges p)).
  Definition row_code (r : row) := path_row_code r.
  Definition target p (r : row) : key := match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Definition deps p (r : row) : list key := match path_row_rule r with
    | PathIdentity _ _ => nil
    | PathStep d0 e x _ => (d0, (C.src p e, x)) :: nil
    | PathReturn d0 call ret x a b _ =>
        (d0, (C.src p call, x)) :: (a, (C.src p ret, b)) :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
  Definition finish p (r : path_rule N.t E.t F.t) (xs : list M.t) : M.t :=
    match r, xs with
    | PathIdentity _ _, _ => M.identity
    | PathStep _ e x y, a :: _ => M.compose (FL.weight p e x y) a
    | PathReturn _ call ret x a b y, caller :: callee :: _ =>
        M.compose (FL.weight p ret b y)
          (M.compose callee (M.compose (FL.weight p call x a) caller))
    | _, _ => M.bot
    end.
  Definition start p (r : row) : query key M.t frame :=
    path_query (finish p) (path_row_rule r) (deps p r) nil.
  Definition resume p (f : frame) (a : M.t) : query key M.t frame :=
    match f with
    | PathFrame _ _ _ _ rule pending received => path_query (finish p) rule pending (a :: received)
    end.
  Definition rows_of p (x : key) : list row :=
    filter (fun r => key_eqb x (target p r)) (rows p).
End IdeCode.

Module Ide (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) <: IDE P N E C Site I F V M FL.
  Include IdeCode P N E C Site I F V M FL.
  Include SYSTEM_SPEC M.
  Definition wf (_ : prog) := True.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof. Admitted.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof. Admitted.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof. Admitted.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof. Admitted.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof. Admitted.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof. Admitted.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof. Admitted.
  (** Row codes distinguish rows within each program. *)
  Lemma row_code_inj : forall p a b, wf p -> In a (rows p) -> In b (rows p) ->
    row_code a = row_code b -> a = b.
  Proof. Admitted.
  (** The index lists exactly the rows that may write the requested key. *)
  Lemma rows_of_spec : forall p x r, wf p ->
    (In r (rows_of p x) <-> In r (rows p) /\ In x (writes p r)).
  Proof. Admitted.
  Include IDE_RULE_SPEC P N E C Site I F V M FL.
  (** The path-edge encoding retains all three components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof. Admitted.
  (** Row codes retain binary occurrence identities. *)
  Lemma row_code_spec : row_code = path_row_code.
  Proof. Admitted.
  (** Rows contain exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule,
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof. Admitted.
  (** Every rule writes its destination path edge. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof. Admitted.
  (** Matched returns compose caller, call, callee and return effects in that order. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => M.identity
     | PathStep d0 e x y => M.compose (FL.weight p e x y) (look (d0, (C.src p e, x)))
     | PathReturn d0 call ret x a b y => M.compose (FL.weight p ret b y)
         (M.compose (look (a, (C.src p ret, b)))
           (M.compose (FL.weight p call x a) (look (d0, (C.src p call, x)))))
     end, nil).
  Proof. Admitted.
End Ide.

Module IdeT (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T)
    (V : LATTICE_T) (M : MICRO_T V) (FL : IDE_FLOW_T P N E C F V M).
  Include Ide P N E C Site I F V M FL.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun row_code.
  TimeFun target.
  TimeFun deps.
  TimeFun sides.
  TimeFun finish.
  TimeFun start.
  TimeFun resume.
  TimeFun rows_of.
End IdeT.

Module IdeSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) (A : IDE P N E C Site I F V M FL)
    <: IDE_SOUND P N E C Site I F V M FL A.
  Lemma covers : forall p look, A.post_solution p look ->
    forall entry d0 n path d f, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In (d, f) (weighted_facts (FL.flow p) (FL.weight p) M.identity M.compose d0 path) ->
      forall a, V.leb (M.apply f a) (M.apply (look (d0, (n, d))) a) = true.
  Proof. Admitted. (* CONVERT: balanced_path_sound: The reference TabPaths.trace_complete was not found *)
End IdeSound.
