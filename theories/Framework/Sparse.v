(** * Sparse SSA analyses

    Sparse rows collect operand values before applying an abstract operation.
    For example, an incoming operand is copied to its destination parameter.
    Builds on: Framework.SparseSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool Arith.
From Argent Require Import Time Std Loop.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig SsaSig SemanticsSig.
From Galois.Framework Require Import SparseSig.

Module List.
  TimeFun Stdlib.Lists.List.flat_map.
End List.

Definition sparse_read {X K A} (forward : K -> list A -> A)
    (op : K) (pending : list X) (received : list A)
    : query X A (sparse_frame X K A) :=
  match pending with
  | nil => Ret (forward op (rev_append received nil))
  | x :: xs => Ask x (SparseRead X K A op xs received)
  end.

TimeFun sparse_read.

Module SparseCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (L : LANG_OPS)
    (K : TYPE with Definition t := L.op) (G : TYPE with Definition t := L.guard)
    (S : SSA_OPS P N E C X K G) (V : VALUE_DOMAIN_OPS L)
    (T : SSA_TRANSFER_OPS P X L V) <: SPARSE_OPS P E X L V.
  Definition prog := P.t.
  Definition key := X.t.
  Definition row := sparse_row E.t X.t.
  Definition frame := sparse_frame X.t L.op V.t.
  Definition key_code := X.encode.
  Definition key_eqb := X.eqb.
  Definition rows p : list row :=
    map SparseSeed (S.entry_params p) ++
    map SparseDef (S.values p) ++
    map (fun r => SparseArg (fst r) (fst (snd r)) (snd (snd r))) (S.arg_rows p).
  Definition target (_ : prog) (r : row) : key :=
    match r with
    | SparseSeed x => x
    | SparseDef x => x
    | SparseArg _ x _ => x
    end.
  Definition start p (r : row) : query key V.t frame :=
    match r with
    | SparseSeed x => Ret (T.seed p x)
    | SparseDef x => match S.def p x with
      | Op op xs => sparse_read V.forward op xs nil
      | Param _ _ => Ret V.bot
      | Arbitrary => Ret V.top
      end
    | SparseArg _ _ y => Ask y (SparseCopy X.t L.op V.t)
    end.
  Definition resume (_ : prog) (f : frame) (a : V.t) : query key V.t frame :=
    match f with
    | SparseRead _ _ _ op xs acc => sparse_read V.forward op xs (a :: acc)
    | SparseCopy _ _ _ => Ret a
    end.
  Definition deps p (r : row) : list key :=
    match r with
    | SparseSeed _ => nil
    | SparseDef x => match S.def p x with Op _ xs => xs | _ => nil end
    | SparseArg _ _ y => y :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
End SparseCode.

Module Sparse (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard) (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    <: SPARSE P N E C X L K G S V T.
  Include SparseCode P N E C X L K G S V T.
  Include SYSTEM_SPEC V.
  Definition wf (_ : prog) := True.
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
  (** Value keys retain the supplied key encoding. *)
  Lemma key_code_spec : key_code = X.encode.
  Proof. Admitted. (* STUB *)
  (** Value equality retains the supplied key test. *)
  Lemma key_eqb_specification : key_eqb = X.eqb.
  Proof. Admitted. (* STUB *)
  (** Rows retain entry, definition and incoming-operand occurrence order. *)
  Lemma rows_spec : forall p, rows p =
    map SparseSeed (flat_map (S.params p) (C.entries p)) ++
    map SparseDef (S.values p) ++
    flat_map (fun e => map (fun xy => SparseArg e (fst xy) (snd xy)) (S.args p e))
      (C.edges p).
  Proof. Admitted. (* STUB *)
  (** Seed rows target their value. *)
  Lemma target_seed : forall p x, target p (SparseSeed x) = x.
  Proof. Admitted. (* STUB *)
  (** Definition rows target their defined value. *)
  Lemma target_def : forall p x, target p (SparseDef x) = x.
  Proof. Admitted. (* STUB *)
  (** Incoming-operand rows target the destination parameter. *)
  Lemma target_arg : forall p e x y, target p (SparseArg e x y) = x.
  Proof. Admitted. (* STUB *)
  (** Seeds have no dependencies and return their client's entry fact. *)
  Lemma eval_seed : forall p x look, eval p (SparseSeed x) look = Some (T.seed p x, nil).
  Proof. Admitted. (* STUB *)
  (** Definitions apply the domain transfer or supply top for arbitrary bindings. *)
  Lemma eval_def : forall p x look, eval p (SparseDef x) look = Some
    (match S.def p x with
     | Op op xs => V.forward op (map look xs)
     | Param _ _ => V.bot
     | Arbitrary => V.top
     end, nil).
  Proof. Admitted. (* STUB *)
  (** Incoming operands contribute their value to the destination parameter. *)
  Lemma eval_arg : forall p e x y look,
    eval p (SparseArg e x y) look = Some (look y, nil).
  Proof. Admitted. (* STUB *)
End Sparse.

Module SparseT (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (X : KEY_T) (L : LANG_T) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA_T P N E C X K G) (V : VALUE_DOMAIN_T L)
    (T : SSA_TRANSFER_T P X L V).
  Include Sparse P N E C X L K G S V T.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
End SparseT.

Module SparseSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard) (Val : TYPE with Definition t := L.val)
    (S : SSA P N E C X K G) (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    (A : SPARSE P N E C X L K G S V T) (M : SEMANTICS P)
    (CL : CFG_LINK P N E C M) (SL : SSA_LINK P N E C X K G Val S M CL)
    (IL : SPARSE_INITIAL_LINK P N E C X L K G Val S V T M CL SL)
    <: SPARSE_SOUND P N E C X L K G Val S V T A M CL SL IL.
  Lemma covers : forall p look, A.post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s ->
      forall x c, SL.venv s x = Some c -> V.gamma (look x) c.
  Proof. Admitted. (* CONVERT: sparse_sound: The variable sparse_reachable_invariant was not found *)
End SparseSound.
