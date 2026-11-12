(** * Sparse value constraints

    Sparse rows seed entry bindings, evaluate definitions and copy incoming operands.
    For example, a parameter receives each operand on an incoming edge.
    Builds on: Program.SsaSig, Domains.ValueSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import CfgSig SemanticsSig SsaSig.

Inductive sparse_row (E X : Type) :=
  | SparseSeed (value : X)
  | SparseDef (value : X)
  | SparseArg (edge : E) (parameter operand : X).

Arguments SparseSeed {E X}.
Arguments SparseDef {E X}.
Arguments SparseArg {E X}.

Inductive sparse_frame (X K A : Type) :=
  | SparseRead (operator : K) (pending : list X) (received : list A)
  | SparseCopy.

Module Type SSA_TRANSFER_OPS (P : TYPE) (X : KEY_OPS) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L).
  Parameter seed : P.t -> X.t -> V.t.
End SSA_TRANSFER_OPS.

Module Type SSA_TRANSFER_TIME (P : TYPE) (X : KEY_T) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (Import T : SSA_TRANSFER_OPS P X L V).
  (* spec: seed_work *)
  Parameter seed_work : P.t -> nat.
  Parameter T_seed : P.t -> X.t -> N.
  Parameter c_seed : N.
  (** Seed lookup pays for the value key and the program seed budget. *)
  Parameter T_seed_le : forall p x,
    (T_seed p x <= c_seed * N.of_nat (X.bits x + seed_work p + 1))%N.
  (** Seed facts fit the program seed budget. *)
  Parameter seed_size : forall p x, V.size (seed p x) <= seed_work p.
End SSA_TRANSFER_TIME.

Module Type SSA_TRANSFER_T (P : TYPE) (X : KEY_T) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) :=
  SSA_TRANSFER_OPS P X L V <+ SSA_TRANSFER_TIME P X L V.

Module Type SPARSE_OPS (P : TYPE) (E : TYPE) (X : KEY_OPS) (L : LANG_OPS)
    (V : VALUE_DOMAIN_OPS L).
  Include SYSTEM_OPS V
    with Definition prog := P.t
    with Definition key := X.t
    with Definition row := sparse_row E.t X.t
    with Definition frame := sparse_frame X.t L.op V.t.
End SPARSE_OPS.

Module Type SPARSE_LAWS (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    (Import A : SPARSE_OPS P E X L V) (Import AS : SYSTEM_SPEC V A).
  (** Value keys retain the supplied key encoding. *)
  Parameter key_code_spec : key_code = X.encode.
  (** Value equality retains the supplied key test. *)
  Parameter key_eqb_specification : key_eqb = X.eqb.
  (** Rows retain entry, definition and incoming-operand occurrence order. *)
  Parameter rows_spec : forall p, rows p =
    map SparseSeed (flat_map (S.params p) (C.entries p)) ++
    map SparseDef (S.values p) ++
    flat_map (fun e => map (fun xy => SparseArg e (fst xy) (snd xy)) (S.args p e))
      (C.edges p).
  (** Seed rows target their value. *)
  Parameter target_seed : forall p x, target p (SparseSeed x) = x.
  (** Definition rows target their defined value. *)
  Parameter target_def : forall p x, target p (SparseDef x) = x.
  (** Incoming-operand rows target the destination parameter. *)
  Parameter target_arg : forall p e x y, target p (SparseArg e x y) = x.
  (** Seeds have no dependencies and return their client's entry fact. *)
  Parameter eval_seed : forall p x look, eval p (SparseSeed x) look = Some (T.seed p x, nil).
  (** Definitions apply the domain transfer or supply top for arbitrary bindings. *)
  Parameter eval_def : forall p x look, eval p (SparseDef x) look = Some
    (match S.def p x with
     | Op op xs => V.forward op (map look xs)
     | Param _ _ => V.bot
     | Arbitrary => V.top
     end, nil).
  (** Incoming operands contribute their value to the destination parameter. *)
  Parameter eval_arg : forall p e x y look,
    eval p (SparseArg e x y) look = Some (look y, nil).
End SPARSE_LAWS.

Module Type SPARSE (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V) :=
  SPARSE_OPS P E X L V <+ SYSTEM_SPEC V <+ SYSTEM_LAWS V <+
  SPARSE_LAWS P N E C X L K G S V T.

Module Type SPARSE_ENVELOPE (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (X : KEY_T) (L : LANG_T) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA_T P N E C X K G) (V : VALUE_DOMAIN_T L).
  (* spec: op_work op_arity *)
  Parameter op_work : P.t -> nat -> nat.
  Parameter op_arity : P.t -> nat.
  (** Operator envelopes grow with the operand size. *)
  Parameter op_work_mono : forall p s t, s <= t -> op_work p s <= op_work p t.
  (** Every listed operation has at most the program's operand count. *)
  Parameter op_arity_le : forall p x op xs, In x (S.values p) ->
    S.def p x = Op op xs -> length xs <= op_arity p.
  (** Every listed operation fits the envelope on operands of bounded size. *)
  Parameter op_work_le : forall p x op xs vs s, In x (S.values p) ->
    S.def p x = Op op xs -> length vs = length xs ->
    Forall (fun v => V.size v <= s) vs -> V.work op vs <= op_work p s.
End SPARSE_ENVELOPE.

Module Type SPARSE_TIME (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (X : KEY_T) (L : LANG_T) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA_T P N E C X K G)
    (V : VALUE_DOMAIN_T L) (T : SSA_TRANSFER_T P X L V)
    (B : SPARSE_ENVELOPE P N E C X L K G S V)
    (Import A : SPARSE P N E C X L K G S V T).
  Include SYSTEM_TIME V A with Definition row_work := fun p s =>
    N.of_nat (B.op_work p s + (B.op_arity p + 1) * (s + 1) + T.seed_work p +
      V.size V.top + V.size V.bot + 1).
End SPARSE_TIME.

Module Type SPARSE_T (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (X : KEY_T) (L : LANG_T) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (S : SSA_T P N E C X K G)
    (V : VALUE_DOMAIN_T L) (T : SSA_TRANSFER_T P X L V)
    (B : SPARSE_ENVELOPE P N E C X L K G S V) :=
  SPARSE P N E C X L K G S V T <+ SPARSE_TIME P N E C X L K G S V T B.

Module Type SPARSE_INITIAL_LINK (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (Val : TYPE with Definition t := L.val)
    (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    (M : SEMANTICS P) (CL : CFG_LINK P N E C M)
    (SL : SSA_LINK P N E C X K G Val S M CL).
  (** Concrete operation evaluation agrees with the domain's language. *)
  Parameter eval_agrees : SL.eval = L.eval.
  (** Initial bindings come from entry seeds, operations or arbitrary definitions. *)
  Parameter initial_binding : forall p s x c, M.initial p s -> SL.venv s x = Some c ->
    (exists b, In b (C.entries p) /\ In x (S.params p b) /\ V.gamma (T.seed p x) c) \/
    (exists op xs cs, S.def p x = Op op xs /\
      Forall2 (fun y d => SL.venv s y = Some d) xs cs /\ SL.eval op cs = Some c) \/
    S.def p x = Arbitrary.
  (** Edges selected by value origins belong to the executable edge inventory. *)
  Parameter taken_listed : forall p s t e,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> CL.taken p s t e ->
    In e (C.edges p).
End SPARSE_INITIAL_LINK.

Module Type SPARSE_SOUND (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (X : KEY) (L : LANG) (K : TYPE with Definition t := L.op)
    (G : TYPE with Definition t := L.guard)
    (Val : TYPE with Definition t := L.val)
    (S : SSA P N E C X K G)
    (V : VALUE_DOMAIN L) (T : SSA_TRANSFER_OPS P X L V)
    (A : SPARSE P N E C X L K G S V T)
    (M : SEMANTICS P) (CL : CFG_LINK P N E C M)
    (SL : SSA_LINK P N E C X K G Val S M CL)
    (IL : SPARSE_INITIAL_LINK P N E C X L K G Val S V T M CL SL).
  (** Sparse post-solutions describe every defined binding in each reachable state. *)
  Parameter covers : forall p look, A.post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s ->
      forall x c, SL.venv s x = Some c -> V.gamma (look x) c.
End SPARSE_SOUND.
