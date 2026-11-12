(** * Dense dataflow systems

    Dense frameworks attach boundary values to entries and transfers to edges.
    For example, a forward flow row reads its edge source and writes its destination.
    Builds on: Program.CfgSig, Program.SemanticsSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List Relation_Operators NArith.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.

Inductive direction :=
  | Forward
  | Backward.

Inductive dense_row (N E : Type) :=
  | Seed (n : N)
  | Flow (e : E).

Arguments Seed {N E} n.
Arguments Flow {N E} e.

Module Type FLOW_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (L : LATTICE_OPS).
  Parameter dir : direction.
  Parameter boundary : P.t -> N.t -> L.t.
  Parameter transfer : P.t -> E.t -> L.t -> L.t.
End FLOW_OPS.

Module Type FLOW_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter gamma : L.t -> M.state -> Prop.
  (** Abstract inclusion entails concrete inclusion at the same state. *)
  Parameter gamma_mono : forall a b s, L.leb a b = true -> gamma a s -> gamma b s.
  (** Initial states are described by the boundary at an entry. *)
  Parameter init_sound : forall p s, M.initial p s ->
    In (point s) (C.entries p) /\ gamma (T.boundary p (point s)) s.
  (** Every reachable step follows a sound transfer between its actual endpoints. *)
  Parameter step_sound : forall p s t a,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> gamma a s ->
    exists e, In e (C.edges p) /\ C.src p e = point s /\ C.dst p e = point t /\
      gamma (T.transfer p e a) t.
End FLOW_LINK.

Module Type BACKWARD_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter gamma : L.t -> M.state -> Prop.
  Parameter terminal : P.t -> M.state -> Prop.
  (** Abstract inclusion entails concrete inclusion at the same state. *)
  Parameter gamma_mono : forall a b s, L.leb a b = true -> gamma a s -> gamma b s.
  (** Terminal states are covered by the boundary at a listed boundary node. *)
  Parameter terminal_sound : forall p s, terminal p s ->
    In (point s) (C.entries p) /\ gamma (T.boundary p (point s)) s.
  (** Backward transfer transports the target predicate to the source state. *)
  Parameter step_sound : forall p s t a, M.step p s t -> gamma a t ->
    exists e, In e (C.edges p) /\ C.src p e = point s /\ C.dst p e = point t /\
      gamma (T.transfer p e a) s.
End BACKWARD_LINK.

Module Type DENSE_SYSTEM (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L).
  Include SYSTEM_OPS L
    with Definition prog := P.t
    with Definition key := N.t
    with Definition row := dense_row N.t E.t
    with Definition frame := E.t.
  Include SYSTEM_SPEC L.
  (** Dense rows consist of boundary seeds followed by flow edges. *)
  Parameter rows_spec : forall p,
    rows p = List.map Seed (C.entries p) ++ List.map Flow (C.edges p).
  (** Seed rows target their boundary node. *)
  Parameter target_seed : forall p n, target p (Seed n) = n.
  (** Flow targets follow the selected direction. *)
  Parameter target_flow : forall p e, target p (Flow e) =
    match T.dir with Forward => C.dst p e | Backward => C.src p e end.
  (** Seed evaluation returns the boundary without side contributions. *)
  Parameter eval_seed : forall p n look,
    eval p (Seed n) look = Some (T.boundary p n, nil).
  (** Flow evaluation reads the directional predecessor and applies the transfer. *)
  Parameter eval_flow : forall p e look,
    eval p (Flow e) look = Some
      (T.transfer p e (look
        (match T.dir with Forward => C.src p e | Backward => C.dst p e end)), nil).
End DENSE_SYSTEM.

Module Type DENSE_SOUND (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    (S : DENSE_SYSTEM P N E C L T) (M : SEMANTICS P)
    (K : FLOW_LINK P N E C L T M).
  (** Forward post-solutions cover all reachable concrete states. *)
  Parameter covers : forall p look, T.dir = Forward -> S.post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> K.gamma (look (K.point s)) s.
End DENSE_SOUND.

Module Type DENSE_BACKWARD_SOUND (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE_OPS) (T : FLOW_OPS P N E L)
    (S : DENSE_SYSTEM P N E C L T) (M : SEMANTICS P)
    (K : BACKWARD_LINK P N E C L T M).
  (** Backward post-solutions cover every finite suffix ending at a terminal state. *)
  Parameter covers_backward : forall p look, T.dir = Backward -> S.post_solution p look ->
    forall s t, clos_refl_trans M.state (M.step p) s t -> K.terminal p t ->
      K.gamma (look (K.point s)) s.
End DENSE_BACKWARD_SOUND.

Module Type FLOW_TIME (P : TYPE) (N : KEY_T) (E : TYPE) (L : LATTICE_T)
    (Import T : FLOW_OPS P N E L).
  (* spec: flow_work *)
  Parameter flow_work : P.t -> nat -> N.
  Parameter T_boundary : P.t -> N.t -> N.
  Parameter T_transfer : P.t -> E.t -> L.t -> N.
  Parameter c_flow : N.
  (** Transfer budgets grow with the size of their input. *)
  Parameter flow_work_mono : forall p s s', s <= s' ->
    (flow_work p s <= flow_work p s')%N.
  (** Reading the boundary fits its transfer budget. *)
  Parameter T_boundary_le : forall p n,
    (T_boundary p n <= c_flow * (flow_work p 0 + 1))%N.
  (** Transfers fit their size-dependent budget. *)
  Parameter T_transfer_le : forall p e a,
    (T_transfer p e a <= c_flow * (flow_work p (L.size a) + 1))%N.
  (** Boundary values fit the zero-input transfer budget. *)
  Parameter boundary_size_le : forall p n,
    (N.of_nat (L.size (boundary p n)) <= flow_work p 0)%N.
  (** Transfer outputs fit their input-size budget. *)
  Parameter transfer_size_le : forall p e a,
    (N.of_nat (L.size (transfer p e a)) <= flow_work p (L.size a))%N.
End FLOW_TIME.

Module Type FLOW_T (P : TYPE) (N : KEY_T) (E : TYPE) (L : LATTICE_T) :=
  FLOW_OPS P N E L <+ FLOW_TIME P N E L.

Module Type DENSE (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG_OPS P N E) (L : LATTICE) (T : FLOW_OPS P N E L) :=
  DENSE_SYSTEM P N E C L T <+ SYSTEM_LAWS L.

Module Type DENSE_TIME (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (L : LATTICE_T) (T : FLOW_T P N E L)
    (Import S : DENSE P N E C L T).
  Include SYSTEM_TIME L S
    with Definition row_work := T.flow_work
    with Definition kw := fun p => fold_right Nat.max 0
      (List.map N.bits (C.entries p ++
        flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))).
End DENSE_TIME.

Module Type DENSE_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (L : LATTICE_T) (T : FLOW_T P N E L) :=
  DENSE P N E C L T <+ DENSE_TIME P N E C L T.
