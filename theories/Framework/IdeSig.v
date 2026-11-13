(** * IDE micro-function path edges

    IDE constraints compose symbolic edge functions along balanced fact paths.
    For example, a matched return applies the caller, call, callee and return functions in order.
    Builds on: Framework.IfdsSig and Fixpoint.SystemSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig.

(** Each output retains its fact and the composed micro-function for that fact path. *)
Definition weighted_facts {E F A} (flow : E -> F -> list F)
    (weight : E -> F -> F -> A) (identity : A) (compose : A -> A -> A)
    (origin : F) (path : list E) : list (F * A) :=
  fold_left (fun current e => flat_map (fun xf =>
    map (fun y => (y, compose (weight e (fst xf) y) (snd xf))) (flow e (fst xf))) current)
    path ((origin, identity) :: nil).

TimeFun weighted_facts.

Module Type MICRO_OPS (V : LATTICE_OPS).
  Include LATTICE_OPS.
  Parameter identity : t.
  Parameter compose : t -> t -> t.
  Parameter apply : t -> V.t -> V.t.
End MICRO_OPS.

Module Type MICRO_LAWS (V : LATTICE) (Import M : MICRO_OPS V).
  (** Symbolic inclusion implies pointwise inclusion of results. *)
  Parameter apply_mono : forall f g a, leb f g = true ->
    V.leb (apply f a) (apply g a) = true.
  (** Micro-functions preserve inclusion of their input values. *)
  Parameter value_mono : forall f a b, V.leb a b = true ->
    V.leb (apply f a) (apply f b) = true.
  (** The symbolic identity acts as the identity on values. *)
  Parameter apply_identity : forall a, apply identity a = a.
  (** Composition applies its right operand before its left operand. *)
  Parameter apply_compose : forall f g a, apply (compose f g) a = apply f (apply g a).
  (** Joining symbolic paths joins their pointwise results. *)
  Parameter apply_join : forall f g a, apply (join f g) a = V.join (apply f a) (apply g a).
  (** Composition preserves inclusion in both operands. *)
  Parameter compose_mono : forall f f' g g', leb f f' = true -> leb g g' = true ->
    leb (compose f g) (compose f' g') = true.
End MICRO_LAWS.

Module Type MICRO (V : LATTICE) := MICRO_OPS V <+ LATTICE_LAWS <+ MICRO_LAWS V.

Module Type MICRO_TIME (V : LATTICE_T) (Import M : MICRO V).
  Include LATTICE_TIME M.
  Parameter T_compose : t -> t -> N.
  Parameter T_apply : t -> V.t -> N.
  (* spec: compose_work apply_work *)
  Parameter compose_work : t -> t -> N.
  Parameter apply_work : t -> V.t -> N.
  Parameter c_micro : N.
  (** Composition work is linear in the operand sizes. *)
  Parameter compose_work_le : forall f g,
    (compose_work f g <= c_micro * N.of_nat (size f + size g + 1))%N.
  (** Composed functions have size linear in the operand sizes. *)
  Parameter compose_size : forall f g,
    (N.of_nat (size (compose f g)) <= c_micro * N.of_nat (size f + size g + 1))%N.
  (** The identity has bounded size. *)
  Parameter identity_size : (N.of_nat (size identity) <= c_micro)%N.
  (** Symbolic composition charges its supplied work oracle. *)
  Parameter T_compose_le : forall f g, (T_compose f g <= c_micro * (compose_work f g + 1))%N.
  (** Applying a symbolic function charges its supplied work oracle. *)
  Parameter T_apply_le : forall f a, (T_apply f a <= c_micro * (apply_work f a + 1))%N.
End MICRO_TIME.

Module Type MICRO_T (V : LATTICE_T) := MICRO V <+ MICRO_TIME V.

Module Type IDE_FLOW_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (F : KEY_OPS)
    (V : LATTICE_OPS) (M : MICRO_OPS V).
  Include FLOW_FUN_OPS P N E F.
  Parameter weight : P.t -> E.t -> F.t -> F.t -> M.t.
End IDE_FLOW_OPS.

Module Type IDE_FLOW (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E) (F : KEY)
    (V : LATTICE) (M : MICRO V) :=
  IDE_FLOW_OPS P N E F V M <+ FLOW_FUN_LAWS P N E C F.

Module Type IDE_FLOW_TIME (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (F : KEY_T) (V : LATTICE_T) (M : MICRO_T V)
    (Import FL : IDE_FLOW P N E C F V M).
  Include FLOW_FUN_TIME P N E F FL.
  Parameter T_weight : P.t -> E.t -> F.t -> F.t -> N.
  (* spec: weight_work *)
  Parameter weight_work : P.t -> nat.
  (** Listed edge weights fit the program budget in time. *)
  Parameter T_weight_le : forall p e x y, In e (C.edges p) -> In x (facts p) ->
    In y (flow p e x) -> (T_weight p e x y <= M.c_micro * N.of_nat (weight_work p + 1))%N.
  (** Listed edge weights fit the program budget in size. *)
  Parameter weight_size : forall p e x y, In e (C.edges p) -> In x (facts p) ->
    In y (flow p e x) -> M.size (weight p e x y) <= weight_work p.
End IDE_FLOW_TIME.

Module Type IDE_FLOW_T (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (F : KEY_T) (V : LATTICE_T) (M : MICRO_T V) :=
  IDE_FLOW P N E C F V M <+ IDE_FLOW_TIME P N E C F V M.

Module Type IDE_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (F : KEY_OPS)
    (V : LATTICE_OPS) (M : MICRO_OPS V).
  Include SYSTEM_OPS M with Definition prog := P.t
    with Definition key := path_edge N.t F.t with Definition row := path_row N.t E.t F.t
    with Definition frame := path_frame N.t E.t F.t M.t.
End IDE_OPS.

Module Type IDE_RULE_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (V : LATTICE_OPS) (M : MICRO_OPS V) (FL : IDE_FLOW_OPS P N E F V M).
  Definition identity_root p n d := In (n, d) (FL.seeds p) \/
    exists e site x, In e (C.edges p) /\ I.kind p e = Call site /\
      C.dst p e = n /\ In x (FL.facts p) /\ In d (FL.flow p e x).
  Definition enabled p :=
    path_enabled (C.edges p) (C.dst p) (I.kind p) (FL.facts p) (FL.flow p) (FL.seeds p).
End IDE_RULE_SPEC.

Module Type IDE_LAWS (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) (Import A : IDE_OPS P N E F V M)
    (Import AS : SYSTEM_SPEC M A) (W : SYSTEM_LAWS M A AS)
    (IS : IDE_RULE_SPEC P N E C Site I F V M FL).
  (** The path-edge encoding retains all three components. *)
  Parameter key_code_spec : key_code = path_edge_code N.encode F.encode.
  (** Rows contain exactly the enabled finite rules. *)
  Parameter rows_spec : forall p rule, W.wf p ->
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> IS.enabled p rule.
  (** Every rule writes its destination path edge. *)
  Parameter target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  (** Matched returns compose caller, call, callee and return effects in that order. *)
  Parameter eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => M.identity
     | PathStep d0 e x y => M.compose (FL.weight p e x y) (look (d0, (C.src p e, x)))
     | PathReturn d0 call ret x a b y => M.compose (FL.weight p ret b y)
         (M.compose (look (a, (C.src p ret, b)))
           (M.compose (FL.weight p call x a) (look (d0, (C.src p call, x)))))
     end, nil).
End IDE_LAWS.

Module Type IDE (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) :=
  IDE_OPS P N E F V M <+ SYSTEM_SPEC M <+ SYSTEM_LAWS M <+
  IDE_RULE_SPEC P N E C Site I F V M FL <+ IDE_LAWS P N E C Site I F V M FL.

Module Type IDE_TIME (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T) (V : LATTICE_T) (M : MICRO_T V)
    (FL : IDE_FLOW_T P N E C F V M) (Import A : IDE P N E C Site I F V M FL).
  (** The widest key that a listed row writes or reads. *)
  Definition path_kw (p : prog) : nat := fold_right Nat.max 0
    (flat_map (fun r => map key_bits (writes p r ++ deps p r)) (rows p)).
  Include SYSTEM_TIME M A
    with Definition row_work := fun p s =>
      (3 * (M.c_micro + 1) ^ 3 * N.of_nat (FL.weight_work p + s + 1) +
        N.of_nat (length (rows p) + M.size M.identity + M.size M.bot))%N
    with Definition kw := path_kw.
End IDE_TIME.

Module Type IDE_T (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T) (V : LATTICE_T) (M : MICRO_T V)
    (FL : IDE_FLOW_T P N E C F V M) :=
  IDE P N E C Site I F V M FL <+ IDE_TIME P N E C Site I F V M FL.

Module Type IDE_SOUND (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (V : LATTICE) (M : MICRO V)
    (FL : IDE_FLOW P N E C F V M) (A : IDE P N E C Site I F V M FL).
  (** Every weighted balanced fact path is bounded pointwise by the symbolic post-solution. *)
  Parameter covers : forall p look, A.wf p -> A.post_solution p look ->
    forall entry d0 n path d f, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In (d, f) (weighted_facts (FL.flow p) (FL.weight p) M.identity M.compose d0 path) ->
      forall a, V.leb (M.apply f a) (M.apply (look (d0, (n, d))) a) = true.
End IDE_SOUND.
