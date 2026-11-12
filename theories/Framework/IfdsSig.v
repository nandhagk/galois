(** * Balanced IFDS path-edge constraints

    Path edges retain an origin fact, a destination point and a destination fact.
    For example, a return combines a caller path edge with a balanced callee path edge.
    Builds on: Program.IcfgSig, Base.Code and Fixpoint.SystemSig. *)

From Stdlib Require Import List Bool NArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Code.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.

Definition path_edge (N F : Type) := (F * (N * F))%type.

(** Encoding preserves all three path-edge components. *)
Definition path_edge_code {N F} (node : N -> positive) (fact : F -> positive)
    (x : path_edge N F) : positive := pair_code fact (pair_code node fact) x.

TimeFun path_edge_code.

(** Fact propagation starts from the supplied origin fact and retains flow occurrence order. *)
Definition path_facts {E F} (flow : E -> F -> list F) (origin : F) (path : list E) : list F :=
  fold_left (fun facts e => flat_map (flow e) facts) path (origin :: nil).

TimeFun path_facts.

(** Valid paths start and finish at the same stack level with matching call sites.
    Prefixes ending inside a callee require a separate value-reachability theorem. *)
Inductive valid_path {N E Site} (edges : list E) (src dst : E -> N)
    (kind : E -> edge_kind Site) : N -> list E -> N -> Prop :=
  | Valid_here : forall n, valid_path edges src dst kind n nil n
  | Valid_internal : forall e, In e edges ->
      (kind e = Intra \/ exists site, kind e = CallToReturn site) ->
      valid_path edges src dst kind (src e) (e :: nil) (dst e)
  | Valid_append : forall n m t left right,
      valid_path edges src dst kind n left m ->
      valid_path edges src dst kind m right t ->
      valid_path edges src dst kind n (left ++ right) t
  | Valid_call : forall call ret site inside,
      In call edges -> In ret edges -> kind call = Call site -> kind ret = Return site ->
      valid_path edges src dst kind (dst call) inside (src ret) ->
      valid_path edges src dst kind (src call) (call :: inside ++ ret :: nil) (dst ret).

Inductive path_rule (N E F : Type) :=
  | PathIdentity (node : N) (fact : F)
  | PathStep (origin : F) (edge : E) (input output : F)
  | PathReturn (origin : F) (call ret : E) (caller_input callee_input callee_output output : F).

Arguments PathIdentity {N E F}.
Arguments PathStep {N E F}.
Arguments PathReturn {N E F}.

(** Binary row identities distinguish repeated edge and flow occurrences. *)
Record path_row (N E F : Type) := PathRow {
  path_row_code : positive;
  path_row_rule : path_rule N E F
}.

Arguments PathRow {N E F}.
Arguments path_row_code {N E F}.
Arguments path_row_rule {N E F}.

TimeFun path_row_code.
TimeFun path_row_rule.

Record path_frame (N E F A : Type) := PathFrame {
  path_frame_rule : path_rule N E F;
  path_frame_pending : list (path_edge N F);
  path_frame_received : list A
}.

Module Type FLOW_FUN_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (F : KEY_OPS).
  Parameter facts : P.t -> list F.t.
  Parameter flow : P.t -> E.t -> F.t -> list F.t.
  Parameter seeds : P.t -> list (N.t * F.t).
End FLOW_FUN_OPS.

Module Type FLOW_FUN_LAWS (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (F : KEY) (Import FL : FLOW_FUN_OPS P N E F).
  (** Seed points and facts belong to the finite presentation. *)
  Parameter seeds_listed : forall p n d, In (n, d) (seeds p) ->
    In n (C.nodes p) /\ In d (facts p).
  (** Listed edges map supported facts to supported facts. *)
  Parameter flow_closed : forall p e x y, In e (C.edges p) -> In x (facts p) ->
    In y (flow p e x) -> In y (facts p).
End FLOW_FUN_LAWS.

Module Type FLOW_FUN (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E) (F : KEY) :=
  FLOW_FUN_OPS P N E F <+ FLOW_FUN_LAWS P N E C F.

Module Type FLOW_FUN_TIME (P : TYPE) (N : KEY_T) (E : TYPE) (F : KEY_T)
    (Import FL : FLOW_FUN_OPS P N E F).
  Parameter T_facts T_seeds : P.t -> N.
  Parameter T_flow : P.t -> E.t -> F.t -> N.
End FLOW_FUN_TIME.

Module Type FLOW_FUN_T (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_T P N E)
    (F : KEY_T) := FLOW_FUN P N E C F <+ FLOW_FUN_TIME P N E F.

Module Type IFDS_LATTICE_OPS.
  Include LATTICE_OPS with Definition t := bool
    with Definition leb := fun a b => negb a || b
    with Definition bot := false with Definition is_bot := negb with Definition join := orb.
End IFDS_LATTICE_OPS.

Module Type IFDS_LATTICE := IFDS_LATTICE_OPS <+ LATTICE_LAWS.
Module Type IFDS_LATTICE_T := IFDS_LATTICE <+ LATTICE_TIME.

Module Type IFDS_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE) (F : KEY_OPS)
    (L : IFDS_LATTICE_OPS).
  Include LOCAL_SYSTEM_OPS L with Definition prog := P.t
    with Definition key := path_edge N.t F.t with Definition row := path_row N.t E.t F.t
    with Definition frame := path_frame N.t E.t F.t bool.
End IFDS_OPS.

Module Type IFDS_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (FL : FLOW_FUN_OPS P N E F) (L : IFDS_LATTICE_OPS) (A : IFDS_OPS P N E F L).
  Definition internal p e := I.kind p e = Intra \/
    exists site, I.kind p e = CallToReturn site.
  Definition identity p n d := In (n, d) (FL.seeds p) \/
    exists e site x, In e (C.edges p) /\ I.kind p e = Call site /\
      C.dst p e = n /\ In x (FL.facts p) /\ In d (FL.flow p e x).
  Definition enabled p (r : path_rule N.t E.t F.t) :=
    match r with
    | PathIdentity n d => identity p n d
    | PathStep d0 e x y => In d0 (FL.facts p) /\ In e (C.edges p) /\ internal p e /\
        In x (FL.facts p) /\ In y (FL.flow p e x)
    | PathReturn d0 call ret x a b y =>
        In d0 (FL.facts p) /\ In call (C.edges p) /\ In ret (C.edges p) /\
        (exists site, I.kind p call = Call site /\ I.kind p ret = Return site) /\
        In x (FL.facts p) /\ In a (FL.flow p call x) /\
        In b (FL.facts p) /\ In y (FL.flow p ret b)
    end.
End IFDS_SPEC.

Module Type IFDS_LAWS (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (Import A : IFDS_OPS P N E F L)
    (Import AS : SYSTEM_SPEC L A) (IS : IFDS_SPEC P N E C Site I F FL L A).
  (** The system encodes all three path-edge components. *)
  Parameter key_code_spec : key_code = path_edge_code N.encode F.encode.
  (** The row identifier is its assigned binary occurrence identity. *)
  Parameter row_code_spec : row_code = path_row_code.
  (** The row inventory contains exactly the enabled finite rules. *)
  Parameter rows_spec : forall p rule,
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> IS.enabled p rule.
  (** Rule targets follow their destination edge or identity point. *)
  Parameter target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  (** Boolean rules combine the caller and callee at a matched return. *)
  Parameter eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => true
     | PathStep d0 e x _ => look (d0, (C.src p e, x))
     | PathReturn d0 call ret x a b _ =>
         look (d0, (C.src p call, x)) && look (a, (C.src p ret, b))
     end, nil).
End IFDS_LAWS.

Module Type IFDS (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) := IFDS_OPS P N E F L <+ SYSTEM_SPEC L <+ SYSTEM_LAWS L <+
  LOCAL_LAWS L <+ IFDS_SPEC P N E C Site I F FL L <+
  IFDS_LAWS P N E C Site I F FL L.

Module Type IFDS_TIME (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T) (FL : FLOW_FUN_T P N E C F)
    (L : IFDS_LATTICE_T) (Import A : IFDS P N E C Site I F FL L).
  Include SYSTEM_TIME L A.
  Include LOCAL_TIME L A.
  (* SIG-QUESTION: reader budgets and a prepared rule index must supply the linear
     enumeration and rows_of contracts; arbitrary FLOW_FUN clocks have no such bound. *)
End IFDS_TIME.

Module Type IFDS_T (P : TYPE) (N : KEY_T) (E : TYPE) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T) (FL : FLOW_FUN_T P N E C F)
    (L : IFDS_LATTICE_T) := IFDS P N E C Site I F FL L <+
  IFDS_TIME P N E C Site I F FL L.

Module Type IFDS_SOUND (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (A : IFDS P N E C Site I F FL L).
  (** Seeded facts on balanced paths hold in every Boolean post-solution. *)
  Parameter covers : forall p look, A.post_solution p look ->
    forall entry d0 n path d, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In d (path_facts (FL.flow p) d0 path) -> look (d0, (n, d)) = true.
End IFDS_SOUND.
