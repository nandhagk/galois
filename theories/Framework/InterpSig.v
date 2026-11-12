(** * Ordered environment actions

    Action presentations connect concrete stores to abstract state transfers.
    For example, a guard after an assignment observes the assigned value.
    Builds on: Domains.LangSig, Domains.ValueSig, States.StateSig and Framework.DenseSig. *)

From Stdlib Require Import List NArith.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import SemanticsSig CfgSig.
From Galois.Framework Require Import DenseSig.

Inductive action (K G X : Type) :=
  | Assign (x : X) (e : term K X)
  | Havoc (x : X)
  | Assume (g : G) (es : list (term K X)).

Arguments Assign {K G X} x e.
Arguments Havoc {K G X} x.
Arguments Assume {K G X} g es.

Inductive exec {K G X V : Type} (ev : K -> list V -> option V)
    (holds : G -> list V -> Prop) (eqb : X -> X -> bool)
    : (X -> V) -> action K G X -> (X -> V) -> Prop :=
  | Exec_assign : forall st x e v, eval_term ev st e = Some v ->
      exec ev holds eqb st (Assign x e) (upd eqb st x v)
  | Exec_havoc : forall st x v,
      exec ev holds eqb st (Havoc x) (upd eqb st x v)
  | Exec_assume : forall st g es vs, eval_terms ev st es = Some vs -> holds g vs ->
      exec ev holds eqb st (Assume g es) st.

Inductive exec_all {K G X V : Type} (ev : K -> list V -> option V)
    (holds : G -> list V -> Prop) (eqb : X -> X -> bool)
    : (X -> V) -> list (action K G X) -> (X -> V) -> Prop :=
  | Exec_nil : forall st, exec_all ev holds eqb st nil st
  | Exec_cons : forall st a mid rest out,
      exec ev holds eqb st a mid -> exec_all ev holds eqb mid rest out ->
      exec_all ev holds eqb st (a :: rest) out.

Module Type ACTIONS_OPS (P : TYPE) (E : TYPE) (X : KEY_OPS) (L : LANG_OPS).
  Parameter actions : P.t -> E.t -> list (action L.op L.guard X.t).
End ACTIONS_OPS.

Module Type ACTIONS_TIME (P : TYPE) (E : TYPE) (X : KEY_T) (L : LANG_T)
    (Import A : ACTIONS_OPS P E X L).
  Parameter T_actions : P.t -> E.t -> N.
  Parameter c_actions : N.
  (** Reading actions pays for the returned ordered list. *)
  Parameter T_actions_le : forall p e,
    (T_actions p e <= c_actions * N.of_nat (length (actions p e) + 1))%N.
End ACTIONS_TIME.

Module Type ACTIONS_T (P : TYPE) (E : TYPE) (X : KEY_T) (L : LANG_T) :=
  ACTIONS_OPS P E X L <+ ACTIONS_TIME P E X L.

Module Type INTERP_LINK (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (A : ACTIONS_OPS P E X L) (M : SEMANTICS P).
  Parameter point : M.state -> N.t.
  Parameter store : M.state -> X.t -> L.val.
  (** Every initial state occurs at a listed entry. *)
  Parameter init_entry : forall p s, M.initial p s -> In (point s) (C.entries p).
  (** Every concrete step follows a listed edge and its ordered actions. *)
  Parameter step_edge : forall p s s1, M.step p s s1 ->
    exists e, In e (C.edges p) /\ C.src p e = point s /\ C.dst p e = point s1 /\
      exec_all L.eval L.holds X.eqb (store s) (A.actions p e) (store s1).
End INTERP_LINK.

Module Type INTERP_SYSTEM (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY_OPS) (L : LANG_OPS) (V : VALUE_DOMAIN_OPS L)
    (A : ACTIONS_OPS P E X L) (D : STATE_DOMAIN_OPS X L V).
  Include SYSTEM_OPS D
    with Definition prog := P.t
    with Definition key := N.t
    with Definition row := dense_row N.t E.t
    with Definition frame := E.t.
  Include SYSTEM_SPEC D.
  (** Interpreter rows are entry seeds followed by the listed edges. *)
  Parameter rows_spec : forall p,
    rows p = List.map Seed (C.entries p) ++ List.map Flow (C.edges p).
  (** A seed writes its entry node. *)
  Parameter target_seed : forall p n, target p (Seed n) = n.
  (** A flow writes the edge destination. *)
  Parameter target_flow : forall p e, target p (Flow e) = C.dst p e.
  (** Every entry seed describes all concrete stores. *)
  Parameter eval_seed : forall p n look, eval p (Seed n) look = Some (D.top, nil).
  (** Flow evaluation applies abstract actions in their source order. *)
  Parameter eval_flow : forall p e look,
    eval p (Flow e) look = Some
      (fold_left (fun st a =>
        match a with
        | Assign x ex => D.assign x ex st
        | Havoc x => D.havoc x st
        | Assume g es => D.assume g es st
        end) (A.actions p e) (look (C.src p e)), nil).
End INTERP_SYSTEM.

Module Type INTERP_SOUND (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (A : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) (S : INTERP_SYSTEM P N E C X L V A D)
    (M : SEMANTICS P) (K : INTERP_LINK P N E C X L A M).
  (** Interpreter post-solutions cover every reachable concrete store. *)
  Parameter covers : forall p look, S.post_solution p look ->
    forall s, reachable (M.initial p) (M.step p) s -> D.gamma (look (K.point s)) (K.store s).
End INTERP_SOUND.

Module Type INTERP_ENVELOPE (P : TYPE) (E : TYPE) (X : KEY_T) (L : LANG_T)
    (V : VALUE_DOMAIN_T L) (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V).
  (* spec: primitive_work next_size *)
  Parameter primitive_work : P.t -> nat -> N.
  Parameter next_size : P.t -> nat -> nat.
  (** Primitive work grows with the input state size. *)
  Parameter primitive_work_mono : forall p s t, s <= t ->
    (primitive_work p s <= primitive_work p t)%N.
  (** Primitive output envelopes grow with the input state size. *)
  Parameter next_size_mono : forall p s t, s <= t -> next_size p s <= next_size p t.
  (** Listed assignments fit the primitive work envelope. *)
  Parameter assign_work_le : forall p e x ex st s, In (Assign x ex) (A.actions p e) ->
    D.size st <= s -> (N.of_nat (D.assign_work x ex st) <= primitive_work p s)%N.
  (** Listed havoc actions fit the primitive work envelope. *)
  Parameter havoc_work_le : forall p e x st s, In (Havoc x) (A.actions p e) ->
    D.size st <= s -> (N.of_nat (D.havoc_work x st) <= primitive_work p s)%N.
  (** Listed guards fit the primitive work envelope. *)
  Parameter assume_work_le : forall p e g es st s, In (Assume g es) (A.actions p e) ->
    D.size st <= s -> (N.of_nat (D.assume_work g es st) <= primitive_work p s)%N.
  (** Listed assignments fit the next-state size envelope. *)
  Parameter assign_size_le : forall p e x ex st s, In (Assign x ex) (A.actions p e) ->
    D.size st <= s -> D.size (D.assign x ex st) <= next_size p s.
  (** Listed havoc actions fit the next-state size envelope. *)
  Parameter havoc_size_le : forall p e x st s, In (Havoc x) (A.actions p e) ->
    D.size st <= s -> D.size (D.havoc x st) <= next_size p s.
  (** Listed guards fit the next-state size envelope. *)
  Parameter assume_size_le : forall p e g es st s, In (Assume g es) (A.actions p e) ->
    D.size st <= s -> D.size (D.assume g es st) <= next_size p s.
End INTERP_ENVELOPE.

Module Type INTERP_COST_SPEC (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V)
    (B : INTERP_ENVELOPE P E X L V A D).
  Definition max_actions p : nat := fold_right Nat.max 0
    (List.map (fun e => length (A.actions p e)) (C.edges p)).
  Fixpoint state_extent p n s : nat :=
    match n with
    | O => s
    | S n1 => state_extent p n1 (Nat.max s (B.next_size p s))
    end.
  Fixpoint fold_work p n s : N :=
    match n with
    | O => 1%N
    | S n1 => (B.primitive_work p s + 1 +
        fold_work p n1 (Nat.max s (B.next_size p s)))%N
    end.
  Definition interp_work p s : N :=
    (N.of_nat (D.size D.top + max_actions p + 1) +
      N.of_nat (state_extent p (max_actions p) s) + fold_work p (max_actions p) s)%N.
  Definition interp_kw p : nat := fold_right Nat.max 0
    (List.map N.bits (C.entries p ++
      flat_map (fun e => C.src p e :: C.dst p e :: nil) (C.edges p))).
End INTERP_COST_SPEC.

Module Type INTERP (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (X : KEY) (L : LANG) (V : VALUE_DOMAIN L) (A : ACTIONS_OPS P E X L)
    (D : STATE_DOMAIN X L V) :=
  INTERP_SYSTEM P N E C X L V A D <+ SYSTEM_LAWS D.

Module Type INTERP_TIME (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V)
    (B : INTERP_ENVELOPE P E X L V A D) (Import S : INTERP P N E C X L V A D).
  Include INTERP_COST_SPEC P N E C X L V A D B.
  Include SYSTEM_TIME D S with Definition row_work := interp_work with Definition kw := interp_kw.
End INTERP_TIME.

Module Type INTERP_T (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_BASE_T P N E) (X : KEY_T) (L : LANG_T) (V : VALUE_DOMAIN_T L)
    (A : ACTIONS_T P E X L) (D : STATE_DOMAIN_T X L V)
    (B : INTERP_ENVELOPE P E X L V A D) :=
  INTERP P N E C X L V A D <+ INTERP_TIME P N E C X L V A D B.
