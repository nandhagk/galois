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
