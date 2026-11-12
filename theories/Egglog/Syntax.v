(** * Relational engine syntax

    Programs contain declarations and flat rules over cells and terms.
    For example, a relation declaration has output kind [ORel].
    Builds on: Stdlib lists and binary arithmetic, Base key signatures, and Argent. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.

Inductive cell (V : Type) : Type :=
  | Id (i : positive)
  | Val (v : V).

Arguments Id {V}.
Arguments Val {V}.

Inductive term (V : Type) : Type :=
  | Var (x : positive)
  | Lit (v : V).

Arguments Var {V}.
Arguments Lit {V}.

Inductive output : Type :=
  | ORel
  | OId
  | OLat (merge_op : positive).

Record decl : Type := Decl { name : positive; arity : nat; out : output }.

Inductive atom (V : Type) : Type :=
  | Fun (f : positive) (args : list (term V)) (res : option (term V))
  | Prim (p : positive) (args : list (term V)) (res : term V).

Inductive action (V : Type) : Type :=
  | Make (x : positive) (f : positive) (args : list (term V))
  | Put (f : positive) (args : list (term V)) (res : option (term V))
  | Union (a b : term V)
  | Let (x : positive) (p : positive) (args : list (term V)).

Arguments Make {V}.
Arguments Put {V}.
Arguments Union {V}.
Arguments Let {V}.

Record rule (V : Type) : Type := Rule { query : list (atom V); actions : list (action V) }.
Record program (V : Type) : Type := Program { decls : list decl; rules : list (rule V) }.
Record limits : Type := Limits { max_iter : N; max_ids : N }.
Inductive stop : Type :=
  | Saturated
  | IterLimit
  | IdLimit.

Inductive source (V : Type) : Type :=
  | All (slot : nat)
  | New (slot : nat)
  | Const (c : cell V).
Record jplan : Type := JPlan { nvars : nat; cols : list (list nat) }.
Record cplan (V : Type) : Type := CPlan {
  rule_ix : nat;
  join : jplan;
  sources : list (source V);
  var_of : list positive;
  post : list nat
}.
Record compiled (V : Type) : Type := Compiled {
  slots : list (positive * list nat);
  naive : list (cplan V);
  seminaive : list (cplan V)
}.

TimeFun name.
TimeFun out.
TimeFun actions.
TimeFun decls.
TimeFun rules.

Definition relational_output (d : decl) : bool :=
  match out d with
  | ORel => true
  | _ => false
  end.
TimeFun relational_output.

Definition relational_action {V} (a : action V) : bool :=
  match a with
  | Put _ _ _ | Let _ _ _ => true
  | _ => false
  end.
TimeFun relational_action.

Definition relational_rule {V} (r : rule V) : bool :=
  forallb relational_action (actions V r).
TimeFun relational_rule.

Definition relational_fragment {V} (p : program V) : bool :=
  forallb relational_output (decls V p) && forallb relational_rule (rules V p).
TimeFun relational_fragment.

Module CellKeyCode (V : KEY_OPS) <: KEY_OPS.
  Definition t := cell V.t.
  Definition encode (c : t) : positive :=
    match c with
    | Id i => xO i
    | Val v => xI (V.encode v)
    end.
  Definition eqb (a b : t) : bool :=
    match a, b with
    | Id i, Id j => Pos.eqb i j
    | Val v, Val w => V.eqb v w
    | _, _ => false
    end.
End CellKeyCode.

Module CellKey (V : KEY) <: KEY.
  Include CellKeyCode V.
  Include KEY_SPEC.
  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros [i | v] [j | w] H; cbn in H; try discriminate.
    - injection H as H. now subst.
    - injection H as H. apply V.encode_inj in H. now subst.
  Qed.
  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    intros [i | v] [j | w]; cbn.
    - destruct (Pos.eqb_spec i j); constructor; congruence.
    - constructor; discriminate.
    - constructor; discriminate.
    - destruct (V.eqb_spec v w); constructor; congruence.
  Qed.
End CellKey.

Module CellKeyT (V : KEY_T) <: KEY_T.
  Include CellKey V.
  TimeFun encode.
  TimeFun eqb.
  Definition c_key : N := 1. (* STUB *)
  Lemma T_encode_le : forall k, (T_encode k <= c_key * N.of_nat (bits k + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_eqb_le : forall a b, (T_eqb a b <= c_key * N.of_nat (bits a + 1))%N.
  Proof. Admitted. (* STUB *)
End CellKeyT.
