(** * Recurrence update idioms

    The update table constructs additive, multiplicative and direct-doubling recurrences.
    For example, direct doubling uses a geometric recurrence with mathematical coefficient two.
    Builds on: AnalysesLoopsChrec and CostMonad. *)

From Stdlib Require Import List Bool ZArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Analyses.Loops Require Import AnalysesLoopsChrec.
Import List.ListNotations Cost.Notations Chrec.

Module Idiom.

(** The supported update shapes distinguish direct doubling from an independent multiplier. *)
Inductive kind : Type :=
  | SAdd
  | SMul
  | SDouble.

(** Each entry contains its shape and its charged constructor, without semantic proof fields. *)
Record t (V : Type) : Type := Make {
  shape : kind;
  build_c : Chrec.t V -> option (Chrec.t V) -> Cost.t (option (Chrec.t V))
}.

Arguments Make {V}.
Arguments shape {V}.
Arguments build_c {V}.

(** Projected construction has the same option result as the costed callback. *)
Definition build {V} (entry : t V) base other :=
  Cost.value (build_c entry base other).

Definition add_c {V} (base : Chrec.t V) (other : option (Chrec.t V))
    : Cost.t (option (Chrec.t V)) :=
  Cost.step ;;
  Cost.ret (option_map (CRec base) other).

Definition mul_c {V} (base : Chrec.t V) (other : option (Chrec.t V))
    : Cost.t (option (Chrec.t V)) :=
  Cost.step ;;
  Cost.ret (option_map (CGeo base) other).

Definition double_c {V} (base : Chrec.t V) (other : option (Chrec.t V))
    : Cost.t (option (Chrec.t V)) :=
  Cost.step ;;
  match other with
  | None => Cost.ret (Some (CGeo base (CInv (IConst 2))))
  | Some _ => Cost.ret None
  end.

(** The extensible table is the single owner of the direct-doubling coefficient. *)
Definition table {V} : list (t V) :=
  [Make SAdd add_c; Make SMul mul_c; Make SDouble double_c].

(** A successful entry obeys its local recurrence equation under every invariant environment. *)
Definition entry_laws {V} (entry : t V) : Prop :=
  forall base other c, build entry base other = Some c ->
    forall inv : V -> Z,
    Chrec.eval inv c O = Chrec.eval inv base O /\
      forall k,
      match shape entry, other with
      | SAdd, Some step =>
        Chrec.eval inv c (S k) = (Chrec.eval inv c k + Chrec.eval inv step k)%Z
      | SMul, Some ratio =>
        Chrec.eval inv c (S k) = (Chrec.eval inv c k * Chrec.eval inv ratio k)%Z
      | SDouble, None =>
        Chrec.eval inv c (S k) = (Chrec.eval inv c k + Chrec.eval inv c k)%Z
      | _, _ => False
      end.

Lemma add_laws {V} : entry_laws (@Make V SAdd add_c).
Proof.
  intros base [step|] c Hbuild inv; [|discriminate].
  injection Hbuild as Heq; subst c; split; reflexivity.
Qed.

Lemma mul_laws {V} : entry_laws (@Make V SMul mul_c).
Proof.
  intros base [ratio|] c Hbuild inv; [|discriminate].
  injection Hbuild as Heq; subst c; split; reflexivity.
Qed.

Lemma double_laws {V} : entry_laws (@Make V SDouble double_c).
Proof.
  intros base [other|] c Hbuild inv; [discriminate|].
  injection Hbuild as Heq; subst c; split; [reflexivity|].
  intro k.
  change ((Chrec.eval inv (CGeo base (CInv (IConst 2))) k * 2)%Z =
    (Chrec.eval inv (CGeo base (CInv (IConst 2))) k +
      Chrec.eval inv (CGeo base (CInv (IConst 2))) k)%Z).
  ring.
Qed.

(** Every actual table entry satisfies its update's universal evaluation law. *)
Theorem table_sound {V} : Forall (@entry_laws V) table.
Proof.
  constructor; [apply add_laws|].
  constructor; [apply mul_laws|].
  constructor; [apply double_laws|constructor].
Qed.

Definition kind_eqb (left right : kind) : bool :=
  match left, right with
  | SAdd, SAdd | SMul, SMul | SDouble, SDouble => true
  | _, _ => false
  end.

(** Table dispatch charges every inspected row and the selected construction callback. *)
Fixpoint dispatch_c {V} (entries : list (t V)) wanted base other
    : Cost.t (option (Chrec.t V)) :=
  match entries with
  | [] => Cost.ret None
  | entry :: rest =>
    Cost.step ;;
    if kind_eqb wanted (shape entry) then
      Cost.step ;; build_c entry base other
    else dispatch_c rest wanted base other
  end.

(** Update construction dispatches through the actual table. *)
Definition apply_c {V} wanted (base : Chrec.t V) other :=
  dispatch_c table wanted base other.

Definition apply {V} wanted (base : Chrec.t V) other :=
  Cost.value (apply_c wanted base other).

(** Dispatch selects the original additive, multiplicative or doubling form. *)
Theorem apply_equation {V} wanted (base : Chrec.t V) other :
  apply wanted base other =
  match wanted with
  | SAdd => option_map (CRec base) other
  | SMul => option_map (CGeo base) other
  | SDouble =>
    match other with
    | None => Some (CGeo base (CInv (IConst 2)))
    | Some _ => None
    end
  end.
Proof.
  destruct wanted, other; reflexivity.
Qed.

(** Selected table construction satisfies its initial and successor evaluation laws. *)
Theorem apply_sound {V} wanted (base : Chrec.t V) other c :
  apply wanted base other = Some c -> forall inv : V -> Z,
  Chrec.eval inv c O = Chrec.eval inv base O /\
  forall k,
    match wanted, other with
    | SAdd, Some step =>
      Chrec.eval inv c (S k) = (Chrec.eval inv c k + Chrec.eval inv step k)%Z
    | SMul, Some ratio =>
      Chrec.eval inv c (S k) = (Chrec.eval inv c k * Chrec.eval inv ratio k)%Z
    | SDouble, None =>
      Chrec.eval inv c (S k) = (Chrec.eval inv c k + Chrec.eval inv c k)%Z
    | _, _ => False
    end.
Proof.
  destruct wanted; intros Happly inv.
  - exact (add_laws base other c Happly inv).
  - exact (mul_laws base other c Happly inv).
  - exact (double_laws base other c Happly inv).
Qed.

(** The concrete table pays at most its three row visits and two callback ticks. *)
Theorem apply_cost {V} wanted (base : Chrec.t V) other :
  (Cost.ticks (apply_c wanted base other) <= 5)%N.
Proof.
  destruct wanted, other; vm_compute; discriminate.
Qed.

End Idiom.
