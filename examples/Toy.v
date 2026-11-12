(** * Integer counter analysis

    A hand-built policy analyzes a small counter loop using interval environments.
    For example, the exit edge tests whether the counter equals ten.
    Builds on: Framework.Interp, Domains.Interval and States.Env. *)

From Stdlib Require Import List ZArith NArith PArith.
From Galois.Base Require Import KeySig Key Map Trie Heap.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ThresholdsSig Thresholds ZLang Interval.
From Galois.States Require Import Env.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import InterpSig Interp.
Import List.ListNotations.

Inductive instr :=
  | Set_ (x : positive) (e : term zview positive)
  | Guard (g : zguardview) (es : list (term zview positive)).
Record toy := Toy { entry : positive; code : list (positive * instr * positive) }.

Module ToyProg <: TYPE. Definition t := toy. End ToyProg.
Module ToyEdge <: TYPE. Definition t := (positive * instr * positive)%type. End ToyEdge.
Module ToyCfg <: CFG_OPS ToyProg PosKeyCode ToyEdge.
  Definition entries (p : toy) := [entry p].
  Definition edges (p : toy) := code p.
  Definition src (_ : toy) (e : ToyEdge.t) := fst (fst e).
  Definition dst (_ : toy) (e : ToyEdge.t) := snd e.
End ToyCfg.
Module ToyActions <: ACTIONS_OPS ToyProg ToyEdge PosKeyCode ZLangCode.
  Definition actions (_ : toy) (e : ToyEdge.t) : list (action zview zguardview positive) :=
    match snd (fst e) with
    | Set_ x ex => [Assign x ex]
    | Guard g es => [Assume g es]
    end.
End ToyActions.

Module XM := TrieMapCode PosKeyCode.
Module IV := IntervalCode ZLangCode ThresholdsCode.
Module Dom := EnvCode PosKeyCode XM ZLangCode IV.
Module Sys := InterpCode ToyProg PosKeyCode ToyEdge ToyCfg PosKeyCode ZLangCode IV
  ToyActions Dom.
Module Pol := PolicyCode Dom.
Module Chk := CheckCode Dom Sys.
Module Refine := NarrowCode Dom Sys Chk.
Module Solve := WorklistCode Dom Sys Pol HeapCode.
Module Run := CertifiedCode Dom Sys Solve Chk Refine.

Definition i : positive := 1%positive.
Definition lit (z : Z) : term zview positive := Node (ZConst z) [].
Definition count : toy := Toy 1%positive
  [(1%positive, Set_ i (lit 0), 2%positive);
   (2%positive, Guard (ZGuardCmp Lt) [Leaf i; lit 10], 3%positive);
   (3%positive, Set_ i (Node ZAdd [Leaf i; lit 1]), 2%positive);
   (2%positive, Guard (ZGuardCmp Eq) [Leaf i; lit 10], 4%positive);
   (2%positive, Guard (ZGuardCmp Gt) [Leaf i; lit 10], 4%positive)].
Definition pol : policy IV.wparam :=
  Policy IV.wparam PTrieCode.empty (PTrieCode.set 2%positive (HeadCfg 0%N 0) PTrieCode.empty)
    TLeaf 2.

Example count_solved :
  match Run.analyze count pol 100%N with
  | Solved _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example count_exit_interval :
  match Run.analyze count pol 100%N with
  | Solved m => Dom.eval (Leaf i) (Chk.look m 4%positive)
  | _ => IBot
  end = I (Fin 10) (Fin 10).
Proof.
  vm_compute; reflexivity.
Qed.
