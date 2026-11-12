(** * Integer counter analysis

    A hand-built policy analyzes a small counter loop using interval environments.
    For example, the exit edge tests whether the counter equals ten.
    Builds on: Framework.Interp, Domains.Interval and States.Env. *)

From Stdlib Require Import List ZArith NArith PArith Lia.
From Galois.Base Require Import KeySig Key Map Trie Heap.
From Galois.Domains Require Import LangSig ValueSig IntervalSig ThresholdsSig Thresholds ZLang Interval.
From Galois.States Require Import Env.
From Galois.Fixpoint Require Import PolicySig SolverSig Policy Check Narrow Worklist Certified.
From Galois.Program Require Import SemanticsSig CfgSig.
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

Module ToySem <: SEMANTICS ToyProg.
  Definition state := (positive * (positive -> Z))%type.
  Definition initial (p : toy) (s : state) : Prop := fst s = entry p.
  Definition step (p : toy) (s s1 : state) : Prop :=
    exists e, In e (code p) /\ fst (fst e) = fst s /\ snd e = fst s1 /\
      exec_all ZLang.eval ZLang.holds PosKey.eqb (snd s)
        (ToyActions.actions p e) (snd s1).
End ToySem.

Module ToyLink <: INTERP_LINK ToyProg PosKey ToyEdge ToyCfg PosKey ZLang ToyActions ToySem.
  Definition point (s : ToySem.state) : positive := fst s.
  Definition store (s : ToySem.state) : positive -> Z := snd s.

  (** Initial counter states occur at the program entry. *)
  Lemma init_entry : forall p s, ToySem.initial p s -> In (point s) (ToyCfg.entries p).
  Proof.
    intros p s Hinitial. left. symmetry. exact Hinitial.
  Qed.

  (** Every counter transition follows its listed edge and ordered actions. *)
  Lemma step_edge : forall p s s1, ToySem.step p s s1 ->
    exists e, In e (ToyCfg.edges p) /\ ToyCfg.src p e = point s /\
      ToyCfg.dst p e = point s1 /\
      exec_all ZLang.eval ZLang.holds PosKey.eqb (store s)
        (ToyActions.actions p e) (store s1).
  Proof.
    intros p s s1 Hstep. exact Hstep.
  Qed.
End ToyLink.

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

Module PlainXM := TrieMap PosKey.
Module PlainIV := Interval ZLang Thresholds.
Module PlainDom := Env PosKey PlainXM ZLang PlainIV.
Module PlainSys := InterpSound ToyProg PosKey ToyEdge ToyCfg PosKey ZLang PlainIV
  ToyActions PlainDom ToySem ToyLink.
Module PlainChk := Check PlainDom PlainSys.
Module PlainRefine := Narrow PlainDom PlainSys PlainChk.
Module PlainSolve := Solve.
Module PlainRun := Certified PlainDom PlainSys PlainSolve PlainChk PlainRefine.

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

(** The certified counter result covers every reachable concrete store. *)
Theorem count_covers : forall m, PlainRun.analyze count pol 100%N = Solved m ->
  forall s, reachable (ToySem.initial count) (ToySem.step count) s ->
  PlainDom.gamma (PlainChk.look m (fst s)) (snd s).
Proof.
  intros m Hrun s Hreachable.
  exact (PlainSys.covers count _ (PlainRun.analyze_sound _ _ _ _ Hrun) s Hreachable).
Qed.

(** Every reachable exit state has counter value ten. *)
Corollary exit_value : forall s,
  reachable (ToySem.initial count) (ToySem.step count) s ->
  fst s = 4%positive -> snd s i = 10%Z.
Proof.
  intros s Hreachable Hpoint.
  destruct (PlainRun.analyze count pol 100%N) as [m|m|why] eqn:Hrun;
    [|vm_compute in Hrun; discriminate..].
  pose proof (count_covers m Hrun s Hreachable) as Hgamma.
  vm_compute in Hrun. injection Hrun as <-. rewrite Hpoint in Hgamma.
  cbn in Hgamma. destruct Hgamma as [_ Hgamma].
  specialize (Hgamma i).
  change (10 <= snd s i <= 10)%Z in Hgamma. lia.
Qed.
