(** * Sparse control and parameter fixtures

    A diamond propagates a constant through a parameter and rejects its contradictory arm.
    For example, the join parameter receives two from the executable left predecessor.
    Builds on: FrameworkSparseSound and FrameworkSparseTest. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeConcrete LatticeAdjoin.
From Galois.Bits Require Import BitsWord BitsOp BitsExpr.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramSsa.
From Galois.Domains Require Import DomainsValue DomainsPoint DomainsTagged DomainsBitsValue.
From Galois.Fixpoint Require Import FixpointAnalysis FixpointAnalyze FixpointSolver FixpointCheck.
From Galois.Framework Require Import FrameworkSparse FrameworkSparseSound.
From Galois.Tests.Framework Require Import FrameworkDenseTest FrameworkSparseTest.
Import List.ListNotations Expr Sparse.
Local Open Scope nat_scope.

Definition phi_ssa : Ssa.t nat nat nat expr (bits_guard word) :=
  Ssa.of_pure diamond nat_encoding [0; 1; 2; 3]
    (fun x => match x with
      | 0 => Param 0 0
      | 1 => Op (App bvadd [Var 0; Var 1]) [0; 0]
      | 2 => Param 3 0
      | _ => Arbitrary
      end)
    (fun x => if Nat.eqb x 2 then 3 else 0)
    (fun b => match b with 0 => [0] | 3 => [2] | _ => [] end)
    (fun _ => [1])
    (fun e => match e with
      | 0 => [(Equal (32%positive, 2%Z), [1])]
      | 1 => [(Equal (32%positive, 0%Z), [1])]
      | _ => []
      end).

Definition phi_problem := Sparse.Make phi_ssa values (fun _ => Cost.ret (number 1)).
Definition phi_analysis := sparse_analysis phi_problem 0.

Example diamond_constant_through_phi :
  observe phi_analysis 32
    [UVal 0; UVal 1; UVal 2; UVal 3; UEdge 0; UEdge 1; UEdge 2; UEdge 3;
      UBlock 0; UBlock 1; UBlock 2; UBlock 3] =
  Some [Some (number 1); Some (number 2); Some (number 2); Some TAny;
    Some TAny; None; Some TAny; None; Some TAny; Some TAny; None; Some TAny].
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_analyze_finishes :
  match analyze phi_analysis 32 with Outcome.Solved _ => true | _ => false end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_zero_fuel :
  observe phi_analysis 1 [UVal 2] = None.
Proof.
  vm_compute; reflexivity.
Qed.

Definition phi_candidate (u : unknown nat nat nat) :=
  match u with
  | UVal 0 => Some (number 1)
  | UVal 1 | UVal 2 => Some (number 2)
  | UVal 3 => Some TAny
  | UVal _ => None
  | UEdge 1 | UEdge 3 | UBlock 2 => None
  | _ => Some TAny
  end.

Example diamond_post_solution_checked :
  check_post (Analysis.lat phi_analysis) (Analysis.system phi_analysis) phi_candidate = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example diamond_unsound_phi_rejected :
  check_post (Analysis.lat phi_analysis) (Analysis.system phi_analysis)
    (fun u => match u with UVal 2 => Some (number 0) | _ => phi_candidate u end) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Definition one_block_ssa : Ssa.t nat nat nat expr (bits_guard word) :=
  Ssa.of_pure singleton nat_encoding [0] (fun _ => Param 0 0)
    (fun _ => 0) (fun _ => [0]) (fun _ => []) (fun _ => []).

Example one_block_entry_parameter :
  observe (sparse_analysis (Sparse.Make one_block_ssa values (fun _ => Cost.ret (number 7))) 0)
    4 [UBlock 0; UVal 0; UEdge 0] = Some [Some TAny; Some (number 7); None].
Proof.
  vm_compute; reflexivity.
Qed.

Example executable_distinguishes_reached_empty :
  (SparseSound.executable (Some (@TBot point)), SparseSound.executable (@None (tagged point))) =
    (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** The semantic client uses a weak boolean domain and creates each kind of binding. *)
Definition unit_domain : ValueAbs.t bool unit bool :=
  @ValueAbs.Make bool unit bool bool_lattice true (fun _ _ => Cost.ret true)
    (fun _ _ fs => Cost.ret fs)
    (fun g fs => Cost.ret (if g then fs else map (fun _ => false) fs)).

Definition unit_semantics : ValueSem.t unit unit bool :=
  @ValueSem.Make unit unit bool (fun _ _ => Some tt) (fun g _ => g = true).

Definition unit_gamma : concretisation bool unit :=
  @Concretisation bool unit (fun a _ => a = true).

Example unit_domain_laws : value_laws unit_domain unit_semantics unit_gamma.
Proof.
  constructor.
  - exact bool_laws.
  - constructor; intros [|] [|] [] Hle Ha; discriminate || reflexivity.
  - intros [] Hfalse; discriminate.
  - intros []; reflexivity.
  - intros; reflexivity.
  - intros k a fs cs c Hfs _ _; exact Hfs.
  - intros [|] fs cs Hfs Hholds; [exact Hfs|discriminate].
  - intros; reflexivity.
  - intros [|] fs; [reflexivity|apply length_map].
Qed.

Definition origin_ssa : Ssa.t nat nat nat unit bool :=
  Ssa.of_pure diamond nat_encoding [0; 1; 2; 3]
    (fun x => match x with
      | 0 => Param 0 0
      | 1 => Op tt []
      | 2 => Param 3 0
      | _ => Arbitrary
      end)
    (fun x => if Nat.eqb x 2 then 3 else 0)
    (fun b => match b with 0 => [0] | 3 => [2] | _ => [] end)
    (fun _ => [1])
    (fun e => if Nat.eqb e 1 then [(false, [0])] else []).

Definition origin_machine : semantics nat unit :=
  Semantics (fun s => s = 0) (fun s l t =>
    l = [] /\ ((s = 0 /\ t = 1) \/ (s = 1 /\ t = 3))).

Definition origin_link : Link.t nat unit nat nat :=
  Link.Make (fun s => s)
    (fun s _ _ e => (s = 0 /\ e = 0) \/ (s = 1 /\ e = 2))
    (fun _ _ _ => False).

Definition origin_values : SsaLink.t nat unit nat nat nat unit :=
  SsaLink.Make origin_link (fun s x => match x with
    | 0 => Some tt
    | 1 => if Nat.eqb s 0 then None else Some tt
    | 2 => if Nat.eqb s 3 then Some tt else None
    | 3 => if Nat.eqb s 1 then Some tt else None
    | _ => None
    end).

Example origin_link_laws : link_laws origin_machine (Cfg.graph diamond) origin_link.
Proof.
  constructor.
  - constructor.
    + change (NoDup [0; 1; 2; 3]).
      repeat (apply NoDup_cons; [cbn; intuition congruence|]).
      apply NoDup_nil.
    + intros v [<-|Hbad]; [left; reflexivity|contradiction].
    + intros [|[|[|v]]] e Hin; vm_compute in Hin;
        intuition (subst; vm_compute; reflexivity).
    + intros [|[|[|v]]] e _ Hin; vm_compute in Hin;
        intuition (subst; vm_compute; tauto).
  - intros s ->; left; reflexivity.
  - intros s l t _ [Hl [[-> ->]|[-> ->]]]; right.
    + exists 0; left; split; reflexivity.
    + exists 2; right; split; reflexivity.
  - intros e s l t _ [Hl [[-> ->]|[-> ->]]] [[Hsource ->]|[Hsource ->]];
      try discriminate; vm_compute; tauto.
  - intros s l t _ _ Hbad; contradiction.
Qed.

Example origin_ssa_laws :
  ssa_laws origin_machine origin_ssa origin_values
    (ValueSem.eval unit_semantics) (ValueSem.holds unit_semantics).
Proof.
  constructor.
  - exact origin_link_laws.
  - intros [|[|[|x]]] b i Hdef; cbn in Hdef; try discriminate;
      injection Hdef as <- <-; reflexivity.
  - intros e s l t _ _ Htaken g ys Hguard.
    destruct Htaken as [[_ ->]|[_ ->]]; vm_compute in Hguard; contradiction.
  - intros e s l t _ _ Htaken g ys x k args Hguard.
    destruct Htaken as [[_ ->]|[_ ->]]; vm_compute in Hguard; contradiction.
  - intros x [] s l t _ [Hl [[-> ->]|[-> ->]]] Hval;
      destruct x as [|[|[|[|x]]]]; cbn in Hval; try discriminate.
    + left; reflexivity.
    + right; left; exists tt, [], []; repeat split; constructor.
    + right; right; right; reflexivity.
    + left; reflexivity.
    + left; reflexivity.
    + right; right; left; exists 2, 3, 0, 1; repeat split; try reflexivity.
      right; split; reflexivity.
  - intros s [|[|[|[|x]]]] [] _ Hval; vm_compute in Hval;
      try discriminate; vm_compute; tauto.
Qed.

Definition origin_problem := Sparse.Make origin_ssa unit_domain (fun _ => Cost.ret true).

Example origin_entry_ok :
  SparseSound.sparse_entry_ok origin_machine origin_problem origin_values unit_gamma.
Proof.
  intros s [|[|[|[|x]]]] [] -> Hval; cbn in Hval; try discriminate.
  exists 0, 0; repeat split; try reflexivity; left; reflexivity.
Qed.

Definition origin_candidate (u : unknown nat nat nat) :=
  match u with
  | UVal 0 | UVal 1 | UVal 2 | UVal 3 => Some true
  | UVal _ => None
  | UEdge 1 | UEdge 3 | UBlock 2 => None
  | _ => Some true
  end.

Example origin_post_checked :
  check_post (Analysis.lat (sparse_analysis origin_problem 0))
    (Analysis.system (sparse_analysis origin_problem 0)) origin_candidate = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example all_origins_sound_client :
  (forall s, reachable_state origin_machine s ->
    SparseSound.executable (origin_candidate (UBlock s)) = true) /\
  (forall s l t e, reachable_state origin_machine s -> step origin_machine s l t ->
    Link.taken origin_link s l t e ->
    SparseSound.executable (origin_candidate (UEdge e)) = true) /\
  (forall s x c, reachable_state origin_machine s ->
    SsaLink.val origin_values s x = Some c ->
    gamma (lift_bot_gamma unit_gamma) (origin_candidate (UVal x)) c).
Proof.
  apply (SparseSound.sparse_sound origin_machine origin_problem origin_values
    unit_semantics unit_gamma 0 origin_candidate).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact origin_ssa_laws.
  - exact unit_domain_laws.
  - exact origin_entry_ok.
  - apply (proj1 (check_post_iff _ _ _) origin_post_checked).
Qed.
