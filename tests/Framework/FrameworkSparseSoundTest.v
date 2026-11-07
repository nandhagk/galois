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
From Galois.Domains Require Import DomainsValue DomainsPoint DomainsTagged DomainsNumeric
  DomainsBitsValue.
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

(** The numeric client evaluates the fixture's expressions over normalized word arguments. *)
Definition phi_normalize (c : word) : word := (fst c, wrap (fst c) (snd c)).

Definition phi_eval (e : expr) (cs : list word) : option word :=
  eval eval_op (fun i => nth i (map phi_normalize cs) (1%positive, 0%Z)) e.

Definition phi_truth (c : word) := negb (Z.eqb (snd (phi_normalize c)) 0).
Definition phi_value_sem := bits_sem bridge phi_eval phi_truth.
Definition phi_gamma :=
  numeric_conc (tagged_domain point_word_domain) (tagged_gamma point_gamma) bridge.
Definition phi_one : word := (32%positive, 1%Z).
Definition phi_two : word := (32%positive, 2%Z).

Example phi_bridge_laws : op_bridge_laws bridge phi_eval phi_truth.
Proof.
  constructor.
  - intros [v z] [w t] Hword.
    change (Some (v, wrap v z) = Some (w, t)) in Hword.
    injection Hword as <- <-; apply wrap_is_word.
  - intros k cs c e Hresult Hexpr.
    change (Some k = Some e) in Hexpr; injection Hexpr as <-.
    exists (map phi_normalize cs), c; split.
    + clear Hresult; induction cs as [|d cs IH].
      * constructor.
      * constructor; [reflexivity|exact IH].
    + split; [exact Hresult|].
      destruct c as [w z].
      change (Some (w, wrap w z) = Some (w, z)).
      rewrite wrap_id; [reflexivity|].
      exact (eval_is_word eval_op eval_op_is_word (w, z)
        (fun i => nth i (map phi_normalize cs) (1%positive, 0%Z)) k Hresult).
  - intros [v z] [w t] Hword.
    change (Some (v, wrap v z) = Some (w, t)) in Hword.
    injection Hword as <- <-; reflexivity.
  - intros _ c; exists (phi_normalize c); reflexivity.
  - intros d Hdisabled; discriminate.
  - intros d c wc wd Hdisabled; discriminate.
  - intros d c w Hdisabled; discriminate.
Qed.

Example phi_value_laws : value_laws values phi_value_sem phi_gamma.
Proof.
  apply bits_values_laws.
  - apply tagged_numeric_laws; exact point_word_laws.
  - exact phi_bridge_laws.
  - intros w z _; exact I.
  - reflexivity.
Qed.

(** The operation executes before branching, so guards read its actual stored result. *)
Inductive phi_state : Type :=
  | PhiStart
  | PhiReady
  | PhiArm (left : bool)
  | PhiDone.

Definition phi_branch_holds (left : bool) :=
  phi_two = (32%positive, if left then 2%Z else 0%Z).

Inductive phi_step : phi_state -> list unit -> phi_state -> Prop :=
  | PhiCompute : phi_step PhiStart [] PhiReady
  | PhiBranch : forall left, phi_branch_holds left ->
      phi_step PhiReady [] (PhiArm left)
  | PhiMerge : forall left, phi_step (PhiArm left) [] PhiDone.

Definition phi_machine : semantics phi_state unit :=
  Semantics (fun s => s = PhiStart) phi_step.

Definition phi_point s :=
  match s with
  | PhiStart | PhiReady => 0
  | PhiArm true => 1
  | PhiArm false => 2
  | PhiDone => 3
  end.

Definition phi_link : Link.t phi_state unit nat nat :=
  Link.Make phi_point
    (fun s _ t e => match s, t with
      | PhiReady, PhiArm b => e = if b then 0 else 1
      | PhiArm b, PhiDone => e = if b then 2 else 3
      | _, _ => False
      end)
    (fun s _ t => s = PhiStart /\ t = PhiReady).

Definition phi_values : SsaLink.t phi_state unit nat nat nat word :=
  SsaLink.Make phi_link (fun s x => match x with
    | 0 => Some phi_one
    | 1 => match s with PhiStart => None | _ => Some phi_two end
    | 2 => match s with PhiDone => Some phi_two | _ => None end
    | 3 => match s with PhiArm _ => Some (32%positive, 19%Z) | _ => None end
    | _ => None
    end).

Example phi_link_laws : link_laws phi_machine (Cfg.graph diamond) phi_link.
Proof.
  constructor.
  - exact (cfg_wf origin_link_laws).
  - intros s ->; left; reflexivity.
  - intros s l t _ Hstep; destruct Hstep.
    + left; split; reflexivity.
    + right; exists (if left then 0 else 1); reflexivity.
    + right; exists (if left then 2 else 3); reflexivity.
  - intros e s l t _ Hstep Htaken; destruct Hstep; [contradiction| |].
    + change (e = if left then 0 else 1) in Htaken; subst e.
      destruct left; vm_compute; tauto.
    + change (e = if left then 2 else 3) in Htaken; subst e.
      destruct left; vm_compute; tauto.
  - intros s l t _ _ [-> ->]; reflexivity.
Qed.

(** A branch guard and its operation witness use the same concrete subject and operands. *)
Example phi_guard_holds e s l t :
  step phi_machine s l t -> Link.taken phi_link s l t e ->
  forall g ys, In (g, ys) (Ssa.guards phi_ssa e) ->
    exists cs, Forall2 (fun y c => SsaLink.val phi_values s y = Some c) ys cs /\
      ValueSem.holds phi_value_sem g cs.
Proof.
  intros Hstep Htaken g ys Hguard; destruct Hstep as [|left Hbranch|left];
    [contradiction| |].
  - change (e = if left then 0 else 1) in Htaken; subst e.
    destruct left; cbn in Hguard;
      destruct Hguard as [Heq|Hbad]; try contradiction; inversion Heq; subst g ys.
    + exists [phi_two]; split.
      * constructor; [reflexivity|constructor].
      * exact Hbranch.
    + exists [phi_two]; split.
      * constructor; [reflexivity|constructor].
      * exact Hbranch.
  - change (e = if left then 2 else 3) in Htaken; subst e.
    destruct left; contradiction.
Qed.

Example phi_guard_operation e s l t :
  step phi_machine s l t -> Link.taken phi_link s l t e ->
  guard_ops_consistent phi_ssa phi_values (ValueSem.eval phi_value_sem) s e.
Proof.
  intros Hstep Htaken g ys x k args Hguard Hin Hdef; destruct Hstep;
    [contradiction| |].
  - change (e = if left then 0 else 1) in Htaken; subst e.
    destruct left; cbn in Hguard;
      destruct Hguard as [Heq|Hbad]; try contradiction; inversion Heq; subst g ys;
      destruct Hin as [<-|Hbad]; try contradiction;
      cbn in Hdef; injection Hdef as <- <-;
      exists [phi_one; phi_one], phi_two; split.
    + constructor; [reflexivity|constructor; [reflexivity|constructor]].
    + split; [reflexivity|vm_compute; reflexivity].
    + constructor; [reflexivity|constructor; [reflexivity|constructor]].
    + split; [reflexivity|vm_compute; reflexivity].
  - change (e = if left then 2 else 3) in Htaken; subst e.
    destruct left; contradiction.
Qed.

Example phi_value_origins x c s l t :
  step phi_machine s l t -> SsaLink.val phi_values t x = Some c ->
  SsaLink.val phi_values s x = Some c \/
  (exists k args cs, Ssa.def phi_ssa x = Op k args /\
    Forall2 (fun y d => SsaLink.val phi_values s y = Some d) args cs /\
    ValueSem.eval phi_value_sem k cs = Some c) \/
  (exists e b i z, Ssa.def phi_ssa x = Param b i /\ Link.taken phi_link s l t e /\
    Graph.target (Cfg.graph diamond) e = b /\ nth_error (Ssa.args phi_ssa e) i = Some z /\
    SsaLink.val phi_values s z = Some c) \/ Ssa.def phi_ssa x = Arbitrary.
Proof.
  intros Hstep Hval; destruct Hstep;
    destruct x as [|[|[|[|x]]]]; cbn in Hval; try discriminate;
    injection Hval as <-.
  - left; reflexivity.
  - right; left; exists (App bvadd [Var 0; Var 1]), [0; 0], [phi_one; phi_one].
    split; [reflexivity|split].
    + constructor; [reflexivity|constructor; [reflexivity|constructor]].
    + vm_compute; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - right; right; right; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - right; right; left; exists (if left then 2 else 3), 3, 0, 1.
    split; [reflexivity|split; [reflexivity|]].
    destruct left; repeat split; reflexivity.
Qed.

Example phi_ssa_laws :
  ssa_laws phi_machine phi_ssa phi_values
    (ValueSem.eval phi_value_sem) (ValueSem.holds phi_value_sem).
Proof.
  constructor.
  - exact phi_link_laws.
  - intros [|[|[|x]]] b i Hdef; cbn in Hdef; try discriminate;
      injection Hdef as <- <-; reflexivity.
  - intros e s l t _ Hstep Htaken; eapply phi_guard_holds; eassumption.
  - intros e s l t _ Hstep Htaken; eapply phi_guard_operation; eassumption.
  - intros x c s l t _ Hstep Hval; eapply phi_value_origins; eassumption.
  - intros s [|[|[|[|x]]]] c _ Hval; cbn in Hval; try discriminate;
      vm_compute; tauto.
Qed.

Example phi_entry_ok :
  SparseSound.sparse_entry_ok phi_machine phi_problem phi_values phi_gamma.
Proof.
  intros s [|[|[|[|x]]]] c -> Hval; cbn in Hval; try discriminate;
    injection Hval as <-.
  exists 0, 0; split; [reflexivity|split; [left; reflexivity|]].
  vm_compute; repeat constructor; discriminate.
Qed.

Example numeric_phi_sound_client :
  (forall s, reachable_state phi_machine s ->
    SparseSound.executable (phi_candidate (UBlock (phi_point s))) = true) /\
  (forall s l t e, reachable_state phi_machine s -> step phi_machine s l t ->
    Link.taken phi_link s l t e -> SparseSound.executable (phi_candidate (UEdge e)) = true) /\
  (forall s x c, reachable_state phi_machine s -> SsaLink.val phi_values s x = Some c ->
    gamma (lift_bot_gamma phi_gamma) (phi_candidate (UVal x)) c).
Proof.
  apply (SparseSound.sparse_sound phi_machine phi_problem phi_values
    phi_value_sem phi_gamma 0 phi_candidate).
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact nat_encoding_laws.
  - exact phi_ssa_laws.
  - exact phi_value_laws.
  - exact phi_entry_ok.
  - apply (proj1 (check_post_iff _ _ _) diamond_post_solution_checked).
Qed.

Example numeric_phi_ready_reachable : reachable_state phi_machine PhiReady.
Proof.
  exists PhiStart, []; split; [reflexivity|].
  apply exec_one; constructor.
Qed.

Example numeric_phi_nonempty_operation_and_guard :
  Ssa.def phi_ssa 1 = Op (App bvadd [Var 0; Var 1]) [0; 0] /\
  Ssa.guards phi_ssa 0 = [(Equal phi_two, [1])] /\
  ValueSem.eval phi_value_sem (App bvadd [Var 0; Var 1]) [phi_one; phi_one] =
    Some phi_two /\
  ValueSem.holds phi_value_sem (Equal phi_two) [phi_two].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example numeric_phi_satisfying_guard_witness :
  step phi_machine PhiReady [] (PhiArm true) /\
  Link.taken phi_link PhiReady [] (PhiArm true) 0 /\
  guard_ops_consistent phi_ssa phi_values (ValueSem.eval phi_value_sem) PhiReady 0.
Proof.
  assert (Hbranch : step phi_machine PhiReady [] (PhiArm true)).
  { apply PhiBranch; reflexivity. }
  split; [exact Hbranch|split; [reflexivity|]].
  eapply phi_guard_operation; [exact Hbranch|reflexivity].
Qed.

Example numeric_phi_join_reachable : reachable_state phi_machine PhiDone.
Proof.
  exists PhiStart, []; split; [reflexivity|].
  eapply (exec_step PhiStart [] PhiReady [] PhiDone); [constructor|].
  eapply (exec_step PhiReady [] (PhiArm true) [] PhiDone).
  - apply PhiBranch; reflexivity.
  - apply exec_one; constructor.
Qed.

Example numeric_phi_parameter_two_covered :
  SsaLink.val phi_values PhiDone 2 = Some phi_two /\
  gamma (lift_bot_gamma phi_gamma) (phi_candidate (UVal 2)) phi_two.
Proof.
  split; [reflexivity|].
  apply (proj2 (proj2 numeric_phi_sound_client) PhiDone 2 phi_two
    numeric_phi_join_reachable); reflexivity.
Qed.

Example numeric_phi_infeasible_arm_not_taken s l t :
  reachable_state phi_machine s -> step phi_machine s l t ->
  ~ Link.taken phi_link s l t 1.
Proof.
  intros Hreach Hstep Htaken.
  pose proof (proj1 (proj2 numeric_phi_sound_client) s l t 1 Hreach Hstep Htaken)
    as Hexec.
  discriminate Hexec.
Qed.
