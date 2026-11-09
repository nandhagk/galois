(** * A checked counter and a lawful coarse control

    A finite interval vocabulary proves every value and state duty of a counter client.
    For example, the loop head contains zero through three and havoc forgets that bound.
    Builds on: FrameworkEnvSound, DomainsTerm, LatticeCore and FixpointCheck. *)

From Stdlib Require Import List Bool ZArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkEnv FrameworkEnvSound.
Import List.ListNotations.
Local Open Scope Z_scope.

Module CounterSound.

Inductive op :=
  | Const (z : Z)
  | Add
  | Lt.

Inductive guard :=
  | Below3
  | Never.

Definition eval k cs :=
  match k, cs with
  | Const z, [] => Some z
  | Add, [x; y] => Some (x + y)
  | Lt, [x; y] => Some (if x <? y then 1 else 0)
  | _, _ => None
  end.

Definition holds g cs :=
  match g, cs with
  | Below3, [z] => z < 3
  | _, _ => False
  end.

Definition M : ValueSem.t Z op guard :=
  {| ValueSem.eval := eval; ValueSem.holds := holds |}.

(** Finite intervals have a distinct empty fact and a full unbounded fact. *)
Inductive fact :=
  | Dead
  | U0
  | U1
  | U2
  | U3
  | Any.

Definition le a b :=
  match a, b with
  | Dead, _ => true
  | _, Any => true
  | U0, U0 | U0, U1 | U0, U2 | U0, U3 => true
  | U1, U1 | U1, U2 | U1, U3 => true
  | U2, U2 | U2, U3 | U3, U3 => true
  | _, _ => false
  end.

Definition join a b := if le a b then b else a.
Definition L := simple le Dead join.

Definition gam : concretisation fact Z :=
  {| gamma := fun a z =>
    match a with
    | Dead => False
    | U0 => z = 0
    | U1 => 0 <= z <= 1
    | U2 => 0 <= z <= 2
    | U3 => 0 <= z <= 3
    | Any => True
    end |}.

(** The finite chain satisfies the real weak lattice laws on all facts. *)
Theorem lattice_ok : lattice_laws L.
Proof.
  apply simple_laws; intros;
    repeat match goal with
    | f : fact |- _ => destruct f
    end; reflexivity || discriminate.
Qed.

(** Enlarging an interval retains every contained integer. *)
Theorem gamma_ok : concretisation_laws L gam.
Proof.
  constructor; intros [] [] z Hle Hz; cbn in Hle, Hz |- *;
    try discriminate; tauto || lia.
Qed.

Definition constant z :=
  if z =? 0 then U0 else
  if z =? 1 then U1 else
  if z =? 2 then U2 else
  if z =? 3 then U3 else Any.

Definition plus a b :=
  match a, b with
  | U0, f | f, U0 => f
  | U1, U1 => U2
  | U1, U2 | U2, U1 => U3
  | _, _ => Any
  end.

Definition forward k fs :=
  match k, fs with
  | Const z, [] => constant z
  | Add, [a; b] => plus a b
  | Lt, _ => U1
  | _, _ => Any
  end.

Definition VD : ValueAbs.t fact op guard :=
  {| ValueAbs.lat := L;
     ValueAbs.top := Any;
     ValueAbs.op_c := fun k fs => Cost.ret (forward k fs);
     ValueAbs.back_c := fun _ _ fs => Cost.ret fs;
     ValueAbs.guard_c := fun _ fs => Cost.ret fs |}.

Lemma constant_sound z : gamma gam (constant z) z.
Proof.
  unfold constant.
  repeat match goal with
  | |- context [Z.eqb z ?n] =>
      destruct (Z.eqb z n) eqn:Hsame;
        [apply Z.eqb_eq in Hsame; subst z; cbn; lia|clear Hsame]
  end.
  exact I.
Qed.

Lemma plus_sound a b x y :
  gamma gam a x -> gamma gam b y -> gamma gam (plus a b) (x + y).
Proof.
  destruct a, b; cbn; intros; tauto || lia.
Qed.

Lemma forward_sound k fs cs c :
  Forall2 (gamma gam) fs cs -> eval k cs = Some c -> gamma gam (forward k fs) c.
Proof.
  intros Hargs Heval; destruct k as [z| |].
  - destruct cs as [|x cs]; [|discriminate].
    inversion Hargs; subst fs; injection Heval as <-; apply constant_sound.
  - destruct cs as [|x [|y [|z cs]]]; try discriminate.
    inversion Hargs as [|a x' rest ys Ha Hrest]; subst.
    inversion Hrest as [|b y' rest' ys' Hb Hnil]; subst.
    inversion Hnil; subst.
    injection Heval as <-; apply plus_sound; assumption.
  - destruct cs as [|x [|y [|z cs]]]; try discriminate.
    injection Heval as <-; change (0 <= (if x <? y then 1 else 0) <= 1).
    destruct (x <? y); lia.
Qed.

(** The value dictionary discharges all transfer, refinement and list-length duties. *)
Theorem value_ok : value_laws VD M gam.
Proof.
  constructor.
  - exact lattice_ok.
  - exact gamma_ok.
  - intros c Hdead; exact Hdead.
  - intros c; exact I.
  - exact forward_sound.
  - intros k a fs cs c Hfs Heval Ha; exact Hfs.
  - intros g fs cs Hfs Hguard; exact Hfs.
  - intros; reflexivity.
  - intros; reflexivity.
Qed.

Definition SM : StateSem.t unit Z :=
  {| StateSem.update := fun _ c _ _ => c |}.

Definition gs : concretisation fact (unit -> Z) :=
  {| gamma := fun a st => gamma gam a (st tt) |}.

Definition refine (precise : bool) g (ts : list (term op unit)) a :=
  match precise, g, ts, a with
  | true, Never, _, _ => Dead
  | true, Below3, [Leaf _], U3 => U2
  | _, _, _, _ => a
  end.

(** The coarse variant keeps every guard input and the precise variant detects Never. *)
Definition SD precise : StateAbs.t fact fact unit op guard :=
  {| StateAbs.lat := L;
     StateAbs.top := Any;
     StateAbs.assign_c := fun _ t a =>
       match a with
       | Dead => Cost.ret Dead
       | _ => abs_eval_c VD (fun _ => Cost.ret a) t
       end;
     StateAbs.havoc_c := fun _ a =>
       Cost.ret (match a with Dead => Dead | _ => Any end);
     StateAbs.assume_c := fun g ts a => Cost.ret (refine precise g ts a);
     StateAbs.project_c := fun _ a => Cost.ret a |}.

Lemma update_ok : StateSem.laws SM.
Proof.
  constructor.
  - intros [] c st; reflexivity.
  - intros [] [] c st Hneq; exfalso; apply Hneq; reflexivity.
Qed.

Lemma state_assign_ok precise x t a st c :
  gamma gs a st -> DomainsTerm.eval_term (ValueSem.eval M) st t = Some c ->
  gamma gs (StateAbs.assign (SD precise) x t a) (StateSem.update SM x c st).
Proof.
  intros Ha Heval.
  assert (Henv : forall x : unit, gamma gam a (st x)).
  { intros []; exact Ha. }
  pose proof (abs_eval_sound VD M gam value_ok (fun _ : unit => a) st t c
    Henv Heval) as Hterm.
  destruct a; [contradiction|..]; exact Hterm.
Qed.

Lemma state_assume_ok precise g ts a st cs :
  gamma gs a st ->
  sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) ts) = Some cs ->
  ValueSem.holds M g cs -> gamma gs (StateAbs.assume (SD precise) g ts a) st.
Proof.
  intros Ha Heval Hg; destruct precise; [|exact Ha]; destruct g.
  - destruct ts as [|t ts]; [exact Ha|].
    destruct t as [[]|k children]; [|exact Ha].
    destruct ts as [|t ts]; [|exact Ha].
    cbn [map] in Heval; rewrite eval_term_leaf in Heval; cbn [sequence] in Heval.
    injection Heval as <-.
    change (st tt < 3) in Hg.
    destruct a; cbn in Ha |- *; tauto || lia.
  - change (holds Never cs) in Hg; unfold holds in Hg.
    destruct cs; contradiction.
Qed.

(** Both state dictionaries satisfy every landed state-law clause for arbitrary terms and stores. *)
Theorem state_ok precise : state_laws (SD precise) M SM gam gs.
Proof.
  constructor.
  - exact lattice_ok.
  - constructor; intros a b st Hab Ha; exact (gamma_monotone gamma_ok a b (st tt) Hab Ha).
  - intros st Hdead; exact Hdead.
  - intros st; exact I.
  - exact update_ok.
  - exact (state_assign_ok precise).
  - intros x a st c Ha; destruct a; cbn in Ha |- *; tauto.
  - exact (state_assume_ok precise).
  - intros [] a st Ha; exact Ha.
Qed.

(** The tutorial-sized counter starts here. *)
Definition cfg : Cfg.t bool bool :=
  Cfg.Make (Graph.of_pure [false] [false; true]
    (fun n => [n]) (fun e => e) (fun _ => true)) bool_encoding bool_encoding.

Definition actions (e : bool) : list (Env.action unit op guard) :=
  if e then
    [Env.Assume Below3 [Leaf tt];
     Env.Assign tt (Node Add [Leaf tt; Node (Const 1) []])]
  else [Env.Assign tt (Node (Const 0) [])].

Definition P : Env.t bool bool unit op guard :=
  Env.Make cfg unit_encoding (fun e => Cost.ret (actions e)).

Definition state := (bool * (unit -> Z))%type.

Inductive step : state -> list bool -> state -> Prop :=
  | start : forall st,
      step (false, st) [false] (true, StateSem.update SM tt 0 st)
  | increment : forall st, st tt < 3 ->
      step (true, st) [true] (true, StateSem.update SM tt (st tt + 1) st)
  | stay : forall s, step s [] s.

Definition machine : semantics state bool :=
  Semantics (fun s => fst s = false) step.

Definition lk : Link.t state bool bool bool :=
  Link.Make fst (fun _ l _ e => l = [e]) (fun _ l _ => l = []).

Lemma link_ok : link_laws machine (Cfg.graph cfg) lk.
Proof.
  constructor.
  - constructor.
    + constructor; [vm_compute; intuition discriminate|].
      constructor; [vm_compute; tauto|constructor].
    + intros []; vm_compute; tauto.
    + intros [] [] Hin; vm_compute in Hin |- *; intuition discriminate.
    + intros [] [] Hin; vm_compute in Hin |- *; intuition discriminate.
  - intros [n st] Hinit; change (n = false) in Hinit; subst n; left; reflexivity.
  - intros s l s' Hr Hstep; destruct Hstep.
    + right; exists false; reflexivity.
    + right; exists true; reflexivity.
    + left; reflexivity.
  - intros e s l s' Hr Hstep Htaken.
    change (l = [e]) in Htaken; destruct Hstep;
      inversion Htaken; subst e; vm_compute; tauto.
  - intros s l s' Hr Hstep Hstay.
    change (l = []) in Hstay; destruct Hstep; try discriminate; reflexivity.
Qed.

Lemma actions_ok e : on_steps machine (fun s l s' => Link.taken lk s l s' e ->
  EnvSound.actions_step M SM (snd s) (Env.actions P e) (snd s')).
Proof.
  intros s l s' Hr Hstep Htaken; change (l = [e]) in Htaken.
  destruct Hstep as [st|st Hbound|s]; inversion Htaken; subst e.
  - change (EnvSound.actions_step M SM st (actions false)
      (StateSem.update SM tt 0 st)).
    econstructor; [eapply EnvSound.step_assign; reflexivity|constructor].
  - change (EnvSound.actions_step M SM st (actions true)
      (StateSem.update SM tt (st tt + 1) st)).
    econstructor.
    + eapply EnvSound.step_assume with (cs := [st tt]); [reflexivity|exact Hbound].
    + econstructor; [eapply EnvSound.step_assign; reflexivity|constructor].
Qed.

Lemma env_ok : EnvSound.env_laws machine P lk snd M SM gs Any.
Proof.
  constructor.
  - exact link_ok.
  - exact actions_ok.
  - intros s l s' Hr Hstep Hstay.
    change (l = []) in Hstay; destruct Hstep; try discriminate; reflexivity.
  - intros s Hinitial; exact I.
Qed.

Definition analysis := env_analysis P (SD true) Any.
Definition sigma (n : bool) := if n then U3 else Any.

Example hand_candidate_accepted :
  check_post (Analysis.lat analysis) (Analysis.system analysis) sigma = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example too_small_candidate_rejected :
  check_post (Analysis.lat analysis) (Analysis.system analysis)
    (fun n => if n then U2 else Any) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Lemma candidate_post :
  post_solution (Analysis.lat analysis) (Analysis.system analysis) sigma.
Proof.
  apply check_post_sound; exact hand_candidate_accepted.
Qed.

Example reachable_loop_head s :
  reachable_state machine s -> Link.point lk s = true -> 0 <= snd s tt <= 3.
Proof.
  intros Hr Hhead.
  pose proof (EnvSound.sound machine P (SD true) lk snd M SM gam gs Any sigma
    bool_encoding_laws (state_ok true) env_ok candidate_post s Hr) as Hfact.
  rewrite Hhead in Hfact; exact Hfact.
Qed.

(** The tutorial-sized counter ends here. *)

Example head_three_reachable :
  reachable_state machine (true, fun _ => 3).
Proof.
  exists (false, fun _ => 99), [false; true; true; true]; split; [reflexivity|].
  eapply exec_step with (s' := (true, fun _ => 0)) (l := [false]); [constructor|].
  eapply exec_step with (s' := (true, fun _ => 1)) (l := [true]).
  - apply increment; cbn; lia.
  - eapply exec_step with (s' := (true, fun _ => 2)) (l := [true]).
    + apply increment; cbn; lia.
    + eapply exec_step with (s' := (true, fun _ => 3)) (l := [true]).
      * apply increment; cbn; lia.
      * constructor.
Qed.

Example nested_term_sound :
  gamma gam (abs_eval VD (fun _ : unit => U2)
    (Node Add [Leaf tt; Node (Const 1) []])) 3.
Proof.
  eapply (EnvSound.eval_term_sound VD (SD true) M SM gam gs
    (fun z : Z => fun _ : unit => z) 2 U2).
  - exact value_ok.
  - exact (state_ok true).
  - cbn; lia.
  - reflexivity.
Qed.

Example undefined_term :
  EnvSound.eval_term M (fun z : Z => fun _ : unit => z) 2 (Node Add []) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example havoc_vs_assign :
  (Env.apply_actions (SD true) [Env.Assign tt (Node (Const 0) [])] U3,
   Env.apply_actions (SD true) [Env.Havoc tt] U3) = (U0, Any).
Proof.
  vm_compute; reflexivity.
Qed.

Example havoc_does_not_keep_assignment_bound :
  le (Env.apply_actions (SD true) [Env.Havoc tt] U3) U0 = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example havoc_accepts_an_outside_value :
  EnvSound.actions_step M SM (fun _ => 0) [Env.Havoc tt] (fun _ => -7).
Proof.
  econstructor; [constructor|constructor].
Qed.

Example havoc_sound_for_an_outside_value :
  gamma gs (Env.apply_actions (SD true) [Env.Havoc tt] U0) (fun _ => -7).
Proof.
  eapply (EnvSound.transfer_sound (SD true) M SM gam gs (state_ok true)).
  - exact havoc_accepts_an_outside_value.
  - reflexivity.
Qed.

Example assignment_excludes_an_outside_value :
  ~ gamma gs (Env.apply_actions (SD true) [Env.Assign tt (Node (Const 0) [])] U3)
    (fun _ => -7).
Proof.
  vm_compute; discriminate.
Qed.

Example empty_actions :
  Env.apply_actions (SD true) [] U3 = U3.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_concrete_actions (st : unit -> Z) :
  EnvSound.actions_step M SM st [] st.
Proof.
  constructor.
Qed.

Example empty_operand_node :
  EnvSound.eval_term M (fun st : unit -> Z => st) (fun _ => 99)
    (Node (Const 2) []) = Some 2.
Proof.
  vm_compute; reflexivity.
Qed.

Example precise_impossible_guard_bottom :
  StateAbs.assume (SD true) Never [Leaf tt] U3 = Dead.
Proof.
  vm_compute; reflexivity.
Qed.

Example precise_impossible_guard_infeasible st cs :
  gamma gs U3 st ->
  sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) [Leaf tt]) = Some cs ->
  ~ ValueSem.holds M Never cs.
Proof.
  eapply (EnvSound.assume_bottom_infeasible (SD true) M SM gam gs);
    [exact (state_ok true)|reflexivity].
Qed.

Example coarse_impossible_guard_nonbottom :
  StateAbs.assume (SD false) Never [Leaf tt] U3 <> bot (StateAbs.lat (SD false)).
Proof.
  vm_compute; discriminate.
Qed.

Example coarse_impossible_guard_has_no_store :
  ~ exists st cs,
    sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) [Leaf tt]) = Some cs /\
    ValueSem.holds M Never cs.
Proof.
  intros [st [cs [Heval Hg]]]; destruct cs; exact Hg.
Qed.

Example coarse_impossible_result_is_inhabited :
  gamma gs (StateAbs.assume (SD false) Never [Leaf tt] U3) (fun _ => 1).
Proof.
  cbn; lia.
Qed.

End CounterSound.
