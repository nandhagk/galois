(** * Sound environment actions and reachable states

    Concrete action lists describe ordered store changes independently of analysis results.
    For example, havoc permits every replacement and an assumption keeps a satisfying store.
    Builds on: FrameworkEnv, FrameworkDenseForward, DomainsState and DomainsTerm. *)

From Stdlib Require Import List.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkEnv FrameworkDense FrameworkDenseForward.
Import List.ListNotations.

Module EnvSound.

(** Concrete evaluation reuses the generic term evaluator with the supplied state reader. *)
Definition eval_term {S C X K G} (M : ValueSem.t C K G) (get : S -> X -> C)
    (s : S) (t : term K X) : option C :=
  DomainsTerm.eval_term (ValueSem.eval M) (get s) t.

(** Successful concrete evaluation is contained in evaluation of the state's projections. *)
Theorem eval_term_sound {S St A C X K G} (VD : ValueAbs.t A K G)
    (SD : StateAbs.t St A X K G) (M : ValueSem.t C K G) SM gam gs
    (get : S -> X -> C) s a t c :
  value_laws VD M gam -> state_laws SD M SM gam gs ->
  gamma gs a (get s) -> eval_term M get s t = Some c ->
  gamma gam (abs_eval VD (fun x => StateAbs.project SD x a) t) c.
Proof.
  intros HV HS Ha Heval; eapply abs_eval_sound; [exact HV| |exact Heval].
  intro x; exact (project_sound _ _ _ _ _ HS x a (get s) Ha).
Qed.

(** Each concrete action uses the same update dictionary as the state laws. *)
Inductive action_step {C X K G} (M : ValueSem.t C K G) (SM : StateSem.t X C) :
    (X -> C) -> Env.action X K G -> (X -> C) -> Prop :=
  | step_assign : forall st x t c,
      DomainsTerm.eval_term (ValueSem.eval M) st t = Some c ->
      action_step M SM st (Env.Assign x t) (StateSem.update SM x c st)
  | step_havoc : forall st x c,
      action_step M SM st (Env.Havoc x) (StateSem.update SM x c st)
  | step_assume : forall st g ts cs,
      sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) ts) = Some cs ->
      ValueSem.holds M g cs ->
      action_step M SM st (Env.Assume g ts) st.

(** Action lists compose left to right and the empty list leaves the store unchanged. *)
Inductive actions_step {C X K G} (M : ValueSem.t C K G) (SM : StateSem.t X C) :
    (X -> C) -> list (Env.action X K G) -> (X -> C) -> Prop :=
  | steps_nil : forall st, actions_step M SM st [] st
  | steps_cons : forall st a mid acts out,
      action_step M SM st a mid -> actions_step M SM mid acts out ->
      actions_step M SM st (a :: acts) out.

(** Defined assignments retain the updated concrete store. *)
Theorem assign_sound {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs x t a st c :
  state_laws SD M SM gam gs -> gamma gs a st ->
  DomainsTerm.eval_term (ValueSem.eval M) st t = Some c ->
  gamma gs (StateAbs.assign SD x t a) (StateSem.update SM x c st).
Proof.
  intros HS; exact (DomainsState.assign_sound _ _ _ _ _ HS x t a st c).
Qed.

(** Havoc retains every replacement value of the selected variable. *)
Theorem havoc_sound {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs x a st c :
  state_laws SD M SM gam gs -> gamma gs a st ->
  gamma gs (StateAbs.havoc SD x a) (StateSem.update SM x c st).
Proof.
  intros HS; exact (DomainsState.havoc_sound _ _ _ _ _ HS x a st c).
Qed.

(** A guard assumption retains every input store whose defined operands satisfy the guard. *)
Theorem assume_sound {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs g ts a st cs :
  state_laws SD M SM gam gs -> gamma gs a st ->
  sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) ts) = Some cs ->
  ValueSem.holds M g cs -> gamma gs (StateAbs.assume SD g ts a) st.
Proof.
  intros HS; exact (state_assume_sound _ _ _ _ _ HS g ts a st cs).
Qed.

(** One abstract action contains every concrete successor of that action. *)
Theorem action_sound {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs :
  state_laws SD M SM gam gs -> forall st act out a,
  action_step M SM st act out -> gamma gs a st ->
  gamma gs (Env.apply_actions SD [act] a) out.
Proof.
  intros HS st act out a Hstep Ha; rewrite Env.apply_actions_left_fold.
  destruct Hstep as [st x t c Heval|st x c|st g ts cs Heval Hguard];
    cbn [fold_left].
  - eapply assign_sound; eassumption.
  - eapply havoc_sound; eassumption.
  - eapply assume_sound; eassumption.
Qed.

(** Ordered abstract transfer contains every endpoint of the concrete action list. *)
Theorem transfer_sound {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs :
  state_laws SD M SM gam gs -> forall st acts out a,
  actions_step M SM st acts out -> gamma gs a st ->
  gamma gs (Env.apply_actions SD acts a) out.
Proof.
  intros HS st acts out a Hsteps; revert a.
  induction Hsteps as [st|st act mid acts out Hfirst Htail IH]; intros a Ha.
  - rewrite Env.apply_actions_left_fold; exact Ha.
  - rewrite Env.apply_actions_left_fold; cbn [fold_left].
    rewrite <- Env.apply_actions_left_fold; apply IH.
    pose proof (action_sound SD M SM gam gs HS st act mid a Hfirst Ha) as Hmid.
    rewrite Env.apply_actions_left_fold in Hmid; exact Hmid.
Qed.

(** Links describe actual machine steps and initial stores without mentioning a solution.
    Endpoints use equality of store readers because arbitrary state meanings need not
    respect pointwise equality of functions. *)
Record env_laws {S O N E X K G St C} (m : semantics S O)
    (P : Env.t N E X K G) (lk : Link.t S O N E) (get : S -> X -> C)
    (M : ValueSem.t C K G) (SM : StateSem.t X C)
    (gs : concretisation St (X -> C)) (entry : St) : Prop := {
  link_ok : link_laws m (Cfg.graph (Env.cfg P)) lk;
  actions_ok : forall e, on_steps m (fun s l s' =>
    Link.taken lk s l s' e -> actions_step M SM (get s) (Env.actions P e) (get s'));
  stays_ok : on_steps m (fun s l s' => Link.stays lk s l s' -> get s' = get s);
  init_ok : forall s, initial m s -> gamma gs entry (get s)
}.

(** State meanings pulled back along a store reader retain the state order. *)
Definition meaning {S St X C} (gs : concretisation St (X -> C))
    (get : S -> X -> C) : concretisation St S :=
  {| gamma := fun a s => gamma gs a (get s) |}.

(** Pulling back a monotone state meaning gives a monotone machine-state meaning. *)
Theorem meaning_laws {S St X C} (L : lattice St) (gs : concretisation St (X -> C))
    (get : S -> X -> C) :
  concretisation_laws L gs -> concretisation_laws L (meaning gs get).
Proof.
  intros HG; constructor; intros a b s Hab Ha.
  exact (gamma_monotone HG a b (get s) Hab Ha).
Qed.

(** A post-solution of the actual environment generator contains every reachable machine store.
    State laws already include the semantic transfer duties for the chosen value semantics. *)
Theorem sound {S O N E X K G St A C} (m : semantics S O)
    (P : Env.t N E X K G) (SD : StateAbs.t St A X K G)
    (lk : Link.t S O N E) (get : S -> X -> C) (M : ValueSem.t C K G)
    SM gam gs entry sigma :
  encoding_laws (Cfg.edge_enc (Env.cfg P)) ->
  state_laws SD M SM gam gs -> env_laws m P lk get M SM gs entry ->
  post_solution (Analysis.lat (env_analysis P SD entry))
    (Analysis.system (env_analysis P SD entry)) sigma ->
  forall s, reachable_state m s -> gamma gs (sigma (Link.point lk s)) (get s).
Proof.
  intros HE HS [HL HA HT HI] Hpost.
  eapply (DenseForward.forward_invariant_sound m (Env.dense P SD entry) lk
    (fun _ => meaning gs get) sigma).
  - reflexivity.
  - exact (state_lat_ok _ _ _ _ _ HS).
  - exact HL.
  - apply meaning_laws; exact (state_gamma_ok _ _ _ _ _ HS).
  - intros n Hn; exists entry; reflexivity.
  - intros s a Hinit Hboundary.
    change (Some entry = Some a) in Hboundary; injection Hboundary as <-.
    apply HI; exact Hinit.
  - intros e s l s' Hr Hstep Htaken Hfact.
    rewrite Env.dense_transfer by
      (assumption || eapply link_taken_edge; eassumption).
    eapply transfer_sound; [exact HS|eapply HA; eassumption|exact Hfact].
  - intros s l s' Hr Hstep Hstay Hfact.
    change (gamma gs (sigma (Link.point lk s)) (get s')).
    rewrite (HT s l s' Hr Hstep Hstay); exact Hfact.
  - exact Hpost.
Qed.

(** Empty abstract assumption meaning excludes every satisfying concrete input store. *)
Theorem assume_infeasible {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs g ts a :
  state_laws SD M SM gam gs ->
  (forall st, ~ gamma gs (StateAbs.assume SD g ts a) st) ->
  forall st cs, gamma gs a st ->
  sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) ts) = Some cs ->
  ~ ValueSem.holds M g cs.
Proof.
  intros HS Hempty st cs Ha Heval Hguard.
  apply (Hempty st); eapply assume_sound; eassumption.
Qed.

(** Returning state bottom is a sufficient condition for assumption infeasibility. *)
Theorem assume_bottom_infeasible {St A C X K G} (SD : StateAbs.t St A X K G)
    (M : ValueSem.t C K G) SM gam gs g ts a :
  state_laws SD M SM gam gs ->
  StateAbs.assume SD g ts a = bot (StateAbs.lat SD) ->
  forall st cs, gamma gs a st ->
  sequence (map (DomainsTerm.eval_term (ValueSem.eval M) st) ts) = Some cs ->
  ~ ValueSem.holds M g cs.
Proof.
  intros HS Hbot; eapply assume_infeasible; [exact HS|].
  intros st; rewrite Hbot; exact (state_bot_empty _ _ _ _ _ HS st).
Qed.

End EnvSound.
