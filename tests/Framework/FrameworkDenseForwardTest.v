(** * Forward counter clients

    A three-state counter crosses one graph edge and then stays at its target.
    For example, the solution records that the counter has left its initial state.
    Builds on: FrameworkDenseForward. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Fixpoint Require Import FixpointSystem.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink ProgramRuns.
From Galois.Framework Require Import FrameworkDense FrameworkDenseForward.
Import List.ListNotations.

Module DenseCounter.

Inductive state :=
  | C0
  | C1
  | C2.

Definition m : semantics state unit :=
  Semantics (fun s => s = C0)
    (fun s l t =>
      match s with
      | C0 => l = [tt] /\ t = C1
      | C1 => l = [] /\ t = C2
      | C2 => False
      end).

Definition point s := match s with C0 => false | _ => true end.

Definition cfg : Cfg.t bool unit :=
  Cfg.Make (Graph.of_pure [false] [false; true]
    (fun n => if n then [] else [tt]) (fun _ => false) (fun _ => true))
    bool_encoding unit_encoding.

Definition lk : Link.t state unit bool unit :=
  Link.Make point (fun s _ _ _ => s = C0) (fun s _ _ => s = C1).

Lemma link_ok : link_laws m (Cfg.graph cfg) lk.
Proof.
  constructor.
  - constructor.
    + constructor; [vm_compute; intuition discriminate|].
      constructor; [vm_compute; tauto|constructor].
    + intros n; destruct n; vm_compute; tauto.
    + intros n []; destruct n; vm_compute; intuition discriminate.
    + intros n []; destruct n; vm_compute; tauto.
  - intros s ->; vm_compute; tauto.
  - intros s l t Hr Hstep; destruct s; cbn in Hstep.
    + right; exists tt; reflexivity.
    + left; reflexivity.
    + contradiction.
  - intros [] s l t Hr Hstep Htaken.
    change (s = C0) in Htaken; subst s.
    change (l = [tt] /\ t = C1) in Hstep; destruct Hstep as [-> ->].
    vm_compute; tauto.
  - intros s l t Hr Hstep Hstay.
    change (s = C1) in Hstay; subst s.
    change (l = [] /\ t = C2) in Hstep; destruct Hstep as [-> ->]; reflexivity.
Qed.

Definition D : Dense.t bool unit bool :=
  Dense.of_pure cfg Forward bool_lattice
    (fun n => if n then None else Some false) (fun _ _ => true).

Definition sigma (n : bool) := n.

Definition G : concretisation bool state :=
  Concretisation bool state (fun a s => a = true \/ s = C0).

Lemma gamma_ok : concretisation_laws bool_lattice G.
Proof.
  constructor; intros [] [] s Hab Hfact; vm_compute in Hab; try discriminate;
    try exact Hfact; left; reflexivity.
Qed.

Lemma covers : DenseForward.boundary_covers D.
Proof.
  intros [] Hin.
  - vm_compute in Hin; intuition discriminate.
  - exists false; reflexivity.
Qed.

Lemma post : post_solution (Dense.lat D) (Dense.system D) sigma.
Proof.
  apply (proj2 (Dense.post_solution_iff D sigma bool_laws)); split.
  - intros [] a Hin Ha; vm_compute in Hin, Ha; try discriminate.
    inversion Ha; reflexivity.
  - intros [] Hin; reflexivity.
Qed.

Lemma initial_fact s a :
  initial m s -> Dense.boundary D (Link.point lk s) = Some a -> gamma G a s.
Proof.
  intros -> Ha; right; reflexivity.
Qed.

Lemma edge_fact e : on_steps m (fun s l s' => Link.taken lk s l s' e ->
  gamma G (sigma (Link.point lk s)) s ->
  gamma G (Dense.transfer D e (sigma (Link.point lk s))) s').
Proof.
  intros s l s' Hr Hstep Htaken Hfact; left; reflexivity.
Qed.

Lemma stay_fact : on_steps m (fun s l s' => Link.stays lk s l s' ->
  gamma G (sigma (Link.point lk s)) s -> gamma G (sigma (Link.point lk s)) s').
Proof.
  intros s l s' Hr Hstep Hstay Hfact.
  change (s = C1) in Hstay; subst s; left; reflexivity.
Qed.

Lemma history : run_edges m lk C0 [tt] C2.
Proof.
  eapply run_take with (s' := C1) (l := [tt]).
  - split; reflexivity.
  - reflexivity.
  - eapply run_stay with (s' := C2) (l := []).
    + split; reflexivity.
    + reflexivity.
    + constructor.
Qed.

Example counter_forward_positive : gamma G (sigma (Link.point lk C2)) C2.
Proof.
  eapply (DenseForward.forward_invariant_sound m D lk (fun _ => G) sigma).
  - reflexivity.
  - exact bool_laws.
  - exact link_ok.
  - exact gamma_ok.
  - exact covers.
  - exact initial_fact.
  - exact edge_fact.
  - exact stay_fact.
  - exact post.
  - eapply DenseForward.history_reachable; [reflexivity|exact history].
Qed.

Example counter_reads_solution : sigma (Link.point lk C2) = true.
Proof.
  destruct counter_forward_positive as [Hflag|Hbad].
  - vm_compute in Hflag; exact Hflag.
  - discriminate.
Qed.

Definition GH : concretisation bool (state * list unit) :=
  Concretisation bool (state * list unit)
    (fun a se => a = true \/ (fst se = C0 /\ snd se = [])).

Example counter_history_positive : gamma GH (sigma (Link.point lk C2)) (C2, [tt]).
Proof.
  eapply (DenseForward.forward_history_sound m D lk (fun _ => GH) sigma).
  - reflexivity.
  - exact bool_laws.
  - exact link_ok.
  - constructor; intros [] [] se Hab Hfact; vm_compute in Hab; try discriminate;
      try exact Hfact; left; reflexivity.
  - exact covers.
  - intros s a -> Ha; right; split; reflexivity.
  - intros e s0 es s l s' Hr Hstep Hs0 Hrun Htaken Hfact; left; reflexivity.
  - intros s0 es s l s' Hr Hstep Hs0 Hrun Hstay Hfact.
    change (s = C1) in Hstay; subst s; left; reflexivity.
  - exact post.
  - reflexivity.
  - exact history.
Qed.

Definition bad : Dense.t bool unit bool :=
  Dense.of_pure cfg Forward bool_lattice
    (fun _ => Some false) (fun _ a => a).

Example bad_transfer_negative :
  post_solution (Dense.lat bad) (Dense.system bad) (fun _ => false) /\
  ~ gamma G false C1 /\
  ~ (forall e, on_steps m (fun s l s' => Link.taken lk s l s' e ->
    gamma G false s -> gamma G (Dense.transfer bad e false) s')).
Proof.
  split.
  - apply (proj2 (Dense.post_solution_iff bad _ bool_laws)); split.
    + intros n a Hn Ha; inversion Ha; reflexivity.
    + intros [] He; reflexivity.
  - split.
    + vm_compute; intros [Hbad|Hbad]; discriminate.
    + intro Hlocal.
      assert (Hr : reachable_state m C0).
      { exists C0, []; split; [reflexivity|constructor]. }
      pose proof (Hlocal tt C0 [tt] C1 Hr (conj eq_refl eq_refl)
        eq_refl (or_intror eq_refl)) as Hbad.
      vm_compute in Hbad; destruct Hbad; discriminate.
Qed.

Example empty_history_boundary : gamma GH (sigma (Link.point lk C0)) (C0, []).
Proof.
  vm_compute; right; split; reflexivity.
Qed.

End DenseCounter.
