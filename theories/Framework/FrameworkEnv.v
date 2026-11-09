(** * Ordered state-domain actions

    The environment generator delegates assignments, havoc and guards to StateAbs.
    For example, an assignment followed by a guard observes the assigned state.
    Builds on: FrameworkDense and DomainsState. *)

From Stdlib Require Import List.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Domains Require Import DomainsTerm DomainsState.
From Galois.Fixpoint Require Import FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkDense.
Import List.ListNotations Cost.Notations.

Module Env.

(** Actions preserve source order, including repeated writes to the same variable. *)
Inductive action (X K G : Type) :=
  | Assign (x : X) (e : term K X)
  | Havoc (x : X)
  | Assume (g : G) (ts : list (term K X)).
Arguments Assign {X K G}.
Arguments Havoc {X K G}.
Arguments Assume {X K G}.

(** An action presentation contains syntax readers and encodings without semantic fields. *)
Record t (N E X K G : Type) := Make {
  cfg : Cfg.t N E;
  var_enc : encoding X;
  actions_c : E -> Cost.t (list (action X K G))
}.
Arguments Make {N E X K G}.
Arguments cfg {N E X K G}.
Arguments var_enc {N E X K G}.
Arguments actions_c {N E X K G}.

Definition actions {N E X K G} (P : t N E X K G) e := Cost.value (actions_c P e).

Definition one_c {St A X K G} (D : StateAbs.t St A X K G) s a :=
  Cost.step ;;
  match a with
  | Assign x e => StateAbs.assign_c D x e s
  | Havoc x => StateAbs.havoc_c D x s
  | Assume g ts => StateAbs.assume_c D g ts s
  end.

(** Action application is a charged left fold over changing abstract states. *)
Definition apply_actions_c {St A X K G} (D : StateAbs.t St A X K G) xs s :=
  fold_left_c (one_c D) xs s.

Definition apply_actions {St A X K G} (D : StateAbs.t St A X K G) xs s :=
  Cost.value (apply_actions_c D xs s).

(** The pure action result is the left fold of the StateAbs observations. *)
Theorem apply_actions_left_fold {St A X K G} (D : StateAbs.t St A X K G) xs s :
  apply_actions D xs s =
    fold_left (fun s a => match a with
      | Assign x e => StateAbs.assign D x e s
      | Havoc x => StateAbs.havoc D x s
      | Assume g ts => StateAbs.assume D g ts s
      end) xs s.
Proof.
  unfold apply_actions, apply_actions_c; rewrite value_fold_left_c.
  revert s; induction xs as [|a xs IH]; intro s; cbn [fold_left].
  - reflexivity.
  - destruct a; apply IH.
Qed.

(** Action lists are prepared once per listed edge. *)
Definition prepare_c {N E X K G} (P : t N E X K G) :=
  let* es := fw_edges_c (cfg P) in
  let* rows := map_c (fun e =>
    Cost.step ;; Cost.map (fun xs => (e, xs)) (actions_c P e)) es in
  Map.of_list_c (Cfg.edge_enc (cfg P)) rows.

Definition dense {N E X K G St A} (P : t N E X K G)
    (D : StateAbs.t St A X K G) (entry : St) :=
  let table := Cost.value (prepare_c P) in
  Dense.Make (cfg P) Forward (StateAbs.lat D)
    (fun _ => Cost.ret (Some entry))
    (fun e s =>
      let* xs := Map.find_or_c (Cfg.edge_enc (cfg P)) [] e table in
      apply_actions_c D xs s).

(** Prepared actions retain the original ordered lists for every edge occurrence. *)
Theorem prepare_equation {N E X K G} (P : t N E X K G) :
  Cost.value (prepare_c P) = Map.of_list (Cfg.edge_enc (cfg P))
    (map (fun e => (e, actions P e)) (Cfg.edges (cfg P))).
Proof.
  unfold prepare_c; rewrite !Cost.value_bind, fw_edges_value, value_map_c.
  reflexivity.
Qed.

Local Lemma actions_lookup {N E X K G} (P : t N E X K G) e :
  encoding_laws (Cfg.edge_enc (cfg P)) -> In e (Cfg.edges (cfg P)) ->
  Map.get (Cfg.edge_enc (cfg P)) e (Cost.value (prepare_c P)) = Some (actions P e).
Proof.
  intros HE Hin; rewrite prepare_equation, Map.of_list_get.
  assert (Hfold : forall es old, old = Some (actions P e) \/ In e es ->
    fold_left (fun old kv =>
      if eqb (Cfg.edge_enc (cfg P)) e (fst kv) then Some (snd kv) else old)
      (map (fun k => (k, actions P k)) es) old = Some (actions P e)).
  { induction es as [|k es IH]; intros old Hhit; cbn [map fold_left fst snd].
    - destruct Hhit as [->|[]]; reflexivity.
    - destruct (eqb (Cfg.edge_enc (cfg P)) e k) eqn:Hsame.
      + apply (eqb_true_iff _ HE) in Hsame; subst k.
        apply IH; left; reflexivity.
      + apply IH; destruct Hhit as [Hhit|[Hequal|Hhit]].
        * left; exact Hhit.
        * subst k; rewrite eqb_refl in Hsame; discriminate.
        * right; exact Hhit. }
  apply Hfold; right; exact Hin.
Qed.

(** A listed edge transfers its source action list without a default-cache approximation. *)
Theorem dense_transfer {N E X K G St A} (P : t N E X K G)
    (D : StateAbs.t St A X K G) entry e s :
  encoding_laws (Cfg.edge_enc (cfg P)) -> In e (Cfg.edges (cfg P)) ->
  Dense.transfer (dense P D entry) e s = apply_actions D (actions P e) s.
Proof.
  intros HE Hin; unfold dense, Dense.transfer; cbn [Dense.transfer_c].
  rewrite Cost.value_bind.
  change (apply_actions D
    (Map.find_or (Cfg.edge_enc (cfg P)) [] e (Cost.value (prepare_c P))) s =
    apply_actions D (actions P e) s).
  rewrite Map.find_or_equation, (actions_lookup P e HE Hin); reflexivity.
Qed.

(** Entry states and ordered actions generate ordinary dense constraints. *)
Definition analysis {N E X K G St A} (P : t N E X K G)
    (D : StateAbs.t St A X K G) (entry : St) (policy : Policy.t N) :=
  Dense.analysis (dense P D entry) policy.

(** State-analysis laws reuse dense coverage and the supplied state lattice laws. *)
Theorem analysis_laws {N E X K G St A} (P : t N E X K G)
    (D : StateAbs.t St A X K G) entry policy :
  encoding_laws (Cfg.node_enc (cfg P)) -> encoding_laws (Cfg.edge_enc (cfg P)) ->
  lattice_laws (StateAbs.lat D) -> Analysis.laws (analysis P D entry policy).
Proof.
  intros HN HE HL; apply Dense.analysis_laws; assumption.
Qed.

End Env.

(** The default environment policy orders nodes by code and requests joining. *)
Definition env_analysis {N E X K G St A} (P : Env.t N E X K G)
    (D : StateAbs.t St A X K G) (entry : St) :=
  Env.analysis P D entry (Policy.by_code (Cfg.node_enc (Env.cfg P))).
