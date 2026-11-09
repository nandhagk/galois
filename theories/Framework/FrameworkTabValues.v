(** * Prefix values from symbolic summaries

    A changed-vertex worklist applies balanced jumps and enters unfinished calls.
    For example, a value reaches a callee before any matching return is available.
    Builds on: FrameworkTabulate, FrameworkIde and FixpointCheck. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet BaseIndex BaseCertify.
From Galois.Lattice Require Import LatticeCore LatticeSimple.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointAnalysis FixpointSystem FixpointCheck.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate.
Import List.ListNotations Cost.Notations.

Module TabValues.

(** Value propagation has one symbolic weight per prepared summary or call occurrence. *)
Definition arc N D F := ((Tab.vertex N D * Tab.vertex N D) * F)%type.

Record prepared (N D F : Type) := Prep {
  outgoing : Index.t (Tab.vertex N D) (arc N D F);
  sources : list (Tab.vertex N D);
  inventory : list (Tab.vertex N D)
}.
Arguments Prep {N D F}.
Arguments outgoing {N D F}.
Arguments sources {N D F}.
Arguments inventory {N D F}.

Record state (N D A : Type) := State {
  values : Map.t (Tab.vertex N D) A;
  work : list (Tab.vertex N D);
  pending : FinSet.t (Tab.vertex N D)
}.
Arguments State {N D A}.
Arguments values {N D A}.
Arguments work {N D A}.
Arguments pending {N D A}.

Definition lookup_c {N E P D A F} (I : Ide.t N E P D A F) m v :=
  Map.find_or_c (IdeValue.key_enc I) (bot (Ide.values I)) v m.

Definition lookup {N E P D A F} (I : Ide.t N E P D A F) m v :=
  Cost.value (lookup_c I m v).

(** Missing value bindings denote the actual value lattice bottom. *)
Theorem lookup_equation {N E P D A F} (I : Ide.t N E P D A F) m v :
  lookup I m v = Map.find_or (IdeValue.key_enc I) (bot (Ide.values I)) v m.
Proof.
  reflexivity.
Qed.

(** The transition inventory contains precisely the prepared balanced jumps and call arcs. *)
Definition transitions {N E P D A F} (I : Ide.t N E P D A F) J (start : N * option D) :
    list (arc N D F) :=
  flat_map (fun root => map (fun dst => ((root, dst), Jump.lookup I J (root, dst)))
    (IdeValue.vertices I))
    (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I))) ++
  filter_map (fun a =>
    match Jump.kind a with
    | Icfg.Call _ => Some ((Jump.source a, Jump.target a), Jump.weight a)
    | _ => None
    end) (Jump.arcs I).

(** Transition membership retains the exact prepared summary and actual call occurrences. *)
Theorem transitions_spec {N E P D A F} (I : Ide.t N E P D A F) J start a :
  In a (transitions I J start) <->
    (exists root dst, In root (Cost.value (Jump.roots_c I (fst start) (Jump.arcs I))) /\
      In dst (IdeValue.vertices I) /\ a = ((root, dst), Jump.lookup I J (root, dst))) \/
    (exists call p, In call (Jump.arcs I) /\ Jump.kind call = Icfg.Call p /\
      a = ((Jump.source call, Jump.target call), Jump.weight call)).
Proof.
  unfold transitions; rewrite in_app_iff, in_flat_map, filter_map_spec; split.
  - intros [[root [Hroot Hin]]|[call [Hcall Hvalue]]].
    + apply in_map_iff in Hin; destruct Hin as [dst [Heq Hdst]].
      left; exists root, dst; repeat split; assumption || congruence.
    + destruct (Jump.kind call) as [|p|p] eqn:Hkind; try discriminate.
      right; exists call, p; repeat split; assumption || congruence.
  - intros [[root [dst [Hroot [Hdst Heq]]]]|[call [p [Hcall [Hkind Heq]]]]]; subst a.
    + left; exists root; split; [exact Hroot|apply in_map_iff].
      exists dst; split; [reflexivity|exact Hdst].
    + right; exists call; split; [exact Hcall|rewrite Hkind; reflexivity].
Qed.

Definition prepare_c {N E P D A F} (I : Ide.t N E P D A F) J start :=
  let* as_ := Jump.arcs_c I in
  let* roots := Jump.roots_c I (fst start) as_ in
  let* facts := map_c (fun d => Cost.ret (Some d)) (Ifds.facts (Ide.ifds I)) in
  let* vertices := fw_flat_map_c (fun n =>
    map_c (fun d => Cost.ret (n, d)) (None :: facts))
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I))))) in
  let* summaries := fw_flat_map_c (fun r =>
    map_c (fun v =>
      let* w := Jump.lookup_c I J (r, v) in
      Cost.ret ((r, v), w)) vertices) roots in
  let* calls := filter_map_c (fun a => Cost.ret
    (match Jump.kind a with
    | Icfg.Call _ => Some ((Jump.source a, Jump.target a), Jump.weight a)
    | _ => None
    end)) as_ in
  let* arcs := app_c summaries calls in
  let* out := Index.group_by_c (IdeValue.key_enc I)
    (fun a => Cost.ret (fst (fst a))) arcs in
  let* srcs := map_c (fun a => Cost.ret (fst (fst a))) arcs in
  let* dsts := map_c (fun a => Cost.ret (snd (fst a))) arcs in
  let* keys := app_c srcs dsts in
  Cost.ret (Prep out (start :: srcs) (start :: keys)).

Definition prepare {N E P D A F} (I : Ide.t N E P D A F) J start :=
  Cost.value (prepare_c I J start).

Local Lemma summaries_value {N E P D A F} (I : Ide.t N E P D A F) J roots vs :
  Cost.value (fw_flat_map_c (fun root => map_c (fun dst =>
    let* w := Jump.lookup_c I J (root, dst) in Cost.ret ((root, dst), w)) vs) roots) =
  flat_map (fun root => map (fun dst => ((root, dst), Jump.lookup I J (root, dst))) vs) roots.
Proof.
  rewrite fw_flat_map_value; apply flat_map_ext; intro root.
  rewrite value_map_c; apply map_ext; intro dst; reflexivity.
Qed.

(** Preparation indexes the exact transition inventory and retains every initial source occurrence. *)
Theorem prepare_equation {N E P D A F} (I : Ide.t N E P D A F) J start :
  prepare I J start =
    Prep (Index.group_by (IdeValue.key_enc I) (fun a => fst (fst a))
      (transitions I J start)) (start :: map (fun a => fst (fst a)) (transitions I J start))
      (start :: (map (fun a => fst (fst a)) (transitions I J start) ++
        map (fun a => snd (fst a)) (transitions I J start))).
Proof.
  unfold prepare, prepare_c; rewrite Cost.value_bind; fold (Jump.arcs I).
  remember (Jump.arcs I) as as_.
  rewrite Cost.value_bind.
  remember (Cost.value (Jump.roots_c I (fst start) as_)) as roots.
  rewrite Cost.value_bind, value_map_c, Cost.value_bind.
  assert (Hvertices : Cost.value (fw_flat_map_c (fun n =>
    map_c (fun d => Cost.ret (n, d))
      (None :: map (fun d => Cost.value (Cost.ret (Some d))) (Ifds.facts (Ide.ifds I))))
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))))) = IdeValue.vertices I).
  { rewrite fw_flat_map_value; apply flat_map_ext; intro n.
    rewrite value_map_c; reflexivity. }
  rewrite Hvertices; autorewrite with galois_cost.
  rewrite summaries_value, Index.group_by_c_value.
  subst roots as_; unfold transitions; reflexivity.
Qed.

Definition schedule_c {N E P D A F} (I : Ide.t N E P D A F) v (s : state N D A) :=
  let* queued := FinSet.mem_c (IdeValue.key_enc I) v (pending s) in
  if queued then Cost.ret s else
  let* ps := FinSet.add_c (IdeValue.key_enc I) v (pending s) in
  Cost.ret (State (values s) (v :: work s) ps).

Definition update_c {N E P D A F} (I : Ide.t N E P D A F) v a (s : state N D A) :=
  let* old := lookup_c I (values s) v in
  Cost.step ;;
  let* covered := leb_c (Ide.values I) a old in
  if covered then Cost.ret s else
  Cost.step ;;
  let* joined := join_c (Ide.values I) old a in
  let* m := Map.set_c (IdeValue.key_enc I) v joined (values s) in
  schedule_c I v (State m (work s) (pending s)).

(** Scheduling adds at most one pending vertex and does not change values. *)
Theorem schedule_equation {N E P D A F} (I : Ide.t N E P D A F) v s :
  Cost.value (schedule_c I v s) =
    if FinSet.mem (IdeValue.key_enc I) v (pending s) then s else
      State (values s) (v :: work s) (FinSet.add (IdeValue.key_enc I) v (pending s)).
Proof.
  unfold schedule_c; autorewrite with galois_cost.
  fold (FinSet.mem (IdeValue.key_enc I) v (pending s)).
  destruct (FinSet.mem (IdeValue.key_enc I) v (pending s));
    autorewrite with galois_cost; reflexivity.
Qed.

(** Value updates join and schedule only contributions not covered by the old binding. *)
Theorem update_equation {N E P D A F} (I : Ide.t N E P D A F) v a s :
  Cost.value (update_c I v a s) =
    if leb (Ide.values I) a (lookup I (values s) v) then s else
      Cost.value (schedule_c I v
        (State (Map.set (IdeValue.key_enc I) v
          (join (Ide.values I) (lookup I (values s) v) a) (values s)) (work s) (pending s))).
Proof.
  unfold update_c; autorewrite with galois_cost.
  fold (lookup I (values s) v).
  fold (leb (Ide.values I) a (lookup I (values s) v)).
  destruct (leb (Ide.values I) a (lookup I (values s) v));
    autorewrite with galois_cost; reflexivity.
Qed.

Definition initial_c {N E P D A F} (I : Ide.t N E P D A F)
    (p : prepared N D F) start a0 :=
  let* s := fold_left_c (fun s v => schedule_c I v s) (sources p)
    (State Map.empty [] FinSet.empty) in
  update_c I start a0 s.

Definition arc_c {N E P D A F} (I : Ide.t N E P D A F)
    (a : arc N D F) (s : state N D A) :=
  let* before := lookup_c I (values s) (fst (fst a)) in
  Cost.step ;;
  let* after := Micro.apply_c (Ide.micro I) (snd a) before in
  update_c I (snd (fst a)) after s.

(** A prepared transition applies its captured symbolic weight to the current source value. *)
Theorem arc_equation {N E P D A F} (I : Ide.t N E P D A F) a s :
  Cost.value (arc_c I a s) =
    Cost.value (update_c I (snd (fst a))
      (Micro.apply (Ide.micro I) (snd a) (lookup I (values s) (fst (fst a)))) s).
Proof.
  unfold arc_c; autorewrite with galois_cost; reflexivity.
Qed.

Definition step_c {N E P D A F} (I : Ide.t N E P D A F)
    (p : prepared N D F) (s : state N D A) : Cost.t (state N D A + state N D A) :=
  match work s with
  | [] => Cost.ret (inr s)
  | v :: rest =>
    let* ps := FinSet.remove_c (IdeValue.key_enc I) v (pending s) in
    let s := State (values s) rest ps in
    let* out := Index.find_c (IdeValue.key_enc I) v (outgoing p) in
    let* s := fold_left_c (fun s a => arc_c I a s) out s in
    Cost.ret (inl s)
  end.

(** The raw value phase retains the state when its numeric budget expires. *)
Definition raw_c {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :=
  let* p := prepare_c I J start in
  let* s := initial_c I p start a0 in
  iterate (step_c I p) fuel s.

Definition raw {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :=
  Cost.value (raw_c I J start a0 fuel).

(** Initialization schedules all prepared sources before inserting the actual seed. *)
Theorem initial_equation {N E P D A F} (I : Ide.t N E P D A F) p start a0 :
  Cost.value (initial_c I p start a0) =
    Cost.value (update_c I start a0
      (fold_left (fun s v => Cost.value (schedule_c I v s)) (sources p)
        (State Map.empty [] FinSet.empty))).
Proof.
  unfold initial_c; autorewrite with galois_cost; reflexivity.
Qed.

(** A value step stops only when its changed-vertex worklist is empty. *)
Theorem step_equation {N E P D A F} (I : Ide.t N E P D A F) p s :
  Cost.value (step_c I p s) =
    match work s with
    | [] => inr s
    | v :: rest =>
      inl (fold_left (fun s a => Cost.value (arc_c I a s))
        (Index.find (IdeValue.key_enc I) v (outgoing p))
        (State (values s) rest (FinSet.remove (IdeValue.key_enc I) v (pending s))))
    end.
Proof.
  unfold step_c; destruct (work s); autorewrite with galois_cost; reflexivity.
Qed.

(** The value runner uses its actual prepared transitions and initialized state. *)
Theorem raw_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :
  raw I J start a0 fuel =
    Cost.value (iterate (step_c I (prepare I J start)) fuel
      (Cost.value (initial_c I (prepare I J start) start a0))).
Proof.
  unfold raw, raw_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Value certificates concern the existing public value analysis and the actual map reader. *)
Definition post {N E P D A F} (I : Ide.t N E P D A F) J start a0 m :=
  post_solution (Ide.values I)
    (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0)) (lookup I m).

Inductive outcome {N E P D A F} (I : Ide.t N E P D A F) J start a0 :=
  | Exhausted (s : state N D A)
  | Rejected (s : state N D A)
  | Certified (result : {m : Map.t (Tab.vertex N D) A | post I J start a0 m}).
Arguments Exhausted {N E P D A F I J start a0}.
Arguments Rejected {N E P D A F I J start a0}.
Arguments Certified {N E P D A F I J start a0}.

(** Checker reflection retains the arbitrary cost of the concrete value reader. *)
Theorem checker_sound {N E P D A F} (I : Ide.t N E P D A F) J start a0 m :
  Cost.value (check_post_c (Ide.values I)
    (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0))
    (lookup_c I m)) = true -> post I J start a0 m.
Proof.
  rewrite (check_post_c_spec _ _ _ (lookup I m)) by reflexivity.
  apply check_post_sound.
Qed.

Definition certify_c {N E P D A F} (I : Ide.t N E P D A F) J start a0
    (s : state N D A) : Cost.t (outcome I J start a0) :=
  let analysis := IdeValue.analysis_c I (Jump.lookup_c I J) start a0 in
  Cost.bind analysis (fun _ =>
    let checked := check_post_c (Ide.values I) (Analysis.system (Cost.value analysis))
      (lookup_c I (values s)) in
    Cost.map (fun _ =>
      match certify (fun _ : unit => post I J start a0 (values s))
        (fun _ => Cost.value checked)
        (fun _ H => checker_sound I J start a0 (values s) H) tt with
      | Some certified => Certified (exist _ (values s) (proj2_sig certified))
      | None => Rejected s
      end) checked).

Definition tabulate_values_c {N E P D A F} (I : Ide.t N E P D A F)
    J start a0 fuel :=
  let* result := raw_c I J start a0 fuel in
  match result with
  | inl s => Cost.ret (Exhausted s)
  | inr s => certify_c I J start a0 s
  end.

Definition tabulate_values {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :=
  Cost.value (tabulate_values_c I J start a0 fuel).

(** The wrapper retains exhaustion and checks each actually stopped value map. *)
Theorem outcome_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0 fuel :
  tabulate_values I J start a0 fuel =
    match raw I J start a0 fuel with
    | inl s => Exhausted s
    | inr s => Cost.value (certify_c I J start a0 s)
    end.
Proof.
  unfold tabulate_values, tabulate_values_c; autorewrite with galois_cost.
  fold (raw I J start a0 fuel); destruct (raw I J start a0 fuel); reflexivity.
Qed.

(** Successful value certification retains the reached candidate map unchanged. *)
Theorem certify_candidate {N E P D A F} (I : Ide.t N E P D A F) J start a0 s c :
  Cost.value (certify_c I J start a0 s) = Certified c -> proj1_sig c = values s.
Proof.
  unfold certify_c; autorewrite with galois_cost; cbn zeta.
  match goal with
  | |- context [match ?decision with Some _ => _ | None => _ end] =>
    destruct decision as [certificate|]
  end.
  - intro Heq; injection Heq as Heq; subst c; reflexivity.
  - discriminate.
Qed.

(** Checking a stopped candidate can reject or certify it but cannot invent fuel exhaustion. *)
Theorem certify_not_exhausted {N E P D A F} (I : Ide.t N E P D A F) J start a0 s t :
  Cost.value (certify_c I J start a0 s) <> Exhausted t.
Proof.
  unfold certify_c; autorewrite with galois_cost; cbn zeta.
  match goal with
  | |- context [match ?decision with Some _ => _ | None => _ end] => destruct decision
  end; discriminate.
Qed.

(** An actual value post-solution is accepted by the charged candidate checker. *)
Theorem certify_accepts {N E P D A F} (I : Ide.t N E P D A F) J start a0 s :
  post I J start a0 (values s) ->
  exists c, Cost.value (certify_c I J start a0 s) = Certified c.
Proof.
  intro Hpost.
  assert (Hchecked : Cost.value (check_post_c (Ide.values I)
    (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0))
    (lookup_c I (values s))) = true).
  { rewrite (check_post_c_spec _ _ _ (lookup I (values s))) by reflexivity.
    apply check_post_iff; exact Hpost. }
  unfold certify_c; autorewrite with galois_cost; cbn zeta.
  match goal with
  | |- context [certify ?P ?check ?sound ?w] =>
    assert (Hex : exists certificate, certify P check sound w = Some certificate)
      by (apply (proj2 (certify_some_iff P check sound w)); exact Hchecked);
    destruct Hex as [certificate Hcertificate]; rewrite Hcertificate
  end.
  eexists; reflexivity.
Qed.

(** Certification retains full value-analysis preparation and the actual costed checker queries. *)
Theorem certify_cost_equation {N E P D A F} (I : Ide.t N E P D A F) J start a0 s :
  Cost.ticks (certify_c I J start a0 s) =
    (Cost.ticks (IdeValue.analysis_c I (Jump.lookup_c I J) start a0) +
      Cost.ticks (check_post_c (Ide.values I)
        (Analysis.system (value_analysis I (Jump.lookup_c I J) start a0))
        (lookup_c I (values s))))%N.
Proof.
  unfold certify_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Reachability uses Boolean values so pending-call prefixes have an informative result. *)
Definition reach_micro : Micro.t bool bool :=
  Micro.of_pure true andb andb bool_lattice.

Definition reach_ide {N E P D} (I : Ifds.t N E P D) :=
  Ide.Make I bool_lattice reach_micro (fun _ _ _ => Cost.ret true).

(** The informative IFDS adapter satisfies both application monotonicity laws. *)
Theorem reach_micro_laws : micro_laws bool_lattice reach_micro.
Proof.
  constructor.
  - exact bool_laws.
  - exact bool_lub.
  - intros []; split; reflexivity.
  - intros [] [] []; split; reflexivity.
  - intros [] [] [] Hle; cbn in *; congruence.
  - intros [] [] [] Hle; cbn in *; congruence.
  - intros [] [] [] [] Hf Hg; cbn in *; congruence.
  - intros [] [] []; split; reflexivity.
Qed.

End TabValues.
