(** * Jump certificates and IDE value constraints

    Jump certificates bound balanced path functions and the value phase follows valid prefixes.
    For example, a call and its matching return compose through the callee's jump summary.
    Builds on: FrameworkIfds, FrameworkRows and FixpointCheck. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkRows FrameworkMicro FrameworkIfds.
Import List.ListNotations Cost.Notations.

(** A jump key retains entry point/fact and destination point/fact. *)
Definition jkey N D := ((N * option D) * (N * option D))%type.

Definition vertex_enc {N D} (EN : encoding N) (ED : encoding D) :=
  FrameworkKey.pair EN (FrameworkKey.option ED).

Definition jkey_enc {N D} (EN : encoding N) (ED : encoding D) :=
  FrameworkKey.pair (vertex_enc EN ED) (vertex_enc EN ED).

(** Jump keys are injective independently of the micro-function algebra. *)
Theorem jkey_enc_laws {N D} (EN : encoding N) (ED : encoding D) :
  encoding_laws EN -> encoding_laws ED -> encoding_laws (jkey_enc EN ED).
Proof.
  intros HN HD; repeat apply FrameworkKey.pair_laws;
    try apply FrameworkKey.option_laws; assumption.
Qed.

Module Jump.

(** Exploded arcs retain their edge occurrence, stack kind and symbolic weight. *)
Record arc (N E P D F : Type) := Arc {
  edge : E;
  source : N * option D;
  target : N * option D;
  kind : Icfg.kind P;
  weight : F
}.
Arguments Arc {N E P D F}.
Arguments edge {N E P D F}.
Arguments source {N E P D F}.
Arguments target {N E P D F}.
Arguments kind {N E P D F}.
Arguments weight {N E P D F}.

Definition fact_domain {N E P D} (I : Ifds.t N E P D) :=
  None :: map (@Some D) (Ifds.facts I).

(** Exploded preparation calls each flow once per listed input fact and edge occurrence. *)
Definition arcs_c {N E P D A F} (I : Ide.t N E P D A F) :=
  let ip := Ide.ifds I in
  let cfg := Icfg.cfg (Ifds.icfg ip) in
  let* es := fw_edges_c cfg in
  let* facts := map_c (fun d => Cost.ret (Some d)) (Ifds.facts ip) in
  fw_flat_map_c (fun e =>
    Cost.step ;;
    let* src := Graph.source_c (Cfg.graph cfg) e in
    Cost.step ;;
    let* dst := Graph.target_c (Cfg.graph cfg) e in
    Cost.step ;;
    let* kind := Icfg.kind_c (Ifds.icfg ip) e in
    fw_flat_map_c (fun d =>
      Cost.step ;;
      let* outs := Ifds.flow_c ip e d in
      map_c (fun d' =>
        Cost.step ;;
        let* w := Ide.weight_c I e d d' in
        Cost.ret (Arc e (src, d) (dst, d') kind w)) outs) (None :: facts)) es.

Definition arcs {N E P D A F} (I : Ide.t N E P D A F) := Cost.value (arcs_c I).

(** Roots are start facts followed by call-target facts, retaining occurrences. *)
Definition roots_c {N E P D A F} (I : Ide.t N E P D A F)
    (start : N) (as_ : list (arc N E P D F)) :=
  let* facts := map_c (fun d => Cost.ret (Some d)) (Ifds.facts (Ide.ifds I)) in
  let* initial := map_c (fun d => Cost.ret (start, d)) (None :: facts) in
  let* callees := filter_map_c (fun a =>
    Cost.ret (match kind a with Icfg.Call _ => Some (target a) | _ => None end)) as_ in
  app_c initial callees.

(** Rules distinguish path edges, call entry identities and matched return summaries. *)
Inductive row (N E P D F : Type) :=
  | Seed (root : N * option D)
  | Call (a : arc N E P D F)
  | Path (root : N * option D) (a : arc N E P D F)
  | Return (root : N * option D) (call ret : arc N E P D F).
Arguments Seed {N E P D F}.
Arguments Call {N E P D F}.
Arguments Path {N E P D F}.
Arguments Return {N E P D F}.

Definition matches_c {N E P D F} (EP : encoding P)
    (a b : arc N E P D F) :=
  match kind a, kind b with
  | Icfg.Call p, Icfg.Return q => eqb_c EP p q
  | _, _ => Cost.ret false
  end.

(** Ground row preparation enumerates facts and arcs, never A or F. *)
Definition rows_c {N E P D A F} (I : Ide.t N E P D A F) start :=
  let* as_ := arcs_c I in
  let* roots := roots_c I start as_ in
  let* facts := map_c (fun d => Cost.ret (Some d)) (Ifds.facts (Ide.ifds I)) in
  let* seeds := map_c (fun d => Cost.ret (Seed (start, d)))
    (None :: facts) in
  let* calls := filter_map_c (fun a =>
    Cost.ret (match kind a with Icfg.Call _ => Some (Call a) | _ => None end)) as_ in
  let* paths := fw_flat_map_c (fun root =>
    filter_map_c (fun a =>
      Cost.ret (match kind a with Icfg.Internal => Some (Path root a) | _ => None end)) as_)
    roots in
  let* returns := fw_flat_map_c (fun root =>
    fw_flat_map_c (fun a =>
      filter_map_c (fun b =>
        let* yes := matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b in
        Cost.ret (if yes then Some (Return root a b) else None)) as_) as_) roots in
  let* tail := app_c paths returns in
  let* tail := app_c calls tail in
  app_c seeds tail.

Definition rows {N E P D A F} (I : Ide.t N E P D A F) start :=
  Cost.value (rows_c I start).

Definition output {N E P D F} (r : row N E P D F) : jkey N D :=
  match r with
  | Seed root => (root, root)
  | Call a => (target a, target a)
  | Path root a => (root, target a)
  | Return root _ b => (root, target b)
  end.

Definition rhs_c {N E P D A F} (I : Ide.t N E P D A F)
    (look : jkey N D -> Cost.t F) (r : row N E P D F) :=
  let M := Ide.micro I in
  match r with
  | Seed _ | Call _ => Cost.ret (Micro.id M)
  | Path root a =>
    Cost.step ;;
    let* before := look (root, source a) in
    Cost.step ;; Micro.compose_c M (weight a) before
  | Return root a b =>
    Cost.step ;;
    let* before := look (root, source a) in
    Cost.step ;;
    let* inside := look (target a, source b) in
    Cost.step ;;
    let* pushed := Micro.compose_c M (weight a) before in
    Cost.step ;;
    let* body := Micro.compose_c M inside pushed in
    Cost.step ;; Micro.compose_c M (weight b) body
  end.

(** Declarative row meaning states the algebraic path and matched-return inequalities. *)
Definition holds {N E P D A F} (I : Ide.t N E P D A F)
    (J : jkey N D -> F) (r : row N E P D F) :=
  let M := Ide.micro I in
  leb (Micro.lat M)
    (match r with
    | Seed _ | Call _ => Micro.id M
    | Path root a => Micro.compose M (weight a) (J (root, source a))
    | Return root a b => Micro.compose M (weight b)
        (Micro.compose M (J (target a, source b))
          (Micro.compose M (weight a) (J (root, source a))))
    end) (J (output r)) = true.

(** Charged row evaluation agrees with the algebraic row specification. *)
Theorem rhs_spec {N E P D A F} (I : Ide.t N E P D A F) look J r :
  (forall k, Cost.value (look k) = J k) ->
  leb (Micro.lat (Ide.micro I)) (Cost.value (rhs_c I look r)) (J (output r)) = true <->
    holds I J r.
Proof.
  intro Hlook; destruct r; unfold rhs_c, holds;
    autorewrite with galois_cost; rewrite ?Hlook; reflexivity.
Qed.

Definition enc {N E P D A F} (I : Ide.t N E P D A F) :=
  jkey_enc (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
    (Ifds.fact_enc (Ide.ifds I)).

Definition lookup_c {N E P D A F} (I : Ide.t N E P D A F) (J : Map.t positive F) k :=
  Cost.step ;;
  let* code := encode_c (enc I) k in
  Map.find_or_c positive_encoding (bot (Micro.lat (Ide.micro I))) code J.

Definition lookup {N E P D A F} (I : Ide.t N E P D A F) J k :=
  Cost.value (lookup_c I J k).

End Jump.

(** A jump post-solution bounds every seed, path, call-entry and matched-return row. *)
Definition jump_post {N E P D A F} (I : Ide.t N E P D A F) start J : Prop :=
  forall r, In r (Jump.rows I start) -> Jump.holds I J r.

Definition check_jumps_c {N E P D A F} (I : Ide.t N E P D A F) start J :=
  let* rows := Jump.rows_c I start in
  forallb_c (fun r =>
    let* value := Jump.rhs_c I (Jump.lookup_c I J) r in
    let* bound := Jump.lookup_c I J (Jump.output r) in
    Cost.step ;; leb_c (Micro.lat (Ide.micro I)) value bound) rows.

Definition check_jumps {N E P D A F} (I : Ide.t N E P D A F) start J :=
  Cost.value (check_jumps_c I start J).

(** The checker accepts exactly the declared jump inequalities without any algebra laws. *)
Theorem check_jumps_iff {N E P D A F} (I : Ide.t N E P D A F) start J :
  check_jumps I start J = true <-> jump_post I start (Jump.lookup I J).
Proof.
  unfold check_jumps, check_jumps_c; rewrite Cost.value_bind, value_forallb_c.
  rewrite forallb_forall; unfold jump_post, Jump.rows.
  split; intros H r Hr; specialize (H r Hr).
  - apply (proj1 (Jump.rhs_spec I (Jump.lookup_c I J) (Jump.lookup I J) r
      (fun _ => eq_refl))).
    exact H.
  - apply (proj2 (Jump.rhs_spec I (Jump.lookup_c I J) (Jump.lookup I J) r
      (fun _ => eq_refl))) in H.
    exact H.
Qed.

(** Every accepted positive-key map denotes a jump post-solution. *)
Theorem check_jumps_sound {N E P D A F} (I : Ide.t N E P D A F) start J :
  check_jumps I start J = true -> jump_post I start (Jump.lookup I J).
Proof.
  apply check_jumps_iff.
Qed.

(** Value rows seed the start, apply balanced summaries and enter calls. *)
Inductive vrow (N E D : Type) :=
  | VSeed
  | VJump (from into : N * option D)
  | VCall (e : E) (from into : option D).
Arguments VSeed {N E D}.
Arguments VJump {N E D}.
Arguments VCall {N E D}.

Module IdeValue.

Definition row_key {N E D} (r : vrow N E D) :
    unit + (((N * option D) * (N * option D)) + (E * (option D * option D))) :=
  match r with
  | VSeed => inl tt
  | VJump from into => inr (inl (from, into))
  | VCall e from into => inr (inr (e, (from, into)))
  end.

Definition row_enc {N E P D A F} (I : Ide.t N E P D A F) :=
  encoding_comap (fun r => Cost.ret (row_key r))
    (FrameworkKey.sum unit_encoding (FrameworkKey.sum (Jump.enc I)
      (FrameworkKey.pair (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
        (FrameworkKey.pair (FrameworkKey.option (Ifds.fact_enc (Ide.ifds I)))
          (FrameworkKey.option (Ifds.fact_enc (Ide.ifds I))))))).

Definition key_enc {N E P D A F} (I : Ide.t N E P D A F) :=
  vertex_enc (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
    (Ifds.fact_enc (Ide.ifds I)).

(** Value-row encodings distinguish seed, jump and exploded call occurrences. *)
Theorem row_enc_laws {N E P D A F} (I : Ide.t N E P D A F) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) -> encoding_laws (row_enc I).
Proof.
  intros HN HE HD; apply encoding_comap_laws.
  - intros [|a b|e d d'] [|a' b'|e' c c'] Hcode;
      rewrite !Cost.value_ret in Hcode; cbn [row_key] in Hcode; congruence.
  - apply FrameworkKey.sum_laws; [apply unit_encoding_laws|].
    apply FrameworkKey.sum_laws.
    + apply jkey_enc_laws; assumption.
    + repeat apply FrameworkKey.pair_laws;
        try apply FrameworkKey.option_laws; assumption.
Qed.

Definition prepare_c {N E P D A F} (I : Ide.t N E P D A F)
    (jump_c : jkey N D -> Cost.t F) (start : N * option D) a0 :=
  let* as_ := Jump.arcs_c I in
  let* roots := Jump.roots_c I (fst start) as_ in
  let* facts := map_c (fun d => Cost.ret (Some d)) (Ifds.facts (Ide.ifds I)) in
  let* vertices := fw_flat_map_c (fun n =>
    map_c (fun d => Cost.ret (n, d)) (None :: facts))
    (Graph.nodes (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I))))) in
  let* summaries := fw_flat_map_c (fun root =>
    map_c (fun dst =>
      Cost.step ;;
      let* weight := jump_c (root, dst) in
      Cost.ret (VJump root dst, Rows.Make dst [root] (fun fs =>
        match fs with
        | a :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) weight a
        | [] => Cost.ret (bot (Ide.values I))
        end))) vertices) roots in
  let* calls := filter_map_c (fun a =>
    Cost.ret (match Jump.kind a with
    | Icfg.Call _ => Some
        (VCall (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)),
        Rows.Make (Jump.target a) [Jump.source a] (fun fs =>
          match fs with
          | value :: _ => Cost.step ;; Micro.apply_c (Ide.micro I) (Jump.weight a) value
          | [] => Cost.ret (bot (Ide.values I))
          end))
    | _ => None
    end)) as_ in
  let* tail := app_c summaries calls in
  Cost.ret ((VSeed, Rows.Make start [] (fun _ => Cost.ret a0)) :: tail).

Definition analysis_c {N E P D A F} (I : Ide.t N E P D A F) jump_c start a0 :=
  let* plans := prepare_c I jump_c start a0 in
  let* cs := map_c (fun cr => Cost.ret (fst cr)) plans in
  let* table := Map.of_list_c (row_enc I) plans in
  let get := fun r => Map.find_or_c (row_enc I)
    (Rows.Make start [] (fun _ => Cost.ret (bot (Ide.values I)))) r table in
  Cost.ret (Analysis.Make (key_enc I) (row_enc I) (Ide.values I)
    (Rows.system cs get) (Rows.static cs get) (Policy.by_code (key_enc I))).

End IdeValue.

(** The value phase captures charged jump reads once and runs without a jump-law proof. *)
Definition value_analysis {N E P D A F} (I : Ide.t N E P D A F)
    (jump_c : jkey N D -> Cost.t F) start a0 :=
  Cost.value (IdeValue.analysis_c I jump_c start a0).

(** Value analysis laws need only key dictionaries and weak value-lattice laws. *)
Theorem value_analysis_laws {N E P D A F} (I : Ide.t N E P D A F) jump_c start a0 :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Ide.values I) -> Analysis.laws (value_analysis I jump_c start a0).
Proof.
  intros HN HE HD HL; unfold value_analysis, IdeValue.analysis_c;
    autorewrite with galois_cost; constructor.
  - apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD].
  - apply IdeValue.row_enc_laws; assumption.
  - exact HL.
  - apply Rows.static_laws.
Qed.

Arguments check_jumps_c {N E P D A F} I start J : simpl never.
Arguments check_jumps {N E P D A F} I start J : simpl never.
Arguments value_analysis {N E P D A F} I jump_c start a0 : simpl never.
