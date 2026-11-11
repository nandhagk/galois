(** * Shared indexed PRE reset graph

    Reset phases query one prepared operand-incidence graph in opposite directions.
    For example, a real-use operand stops down-safety propagation.
    Builds on: AnalysesSsaPreFrg, GraphPrepared, GraphSearchExact and BaseIndex. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphSearchExact.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreOperands.
Import List.ListNotations Cost.Notations.

Module PreReset.

(** Flags are stored on phi sites and missing entries denote false. *)
Record facts (B U : Type) := Facts {
  downsafe : Map.t (B * U) bool;
  can_available : Map.t (B * U) bool;
  later : Map.t (B * U) bool
}.
Arguments Facts {B U}.
Arguments downsafe {B U}.
Arguments can_available {B U}.
Arguments later {B U}.

(** Each phase keeps its original independent least-reset meaning. *)
Inductive phase :=
  | Down
  | Cannot
  | Later.

Section Context.
Context {B BE N E V K G C U : Type}.
Variable c : Pre.ctx B BE N E V K G C U.

Definition flag_c (m : Map.t (B * U) bool) k :=
  Map.find_or_c (PreFrg.phi_encoding c) false k m.
Definition flag m k := Cost.value (flag_c m k).

(** Down-safety resets travel from a user to a phi operand without a real use. *)
Inductive down_unsafe (f : PreFrg.frg B BE E U) : B * U -> Prop :=
  | down_seed : forall k,
      FinSet.mem (PreFrg.phi_encoding c) k (PreFrg.unsafe f) = true -> down_unsafe f k
  | down_step : forall b u k be op, down_unsafe f k ->
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op ->
      PreFrg.real_use op = false -> PreFrg.operand_version op = PreFrg.Phi b u ->
      down_unsafe f (b, u).

(** Cannot resets start at unavailable inputs and propagate to non-down-safe users. *)
Inductive cannot (f : PreFrg.frg B BE E U) (down : B * U -> bool) : B * U -> Prop :=
  | cannot_seed : forall k be op x, down k = false ->
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op ->
      PreFrg.operand_version op = PreFrg.Unavailable x -> cannot f down k
  | cannot_step : forall b u k be op, cannot f down (b, u) -> down k = false ->
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op ->
      PreFrg.real_use op = false -> PreFrg.operand_version op = PreFrg.Phi b u ->
      cannot f down k.

(** Later resets start at available real uses and propagate to can-available users. *)
Inductive later_reset (f : PreFrg.frg B BE E U) (can : B * U -> bool) : B * U -> Prop :=
  | later_seed : forall k be op, can k = true ->
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op ->
      PreFrg.real_use op = true ->
      (forall x, PreFrg.operand_version op <> PreFrg.Unavailable x) -> later_reset f can k
  | later_step : forall b u k be op, later_reset f can (b, u) -> can k = true ->
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op ->
      PreFrg.operand_version op = PreFrg.Phi b u -> later_reset f can k.

(** An operand node makes the real-use guard a scoped vertex decision. *)
Definition vertex := ((B * U) + ((B * U) * BE))%type.
Definition vertex_encoding :=
  sum_encoding (PreFrg.phi_encoding c) (PreFrg.link_encoding c).
Definition arc_encoding := pair_encoding vertex_encoding vertex_encoding.

Definition link_arcs (binding : ((B * U) * BE) * PreFrg.operand B E U)
    : list (vertex * vertex) :=
  let '(key, op) := binding in
  match PreFrg.operand_version op with
  | PreFrg.Phi b u => [(inl (b, u), inr key); (inr key, inl (fst key))]
  | _ => [(inr key, inl (fst key))]
  end.

Definition incidence_c (f : PreFrg.frg B BE E U) :=
  let* links := Map.elements_c (PreFrg.operands f) in
  fold_right_c (fun binding rest =>
    Cost.step ;; app_c (link_arcs binding) rest) [] links.
Definition incidence f := Cost.value (incidence_c f).

Definition endpoints_c (arcs : list (vertex * vertex)) :=
  fold_right_c (fun ab rest => Cost.ret (fst ab :: snd ab :: rest)) [] arcs.

(** The graph callback reads a once-built source index and never scans the arc inventory. *)
Definition indexed_graph (nodes : list vertex) (idx : Index.t vertex (vertex * vertex)) :=
  Graph.Make [] nodes (fun v => Index.find_c vertex_encoding v idx)
    (Cost.lift (fun _ => 1%N) (@fst vertex vertex))
    (Cost.lift (fun _ => 1%N) (@snd vertex vertex)).

(** Arc canonicalisation retains reachability while removing duplicate edge identities. *)
Definition graph_c (f : PreFrg.frg B BE E U) :=
  let* raw := incidence_c f in
  let* edge_set := FinSet.of_list_c arc_encoding raw in
  let* arcs := FinSet.elements_c edge_set in
  let* ends := endpoints_c arcs in
  let* phis := FinSet.elements_c (PreFrg.phis f) in
  let* unsafe := FinSet.elements_c (PreFrg.unsafe f) in
  let* sites := app_c phis unsafe in
  let* named := map_c (fun k => Cost.ret (inl k : vertex)) sites in
  let* all := app_c named ends in
  let* node_set := FinSet.of_list_c vertex_encoding all in
  let* nodes := FinSet.elements_c node_set in
  let* idx := Index.group_by_c vertex_encoding
    (Cost.lift (fun _ => 1%N) (@fst vertex vertex)) arcs in
  Cost.ret (indexed_graph nodes idx).
Definition graph f := Cost.value (graph_c f).

(** Preparation builds the shared dense outgoing and incoming indexes once. *)
Definition arcs_c f :=
  let* g := graph_c f in Prepared.prepare_c vertex_encoding g.
Definition arcs f := Cost.value (arcs_c f).

(** Reversal exchanges the prepared adjacency tables without rebuilding the graph. *)
Definition directed_c (p : Prepared.t vertex (vertex * vertex)) which :=
  match which with
  | Down => Prepared.reverse_c p []
  | _ => Cost.ret p
  end.
Definition directed p which := Cost.value (directed_c p which).

Definition admits_c (f : PreFrg.frg B BE E U) which
    (down can : Map.t (B * U) bool) (v : vertex) :=
  match v with
  | inl k =>
    match which with
    | Down => Cost.ret true
    | Cannot => Cost.map negb (flag_c down k)
    | Later => flag_c can k
    end
  | inr key =>
    match which with
    | Later => Cost.ret true
    | _ =>
      let* op := Map.get_c (PreFrg.link_encoding c) key (PreFrg.operands f) in
      Cost.ret (match op with Some op => negb (PreFrg.real_use op) | None => false end)
    end
  end.
Definition admits f which down can v := Cost.value (admits_c f which down can v).

Definition scope_c (p : Prepared.t vertex (vertex * vertex)) f which down can :=
  let* denied := filter_map_c (fun v =>
    Cost.step ;;
    let* keep := admits_c f which down can v in
    if keep then Cost.ret None else Prepared.id_of_c p v)
      (Graph.nodes (Prepared.graph p)) in
  let* blocked := FinSet.of_list_c positive_encoding denied in
  Cost.ret (Scope.Make blocked None).
Definition scope p f which down can := Cost.value (scope_c p f which down can).

Definition seed_c which (down can : Map.t (B * U) bool)
    (binding : ((B * U) * BE) * PreFrg.operand B E U) :=
  let '(key, op) := binding in
  match which with
  | Down => Cost.ret false
  | Cannot =>
    match PreFrg.operand_version op with
    | PreFrg.Unavailable _ => Cost.map negb (flag_c down (fst key))
    | _ => Cost.ret false
    end
  | Later =>
    if PreFrg.real_use op then
      match PreFrg.operand_version op with
      | PreFrg.Unavailable _ => Cost.ret false
      | _ => flag_c can (fst key)
      end
    else Cost.ret false
  end.

Definition seeds_c (f : PreFrg.frg B BE E U) which down can :=
  match which with
  | Down => FinSet.elements_c (PreFrg.unsafe f)
  | _ =>
    let* links := Map.elements_c (PreFrg.operands f) in
    let* selected := filter_c (seed_c which down can) links in
    map_c (fun binding => Cost.ret (fst (fst binding))) selected
  end.
Definition seeds f which down can := Cost.value (seeds_c f which down can).

(** Every query runs the existing search engine on a view of the same prepared graph. *)
Definition reset_closure_c p f which down can :=
  let* roots := seeds_c f which down can in
  let* named := map_c (fun k => Cost.ret (inl k : vertex)) roots in
  let* ids := Prepared.present_c (Prepared.id_of_c p) named in
  let* region := scope_c p f which down can in
  let* oriented := directed_c p which in
  let* result := SearchRun.run_c oriented Visitor.noop region ids tt in
  Cost.ret (Search.visited (fst result)).
Definition reset_closure p f which down can :=
  Cost.value (reset_closure_c p f which down can).

Definition flags_c (p : Prepared.t vertex (vertex * vertex))
    (keys : list (B * U)) (base : Map.t (B * U) bool)
    (use_base : bool) (reset : FinSet.t positive) :=
  fold_right_c (fun k result =>
    let* id := Prepared.id_of_c p (inl k : vertex) in
    let* cleared :=
      match id with
      | None => Cost.ret false
      | Some id => FinSet.mem_c positive_encoding id reset
      end in
    let* enabled := if use_base then flag_c base k else Cost.ret true in
    Map.set_c (PreFrg.phi_encoding c) k (enabled && negb cleared) result) Map.empty keys.

(** Solve charges one preparation followed by three scoped searches and flag materialisations. *)
Definition solve_c f :=
  let* prepared := arcs_c f in
  let* keys := FinSet.elements_c (PreFrg.phis f) in
  let* unsafe := reset_closure_c prepared f Down Map.empty Map.empty in
  let* down := flags_c prepared keys Map.empty false unsafe in
  let* unavailable := reset_closure_c prepared f Cannot down Map.empty in
  let* can := flags_c prepared keys Map.empty false unavailable in
  let* reset := reset_closure_c prepared f Later down can in
  let* later := flags_c prepared keys can true reset in
  Cost.ret (Facts down can later).
Definition solve f := Cost.value (solve_c f).

(** * Representation of the shared graph *)

(** The incidence list contains the two directed halves of each actual phi operand. *)
Theorem incidence_equation f :
  incidence f = flat_map link_arcs (Map.elements (PreFrg.operands f)).
Proof.
  unfold incidence, incidence_c. rewrite Cost.value_bind.
  fold (Map.elements (PreFrg.operands f)). rewrite value_fold_right_c.
  induction (Map.elements (PreFrg.operands f)) as [|binding rest IH]; [reflexivity|].
  cbn [fold_right flat_map]. autorewrite with galois_cost.
  rewrite IH. reflexivity.
Qed.

(** Endpoint enumeration names both ends of every arc in order. *)
Theorem endpoints_equation es :
  Cost.value (endpoints_c es) = flat_map (fun ab => [fst ab; snd ab]) es.
Proof.
  unfold endpoints_c. rewrite value_fold_right_c.
  induction es as [|[a b] rest IH]; cbn [fold_right flat_map]; [reflexivity|].
  autorewrite with galois_cost. now rewrite IH.
Qed.

Definition edge_inventory f :=
  FinSet.elements (FinSet.of_list arc_encoding (incidence f)).
Definition node_inventory f :=
  FinSet.elements (FinSet.of_list vertex_encoding
    (map (@inl (B * U) ((B * U) * BE))
      (FinSet.elements (PreFrg.phis f) ++ FinSet.elements (PreFrg.unsafe f)) ++
      flat_map (fun ab => [fst ab; snd ab]) (edge_inventory f))).

(** Graph construction exposes a canonical endpoint inventory and a stable source index. *)
Theorem graph_equation f :
  graph f = indexed_graph (node_inventory f)
    (Index.group_by vertex_encoding (@fst vertex vertex) (edge_inventory f)).
Proof.
  unfold graph, graph_c. rewrite !Cost.value_bind, Cost.value_ret.
  fold (incidence f).
  fold (FinSet.of_list arc_encoding (incidence f)).
  fold (edge_inventory f).
  rewrite endpoints_equation.
  fold (FinSet.elements (PreFrg.phis f)).
  fold (FinSet.elements (PreFrg.unsafe f)).
  rewrite value_app_c, value_map_c, value_app_c.
  fold (FinSet.of_list vertex_encoding
    (map (fun k => inl k : vertex)
      (FinSet.elements (PreFrg.phis f) ++ FinSet.elements (PreFrg.unsafe f)) ++
      flat_map (fun ab => [fst ab; snd ab]) (edge_inventory f))).
  fold (node_inventory f).
  rewrite Index.group_by_c_value.
  reflexivity.
Qed.

(** Preparation is the value of the single charged graph construction. *)
Theorem arcs_equation f :
  arcs f = Prepared.prepare vertex_encoding (graph f).
Proof.
  reflexivity.
Qed.

(** All node identities preserve both site and incoming-edge identities under context laws. *)
Theorem vertex_encoding_laws :
  Pre.laws c -> encoding_laws vertex_encoding.
Proof.
  intro Hlaw. apply sum_encoding_laws.
  - apply PreFrg.phi_encoding_laws; exact Hlaw.
  - apply PreFrg.link_encoding_laws; exact Hlaw.
Qed.

(** Source buckets contain precisely the inventory arcs with that source. *)
Theorem graph_out f v ab :
  Pre.laws c ->
  (In ab (Graph.out (graph f) v) <-> In ab (edge_inventory f) /\ fst ab = v).
Proof.
  intro Hlaw. rewrite graph_equation. unfold indexed_graph. rewrite Graph.make_out.
  change (In ab (Index.find vertex_encoding v
    (Index.group_by vertex_encoding (@fst vertex vertex) (edge_inventory f))) <->
    In ab (edge_inventory f) /\ fst ab = v).
  rewrite Index.find_group_by, filter_In.
  rewrite (eqb_true_iff vertex_encoding (vertex_encoding_laws Hlaw)). tauto.
Qed.

(** Canonical edge storage retains the incidence relation without inventing an arc. *)
Theorem edge_inventory_exact f ab :
  Pre.laws c -> (In ab (edge_inventory f) <-> In ab (incidence f)).
Proof.
  intro Hlaw. unfold edge_inventory.
  rewrite (FinSet.elements_spec arc_encoding
    (pair_encoding_laws vertex_encoding vertex_encoding
      (vertex_encoding_laws Hlaw) (vertex_encoding_laws Hlaw)) ab _
      (FinSet.wf_of_list _ _)).
  rewrite FinSet.mem_of_list, existsb_exists.
  split.
  - intros [other [Hin Heq]].
    apply (eqb_true_iff arc_encoding
      (pair_encoding_laws _ _ (vertex_encoding_laws Hlaw) (vertex_encoding_laws Hlaw)))
      in Heq. now subst other.
  - intro Hin. exists ab. split; [exact Hin|apply eqb_refl].
Qed.

(** Canonical node storage contains every listed site and both ends of every arc. *)
Theorem node_inventory_exact f v :
  Pre.laws c ->
  (In v (node_inventory f) <->
    (exists k, v = inl k /\
      (In k (FinSet.elements (PreFrg.phis f)) \/
        In k (FinSet.elements (PreFrg.unsafe f)))) \/
    exists ab, In ab (edge_inventory f) /\ (v = fst ab \/ v = snd ab)).
Proof.
  intro Hlaw. unfold node_inventory.
  rewrite (FinSet.elements_spec vertex_encoding (vertex_encoding_laws Hlaw) v _
    (FinSet.wf_of_list _ _)).
  rewrite FinSet.mem_of_list, existsb_exists.
  assert (Hmember : forall xs,
    (exists other, In other xs /\ eqb vertex_encoding v other = true) <-> In v xs).
  { intro xs. split.
    - intros [other [Hin Heq]].
      apply (eqb_true_iff _ (vertex_encoding_laws Hlaw)) in Heq. now subst other.
    - intro Hin. exists v. split; [exact Hin|apply eqb_refl]. }
  rewrite Hmember, in_app_iff, in_map_iff, in_flat_map.
  split.
  - intros [[k [Heq Hin]]|[ab [Hin Hend]]].
    + left. exists k. split; [symmetry; exact Heq|now apply in_app_iff in Hin].
    + right. exists ab. split; [exact Hin|cbn in Hend; intuition congruence].
  - intros [[k [-> Hin]]|[ab [Hin Hend]]].
    + left. exists k. split; [reflexivity|now apply in_app_iff].
    + right. exists ab. split; [exact Hin|cbn; intuition congruence].
Qed.

(** Sources and targets of the constructed graph are the literal incidence endpoints. *)
Theorem graph_endpoints f ab :
  Graph.source (graph f) ab = fst ab /\ Graph.target (graph f) ab = snd ab.
Proof.
  rewrite graph_equation. unfold indexed_graph.
  rewrite Graph.make_source, Graph.make_target, !Cost.value_lift. split; reflexivity.
Qed.

(** The once-built indexed graph has closed endpoints and canonical node and edge identities. *)
Theorem graph_ready f :
  Pre.laws c ->
  graph_wf (graph f) /\ (forall v, NoDup (Graph.out (graph f) v)).
Proof.
  intro Hlaw. split.
  - constructor.
    + rewrite graph_equation. cbn [indexed_graph Graph.nodes].
      apply (FinSet.elements_nodup vertex_encoding), FinSet.wf_of_list.
    + intros v Hin. rewrite graph_equation in Hin.
      cbn [indexed_graph Graph.entries] in Hin. contradiction.
    + intros v ab Hin. apply (graph_out f v ab Hlaw) in Hin.
      rewrite (proj1 (graph_endpoints f ab)). exact (proj2 Hin).
    + intros v ab Hv Hin. apply (graph_out f v ab Hlaw) in Hin.
      rewrite (proj2 (graph_endpoints f ab)), graph_equation.
      change (In (snd ab) (node_inventory f)).
      apply node_inventory_exact; [exact Hlaw|].
      right. exists ab. split; [exact (proj1 Hin)|now right].
  - intro v. rewrite graph_equation. unfold indexed_graph. rewrite Graph.make_out.
    change (NoDup (Index.find vertex_encoding v
      (Index.group_by vertex_encoding (@fst vertex vertex) (edge_inventory f)))).
    rewrite Index.find_group_by. apply NoDup_filter.
    apply (FinSet.elements_nodup arc_encoding), FinSet.wf_of_list.
Qed.

(** The actual charged preparation establishes all public search initialization duties. *)
Theorem arcs_ready f :
  Pre.laws c -> Prepared.ready (arcs f).
Proof.
  intro Hlaw. rewrite arcs_equation.
  apply Prepared.prepare_ready; [apply vertex_encoding_laws; exact Hlaw| |].
  - exact (proj1 (graph_ready f Hlaw)).
  - exact (proj2 (graph_ready f Hlaw)).
Qed.

(** Reversed down-safety queries reuse names and keep the same valid-ID domain. *)
Theorem directed_ready p which :
  Prepared.ready p -> Prepared.ready (directed p which).
Proof.
  intro Hp. destruct which; [|exact Hp|exact Hp].
  change (Prepared.ready (Prepared.reverse p [])).
  apply Prepared.reverse_ready; [exact Hp|intros i Hin; contradiction].
Qed.

(** Orientation does not change the prepared name assigned to any site or operand. *)
Theorem directed_id p which v :
  Prepared.id_of (directed p which) v = Prepared.id_of p v.
Proof.
  destruct which; [apply Prepared.reverse_id_of|reflexivity|reflexivity].
Qed.

(** The reset query returns the visited set of the existing scoped search producer. *)
Theorem reset_closure_equation p f which down can :
  reset_closure p f which down can =
    Search.visited (SearchRun.dfs (directed p which) (scope p f which down can)
      (Prepared.present (Prepared.id_of p)
        (map (fun k => inl k : vertex) (seeds f which down can)))).
Proof.
  unfold reset_closure, reset_closure_c. rewrite !Cost.value_bind, Cost.value_ret.
  fold (seeds f which down can).
  rewrite value_map_c, Prepared.present_c_value.
  reflexivity.
Qed.

(** Search representation transports initialized reset queries to scoped reachability. *)
Theorem reset_closure_reachable p f which down can id :
  Prepared.ready p ->
  (FinSet.mem positive_encoding id (reset_closure p f which down can) = true <->
    Search.scoped_reachable (directed p which) (scope p f which down can)
      (Prepared.present (Prepared.id_of p)
        (map (fun k => inl k : vertex) (seeds f which down can))) id).
Proof.
  intro Hp. rewrite reset_closure_equation.
  rewrite (proj2 (proj2 (proj2 (proj2 (proj2
    (SearchExact.run_representation (directed p which) (scope p f which down can)
      (Prepared.present (Prepared.id_of p)
        (map (fun k => inl k : vertex) (seeds f which down can))))))))).
  apply SearchExact.run_reachable, directed_ready. exact Hp.
Qed.

(** A prepared name determines its client vertex uniquely. *)
Lemma id_unique (p : Prepared.t vertex (vertex * vertex)) v w id :
  Prepared.ready p ->
  Prepared.id_of p v = Some id -> Prepared.id_of p w = Some id -> v = w.
Proof.
  intros [_ [_ Hp]] Hv Hw.
  pose proof (Prepared.name_of_id_of p v id Hp Hv).
  pose proof (Prepared.name_of_id_of p w id Hp Hw). congruence.
Qed.

(** The blocked-ID construction implements the phase predicate on every prepared vertex. *)
Theorem scope_admits p f which down can v id :
  Prepared.ready p -> Prepared.id_of p v = Some id ->
  Scope.admits (scope p f which down can) id = admits f which down can v.
Proof.
  intros Hp Hid.
  assert (Hin : In v (Graph.nodes (Prepared.graph p))).
  { apply (Prepared.ids_domain p (proj2 (proj2 Hp))). now exists id. }
  unfold scope, scope_c. rewrite !Cost.value_bind, Cost.value_ret.
  rewrite value_filter_map_c.
  fold (FinSet.of_list positive_encoding
    (filter_map (fun v => Cost.value
      (Cost.step ;; let* keep := admits_c f which down can v in
        if keep then Cost.ret None else Prepared.id_of_c p v))
      (Graph.nodes (Prepared.graph p)))).
  rewrite Scope.admits_equation. cbn [Scope.blocked Scope.within andb].
  rewrite FinSet.mem_of_list.
  assert (Hblocked :
    existsb (eqb positive_encoding id)
      (filter_map (fun v => Cost.value
        (Cost.step ;; let* keep := admits_c f which down can v in
          if keep then Cost.ret None else Prepared.id_of_c p v))
        (Graph.nodes (Prepared.graph p))) = true <->
    admits f which down can v = false).
  { rewrite existsb_exists. split.
    - intros [other [Hother Heq]].
      apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq. subst other.
      apply filter_map_spec in Hother. destruct Hother as [w [Hw Hout]].
      autorewrite with galois_cost in Hout. fold (admits f which down can w) in Hout.
      destruct (admits f which down can w) eqn:Hkeep; [discriminate|].
      change (Prepared.id_of p w = Some id) in Hout.
      pose proof (id_unique p v w id Hp Hid Hout) as ->. exact Hkeep.
    - intro Hkeep. exists id. split; [|apply eqb_refl].
      apply filter_map_spec. exists v. split; [exact Hin|].
      autorewrite with galois_cost. fold (admits f which down can v).
      rewrite Hkeep. exact Hid. }
  destruct (existsb _ _), (admits f which down can v); cbn in *;
    intuition discriminate.
Qed.

(** Orientation reverses the same incidence relation only for down-safety. *)
Definition oriented_edge f which (x y : vertex) : Prop :=
  In (match which with Down => (y, x) | _ => (x, y) end) (incidence f).

(** A named query result observes the dense search output through its original name. *)
Definition reached f which down can (v : vertex) : Prop :=
  exists id, Prepared.id_of (arcs f) v = Some id /\
    FinSet.mem positive_encoding id
      (reset_closure (arcs f) f which down can) = true.

Lemma incidence_nodes f x y :
  Pre.laws c -> In (x, y) (incidence f) ->
  In x (Graph.nodes (graph f)) /\ In y (Graph.nodes (graph f)).
Proof.
  intros Hlaw Hin.
  assert (Hedge : In (x, y) (edge_inventory f)).
  { apply edge_inventory_exact; assumption. }
  rewrite graph_equation. change (In x (node_inventory f) /\ In y (node_inventory f)).
  split; apply node_inventory_exact; try exact Hlaw; right; exists (x, y);
    split; [exact Hedge|now left|exact Hedge|now right].
Qed.

Lemma named_arc f x y i j :
  Pre.laws c ->
  Prepared.id_of (arcs f) x = Some i -> Prepared.id_of (arcs f) y = Some j ->
  In (x, y) (incidence f) -> Prepared.arc (arcs f) i (x, y) j.
Proof.
  intros Hlaw Hx Hy Hedge.
  exists x, y. rewrite arcs_equation, Prepared.prepare_graph.
  split; [exact (proj1 (incidence_nodes f x y Hlaw Hedge))|].
  split; [exact Hx|]. split; [exact Hy|].
  split; [exact (proj1 (graph_endpoints f (x, y)))|].
  split; [exact (proj2 (graph_endpoints f (x, y)))|].
  apply graph_out; [exact Hlaw|]. split; [apply edge_inventory_exact; assumption|reflexivity].
Qed.

Lemma arc_names f i ab j :
  Pre.laws c -> Prepared.arc (arcs f) i ab j ->
  Prepared.id_of (arcs f) (fst ab) = Some i /\
  Prepared.id_of (arcs f) (snd ab) = Some j /\ In ab (incidence f).
Proof.
  intros Hlaw [x [y [Hx [Hi [Hj [Hsource [Htarget Hedge]]]]]]].
  assert (Hgraph : Prepared.graph (arcs f) = graph f).
  { rewrite arcs_equation, Prepared.prepare_graph. reflexivity. }
  rewrite Hgraph in Hsource, Htarget, Hedge.
  change (fst ab = x) in Hsource.
  change (snd ab = y) in Htarget.
  subst x y. split; [exact Hi|]. split; [exact Hj|].
  apply edge_inventory_exact; [exact Hlaw|].
  exact (proj1 (proj1 (graph_out f (fst ab) ab Hlaw) Hedge)).
Qed.

Lemma directed_arc_names f which i ab j :
  Pre.laws c -> Prepared.arc (directed (arcs f) which) i ab j ->
  exists x y, Prepared.id_of (arcs f) x = Some i /\
    Prepared.id_of (arcs f) y = Some j /\ oriented_edge f which x y.
Proof.
  intros Hlaw Hedge. destruct which.
  - change (Prepared.arc (Prepared.reverse (arcs f) []) i ab j) in Hedge.
    apply (proj1 (Prepared.reverse_arc (arcs f) [] j ab i (arcs_ready f Hlaw))) in Hedge.
    destruct (arc_names f j ab i Hlaw Hedge) as [Hj [Hi Hin]].
    exists (snd ab), (fst ab). repeat split; try assumption.
    destruct ab; exact Hin.
  - destruct (arc_names f i ab j Hlaw Hedge) as [Hi [Hj Hin]].
    exists (fst ab), (snd ab). repeat split; try assumption. destruct ab; exact Hin.
  - destruct (arc_names f i ab j Hlaw Hedge) as [Hi [Hj Hin]].
    exists (fst ab), (snd ab). repeat split; try assumption. destruct ab; exact Hin.
Qed.

Lemma oriented_nodes f which x y :
  Pre.laws c -> oriented_edge f which x y ->
  In x (Graph.nodes (graph f)) /\ In y (Graph.nodes (graph f)).
Proof.
  intros Hlaw Hedge. destruct which.
  - destruct (incidence_nodes f y x Hlaw Hedge). split; assumption.
  - apply incidence_nodes; assumption.
  - apply incidence_nodes; assumption.
Qed.

Lemma oriented_arc f which x y i j :
  Pre.laws c ->
  Prepared.id_of (arcs f) x = Some i -> Prepared.id_of (arcs f) y = Some j ->
  oriented_edge f which x y ->
  exists ab, Prepared.arc (directed (arcs f) which) i ab j.
Proof.
  intros Hlaw Hi Hj Hedge. destruct which.
  - exists (y, x). apply (proj2
      (Prepared.reverse_arc (arcs f) [] j (y, x) i (arcs_ready f Hlaw))).
    apply named_arc; assumption.
  - exists (x, y). apply named_arc; assumption.
  - exists (x, y). apply named_arc; assumption.
Qed.

Lemma named_id f v :
  Pre.laws c -> In v (Graph.nodes (graph f)) ->
  exists id, Prepared.id_of (arcs f) v = Some id.
Proof.
  intros Hlaw Hin. apply (Prepared.ids_domain _ (proj2 (proj2 (arcs_ready f Hlaw)))).
  rewrite arcs_equation, Prepared.prepare_graph. exact Hin.
Qed.

Lemma scoped_start_admits (p : Prepared.t vertex (vertex * vertex)) region i es j :
  Search.scoped_path p region i es j -> Scope.admits region i = true.
Proof.
  intro Hpath. destruct Hpath; assumption.
Qed.

Lemma scoped_snoc (p : Prepared.t vertex (vertex * vertex)) region i es j ab k :
  Search.scoped_path p region i es j -> Prepared.arc p j ab k ->
  Prepared.valid_id p k -> Scope.admits region k = true ->
  Search.scoped_path p region i (es ++ [ab]) k.
Proof.
  intro Hpath. induction Hpath; intros Hedge Hvalid Hallowed.
  - cbn. econstructor; [eassumption|eassumption|exact Hedge|].
    constructor; assumption.
  - cbn. econstructor; [eassumption|eassumption|eassumption|].
    apply IHHpath; assumption.
Qed.

(** A phase seed is present in the actual search whenever its vertex is admitted. *)
Theorem reached_seed f which down can k :
  Pre.laws c -> In k (seeds f which down can) ->
  In (inl k) (Graph.nodes (graph f)) ->
  admits f which down can (inl k) = true -> reached f which down can (inl k).
Proof.
  intros Hlaw Hseed Hnode Hallowed.
  destruct (named_id f (inl k) Hlaw Hnode) as [id Hid].
  exists id. split; [exact Hid|].
  apply reset_closure_reachable; [apply arcs_ready; exact Hlaw|].
  exists id, []. split.
  - apply Prepared.present_spec. exists (inl k). split; [apply in_map; exact Hseed|exact Hid].
  - constructor.
    + exists (inl k). split.
      * destruct which; exact Hnode.
      * rewrite directed_id. exact Hid.
    + rewrite (scope_admits _ _ _ _ _ _ _ (arcs_ready f Hlaw) Hid). exact Hallowed.
Qed.

(** Following an admitted incidence edge extends the same search result. *)
Theorem reached_step f which down can x y :
  Pre.laws c -> reached f which down can x -> oriented_edge f which x y ->
  admits f which down can y = true -> reached f which down can y.
Proof.
  intros Hlaw [i [Hi Hreached]] Hedge Hallowed.
  destruct (named_id f y Hlaw (proj2 (oriented_nodes f which x y Hlaw Hedge))) as [j Hj].
  destruct (oriented_arc f which x y i j Hlaw Hi Hj Hedge) as [ab Hab].
  exists j. split; [exact Hj|].
  apply (reset_closure_reachable _ _ _ _ _ _ (arcs_ready f Hlaw)) in Hreached.
  apply reset_closure_reachable; [apply arcs_ready; exact Hlaw|].
  destruct Hreached as [root [es [Hroot Hpath]]].
  exists root, (es ++ [ab]). split; [exact Hroot|].
  eapply scoped_snoc; [exact Hpath|exact Hab| |].
  - exists y. split.
    + destruct which; exact (proj2 (oriented_nodes f _ x y Hlaw Hedge)).
    + rewrite directed_id. exact Hj.
  - rewrite (scope_admits _ _ _ _ _ _ _ (arcs_ready f Hlaw) Hj). exact Hallowed.
Qed.

(** Every named search result follows from admitted seeds and incidence-edge preservation. *)
Theorem reached_induction f which down can (P : vertex -> Prop) :
  Pre.laws c ->
  (forall k, In k (seeds f which down can) ->
    admits f which down can (inl k) = true -> P (inl k)) ->
  (forall x y, P x -> oriented_edge f which x y ->
    admits f which down can x = true -> admits f which down can y = true -> P y) ->
  forall v, reached f which down can v -> P v.
Proof.
  intros Hlaw Hseed Hstep.
  assert (Hpath : forall i es j,
    Search.scoped_path (directed (arcs f) which) (scope (arcs f) f which down can) i es j ->
    forall x y, Prepared.id_of (arcs f) x = Some i ->
      Prepared.id_of (arcs f) y = Some j -> P x -> P y).
  { intros i es j Hrun. induction Hrun as [i Hvalid Hallowed|
      i ab middle es j Hvalid Hallowed Hedge Htail IH]; intros x y Hx Hy HP.
    - pose proof (id_unique _ x y i (arcs_ready f Hlaw) Hx Hy) as ->. exact HP.
    - destruct (directed_arc_names f which i ab middle Hlaw Hedge)
        as [a [b [Ha [Hb Hab]]]].
      pose proof (id_unique _ x a i (arcs_ready f Hlaw) Hx Ha) as ->.
      apply (IH b y Hb Hy). apply (Hstep a b HP Hab).
      + rewrite <- (scope_admits _ _ _ _ _ _ _ (arcs_ready f Hlaw) Ha). exact Hallowed.
      + rewrite <- (scope_admits _ _ _ _ _ _ _ (arcs_ready f Hlaw) Hb).
        exact (scoped_start_admits _ _ _ _ _ Htail). }
  intros v [id [Hid Hreached]].
  apply (reset_closure_reachable _ _ _ _ _ _ (arcs_ready f Hlaw)) in Hreached.
  destruct Hreached as [root [es [Hroot Hrun]]].
  apply Prepared.present_spec in Hroot.
  destruct Hroot as [name [Hname Hroot]].
  apply in_map_iff in Hname. destruct Hname as [k [<- Hk]].
  apply (Hpath root es id Hrun (inl k) v Hroot Hid).
  apply Hseed; [exact Hk|].
  rewrite <- (scope_admits _ _ _ _ _ _ _ (arcs_ready f Hlaw) Hroot).
  exact (scoped_start_admits _ _ _ _ _ Hrun).
Qed.

(** Incidence arcs are owned by an actual indexed operand, including its incoming-edge identity. *)
Theorem incidence_exact f x y :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  (In (x, y) (incidence f) <->
    exists key op, Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op /\
      ((x = inr key /\ y = inl (fst key)) \/
        exists b u, PreFrg.operand_version op = PreFrg.Phi b u /\
          x = inl (b, u) /\ y = inr key)).
Proof.
  intros Hlaw Hwf. rewrite incidence_equation, in_flat_map.
  split.
  - intros [[key op] [Hbinding Hin]].
    exists key, op. split.
    + apply (proj1 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)).
      exact Hbinding.
    + cbn [link_arcs] in Hin.
      destruct (PreFrg.operand_version op) as [u|u|e u|b u] eqn:Hversion;
        cbn in Hin.
      all: try (destruct Hin as [Heq|Hfalse]; [inversion Heq; left; auto|contradiction]).
      destruct Hin as [Heq|[Heq|Hfalse]]; [| |contradiction].
      * inversion Heq. right. exists b, u. repeat split; assumption || reflexivity.
      * inversion Heq. left. auto.
  - intros [key [op [Hbinding [Hedge|[b [u [Hversion Hedge]]]]]]].
    + exists (key, op). split.
      * apply (proj2 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)).
        exact Hbinding.
      * destruct Hedge as [-> ->]. cbn [link_arcs].
        destruct (PreFrg.operand_version op); cbn; auto.
    + exists (key, op). split.
      * apply (proj2 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)).
        exact Hbinding.
      * destruct Hedge as [-> ->]. cbn [link_arcs]. rewrite Hversion. now left.
Qed.

(** Seed enumeration retains the original unavailable and real-use tests in operand order. *)
Theorem seeds_equation f which down can :
  seeds f which down can =
    match which with
    | Down => FinSet.elements (PreFrg.unsafe f)
    | _ => map (fun binding => fst (fst binding))
        (filter (fun binding => Cost.value (seed_c which down can binding))
          (Map.elements (PreFrg.operands f)))
    end.
Proof.
  destruct which; [reflexivity| |].
  all: unfold seeds, seeds_c; rewrite !Cost.value_bind.
  all: rewrite value_map_c, value_filter_c; reflexivity.
Qed.

(** Cannot seeds are precisely non-down-safe users having an unavailable operand. *)
Theorem cannot_seeds_exact f down can k :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  (In k (seeds f Cannot down can) <->
    flag down k = false /\ exists be op u,
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op /\
      PreFrg.operand_version op = PreFrg.Unavailable u).
Proof.
  intros Hlaw Hwf. rewrite seeds_equation, in_map_iff. split.
  - intros [[[key be] op] [Heq Hin]]. cbn in Heq. subst key.
    apply filter_In in Hin. destruct Hin as [Hin Hseed].
    apply (proj1 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)) in Hin.
    cbn [seed_c] in Hseed.
    destruct (PreFrg.operand_version op) as [u|u|e u|b u] eqn:Hversion;
      try discriminate.
    rewrite Cost.value_map in Hseed. apply negb_true_iff in Hseed.
    split; [exact Hseed|]. exists be, op, u. split; assumption.
  - intros [Hdown [be [op [u [Hget Hversion]]]]].
    exists ((k, be), op). split; [reflexivity|]. apply filter_In. split.
    + apply (proj2 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)).
      exact Hget.
    + cbn [seed_c]. rewrite Hversion, Cost.value_map.
      change (negb (flag down k) = true). now rewrite Hdown.
Qed.

(** Later seeds are precisely can-available users having an available real-use operand. *)
Theorem later_seeds_exact f down can k :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  (In k (seeds f Later down can) <->
    flag can k = true /\ exists be op,
      Map.get (PreFrg.link_encoding c) (k, be) (PreFrg.operands f) = Some op /\
      PreFrg.real_use op = true /\
      forall u, PreFrg.operand_version op <> PreFrg.Unavailable u).
Proof.
  intros Hlaw Hwf. rewrite seeds_equation, in_map_iff. split.
  - intros [[[key be] op] [Heq Hin]]. cbn in Heq. subst key.
    apply filter_In in Hin. destruct Hin as [Hin Hseed].
    apply (proj1 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)) in Hin.
    cbn [seed_c] in Hseed.
    destruct (PreFrg.real_use op) eqn:Hreal; [|discriminate].
    destruct (PreFrg.operand_version op) as [u|u|e u|b u] eqn:Hversion; try discriminate.
    all: split; [exact Hseed|].
    all: exists be, op; split; [exact Hin|]; split; [exact Hreal|].
    all: intros x Heq; rewrite Hversion in Heq; discriminate.
  - intros [Hcan [be [op [Hget [Hreal Havailable]]]]].
    exists ((k, be), op). split; [reflexivity|]. apply filter_In. split.
    + apply (proj2 (Map.elements_spec _ (PreFrg.link_encoding_laws c Hlaw) _ _ _ Hwf)).
      exact Hget.
    + cbn [seed_c]. rewrite Hreal.
      destruct (PreFrg.operand_version op) eqn:Hversion; try exact Hcan.
      exfalso. exact (Havailable u eq_refl).
Qed.

(** Every operand connects its gate to its user site. *)
Lemma operand_owner_arc f key op :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op ->
  In (inr key, inl (fst key)) (incidence f).
Proof.
  intros Hlaw Hwf Hget. apply incidence_exact; try assumption.
  exists key, op. split; [exact Hget|]. left. split; reflexivity.
Qed.

(** A phi-selected operand additionally connects its definition site to its gate. *)
Lemma operand_phi_arc f key op b u :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op ->
  PreFrg.operand_version op = PreFrg.Phi b u ->
  In (inl (b, u), inr key) (incidence f).
Proof.
  intros Hlaw Hwf Hget Hversion. apply incidence_exact; try assumption.
  exists key, op. split; [exact Hget|]. right. exists b, u.
  repeat split; assumption || reflexivity.
Qed.

(** Non-later scopes admit an operand gate precisely when its real-use bit is false. *)
Lemma admits_gate f which down can key op :
  which <> Later ->
  Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op ->
  admits f which down can (inr key) = negb (PreFrg.real_use op).
Proof.
  intros Hwhich Hget. destruct which; [| |contradiction].
  all: unfold admits, admits_c; rewrite Cost.value_bind, Cost.value_ret.
  all: change
    ((match Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) with
      | Some op => negb (PreFrg.real_use op)
      | None => false
      end) = negb (PreFrg.real_use op)).
  all: now rewrite Hget.
Qed.

(** The reversed shared query is exactly the original independent down-safety reset set. *)
Theorem down_closure_exact f down can k :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.unsafe f) ->
  (reached f Down down can (inl k) <-> down_unsafe f k).
Proof.
  intros Hlaw Hwf Hunsafe. split.
  - apply (reached_induction f Down down can (fun v =>
      match v with
      | inl k => down_unsafe f k
      | inr key => exists op,
          Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op /\
          PreFrg.real_use op = false /\ down_unsafe f (fst key)
      end) Hlaw).
    + intros seed Hseed Hallowed. apply down_seed.
      rewrite seeds_equation in Hseed.
      apply (proj1 (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw) _ _ Hunsafe)).
      exact Hseed.
    + intros x y HP Hedge Hx Hy.
      apply (proj1 (incidence_exact f y x Hlaw Hwf)) in Hedge.
      destruct Hedge as [key [op [Hget [[-> ->]|[b [u [Hversion [-> ->]]]]]]]].
      * exists op. split; [exact Hget|]. split; [|exact HP].
        rewrite (admits_gate f Down down can key op ltac:(discriminate) Hget) in Hy.
        now apply negb_true_iff in Hy.
      * destruct HP as [selected [Hselected [Hreal Hreset]]].
        assert (selected = op) as -> by congruence.
        destruct key as [[block expression] be].
        eapply down_step; eassumption.
  - intro Hreset. induction Hreset as [key Hseed|
      b u key be op Hreset IH Hget Hreal Hversion].
    + apply reached_seed; try exact Hlaw.
      * rewrite seeds_equation.
        apply (proj2 (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw) _ _ Hunsafe)).
        exact Hseed.
      * rewrite graph_equation. change (In (inl key) (node_inventory f)).
        apply node_inventory_exact; [exact Hlaw|]. left. exists key.
        split; [reflexivity|]. right.
        apply (proj2 (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw) _ _ Hunsafe)).
        exact Hseed.
      * reflexivity.
    + eapply reached_step with (x := inr (key, be)); [exact Hlaw| | |reflexivity].
      * eapply reached_step; [exact Hlaw|exact IH| |].
        -- apply operand_owner_arc with (op := op); assumption.
        -- rewrite (admits_gate f Down down can (key, be) op ltac:(discriminate) Hget).
           now rewrite Hreal.
      * apply operand_phi_arc with (op := op); assumption.
Qed.

(** The first forward query is exactly the independent can-availability reset set. *)
Theorem cannot_closure_exact f down can k :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  (reached f Cannot down can (inl k) <-> cannot f (flag down) k).
Proof.
  intros Hlaw Hwf. split.
  - apply (reached_induction f Cannot down can (fun v =>
      match v with
      | inl k => cannot f (flag down) k
      | inr key => exists op b u,
          Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op /\
          PreFrg.operand_version op = PreFrg.Phi b u /\
          PreFrg.real_use op = false /\ cannot f (flag down) (b, u)
      end) Hlaw).
    + intros seed Hseed Hallowed. apply (cannot_seeds_exact f down can seed Hlaw Hwf) in Hseed.
      destruct Hseed as [Hdown [be [op [u [Hget Hversion]]]]].
      eapply cannot_seed; eassumption.
    + intros x y HP Hedge Hx Hy.
      apply (proj1 (incidence_exact f x y Hlaw Hwf)) in Hedge.
      destruct Hedge as [key [op [Hget [[-> ->]|[b [u [Hversion [-> ->]]]]]]]].
      * destruct HP as [selected [b [u [Hselected [Hversion [Hreal Hreset]]]]]].
        assert (selected = op) as -> by congruence.
        change (negb (flag down (fst key)) = true) in Hy.
        apply negb_true_iff in Hy. destruct key as [[block expression] be].
        eapply cannot_step; eassumption.
      * exists op, b, u. split; [exact Hget|]. split; [exact Hversion|].
        split; [|exact HP].
        rewrite (admits_gate f Cannot down can key op ltac:(discriminate) Hget) in Hy.
        now apply negb_true_iff in Hy.
  - intro Hreset. induction Hreset as [key be op u Hdown Hget Hversion|
      b u key be op Hreset IH Hdown Hget Hreal Hversion].
    + apply reached_seed; try exact Hlaw.
      * apply cannot_seeds_exact; try assumption.
        split; [exact Hdown|]. exists be, op, u. split; assumption.
      * exact (proj2 (incidence_nodes f (inr (key, be)) (inl key) Hlaw
          (operand_owner_arc f (key, be) op Hlaw Hwf Hget))).
      * change (negb (flag down key) = true). now rewrite Hdown.
    + eapply reached_step with (x := inr (key, be)); [exact Hlaw| | |].
      * eapply reached_step; [exact Hlaw|exact IH| |].
        -- apply operand_phi_arc with (op := op); assumption.
        -- rewrite (admits_gate f Cannot down can (key, be) op ltac:(discriminate) Hget).
           now rewrite Hreal.
      * apply operand_owner_arc with (op := op); assumption.
      * change (negb (flag down key) = true). now rewrite Hdown.
Qed.

(** The second forward query is exactly the independent later reset set. *)
Theorem later_closure_exact f down can k :
  Pre.laws c -> Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  (reached f Later down can (inl k) <-> later_reset f (flag can) k).
Proof.
  intros Hlaw Hwf. split.
  - apply (reached_induction f Later down can (fun v =>
      match v with
      | inl k => later_reset f (flag can) k
      | inr key => exists op b u,
          Map.get (PreFrg.link_encoding c) key (PreFrg.operands f) = Some op /\
          PreFrg.operand_version op = PreFrg.Phi b u /\ later_reset f (flag can) (b, u)
      end) Hlaw).
    + intros seed Hseed Hallowed. apply (later_seeds_exact f down can seed Hlaw Hwf) in Hseed.
      destruct Hseed as [Hcan [be [op [Hget [Hreal Havailable]]]]].
      eapply later_seed; eassumption.
    + intros x y HP Hedge Hx Hy.
      apply (proj1 (incidence_exact f x y Hlaw Hwf)) in Hedge.
      destruct Hedge as [key [op [Hget [[-> ->]|[b [u [Hversion [-> ->]]]]]]]].
      * destruct HP as [selected [b [u [Hselected [Hversion Hreset]]]]].
        assert (selected = op) as -> by congruence.
        change (flag can (fst key) = true) in Hy. destruct key as [[block expression] be].
        eapply later_step; eassumption.
      * exists op, b, u. repeat split; assumption.
  - intro Hreset. induction Hreset as [key be op Hcan Hget Hreal Havailable|
      b u key be op Hreset IH Hcan Hget Hversion].
    + apply reached_seed; try exact Hlaw.
      * apply later_seeds_exact; try assumption.
        split; [exact Hcan|]. exists be, op. repeat split; assumption.
      * exact (proj2 (incidence_nodes f (inr (key, be)) (inl key) Hlaw
          (operand_owner_arc f (key, be) op Hlaw Hwf Hget))).
      * exact Hcan.
    + eapply reached_step with (x := inr (key, be)); [exact Hlaw| | |exact Hcan].
      * eapply reached_step; [exact Hlaw|exact IH| |reflexivity].
        apply operand_phi_arc with (op := op); assumption.
      * apply operand_owner_arc with (op := op); assumption.
Qed.

Definition reset_member (p : Prepared.t vertex (vertex * vertex)) reset k :=
  match Prepared.id_of p (inl k : vertex) with
  | None => false
  | Some id => FinSet.mem positive_encoding id reset
  end.

(** Flag materialisation is a charged right fold over the supplied phi inventory. *)
Theorem flags_equation p keys base use_base reset :
  Cost.value (flags_c p keys base use_base reset) =
    fold_right (fun k result => Map.set (PreFrg.phi_encoding c) k
      ((if use_base then flag base k else true) && negb (reset_member p reset k)) result)
      Map.empty keys.
Proof.
  unfold flags_c. rewrite value_fold_right_c.
  induction keys as [|key rest IH]; [reflexivity|].
  cbn [fold_right]. rewrite !Cost.value_bind.
  fold (Prepared.id_of p (inl key : vertex)).
  destruct (Prepared.id_of p (inl key : vertex)) as [id|] eqn:Hid;
    destruct use_base; autorewrite with galois_cost; fold (flag base key);
    unfold reset_member; rewrite Hid, IH; reflexivity.
Qed.

(** Materialised flag maps are canonical for arbitrary input flags and reset sets. *)
Theorem flags_wf p keys base use_base reset :
  Map.wf (PreFrg.phi_encoding c) (Cost.value (flags_c p keys base use_base reset)).
Proof.
  rewrite flags_equation.
  induction keys; cbn [fold_right]; [apply Map.wf_empty|apply Map.wf_set; exact IHkeys].
Qed.

(** Every inventoried site receives its queried complement, intersected with the optional base. *)
Theorem flags_get p keys base use_base reset k :
  Pre.laws c -> In k keys ->
  flag (Cost.value (flags_c p keys base use_base reset)) k =
    ((if use_base then flag base k else true) && negb (reset_member p reset k)).
Proof.
  intros Hlaw Hin.
  rewrite flags_equation. revert Hin.
  induction keys as [|key rest IH]; intro Hin; [contradiction|].
  cbn [fold_right].
  assert (Hwf : Map.wf (PreFrg.phi_encoding c)
    (fold_right (fun k result => Map.set (PreFrg.phi_encoding c) k
      ((if use_base then flag base k else true) && negb (reset_member p reset k)) result)
      Map.empty rest)).
  { rewrite <- flags_equation. apply flags_wf. }
  change (Map.find_or (PreFrg.phi_encoding c) false k
    (Map.set (PreFrg.phi_encoding c) key
      ((if use_base then flag base key else true) && negb (reset_member p reset key))
      (fold_right (fun k result => Map.set (PreFrg.phi_encoding c) k
        ((if use_base then flag base k else true) && negb (reset_member p reset k)) result)
        Map.empty rest)) =
    ((if use_base then flag base k else true) && negb (reset_member p reset k))).
  rewrite Map.find_or_equation.
  destruct (eqb_dec (PreFrg.phi_encoding c) (PreFrg.phi_encoding_laws c Hlaw) k key)
    as [->|Hne].
  - rewrite Map.get_set_same by exact Hwf. reflexivity.
  - rewrite Map.get_set_other by (assumption || apply PreFrg.phi_encoding_laws; exact Hlaw).
    change (flag
      (fold_right (fun k result => Map.set (PreFrg.phi_encoding c) k
        ((if use_base then flag base k else true) && negb (reset_member p reset k)) result)
        Map.empty rest) k =
      ((if use_base then flag base k else true) && negb (reset_member p reset k))).
    apply IH. destruct Hin as [Heq|Hin]; [congruence|exact Hin].
Qed.

(** A named reset complement is true precisely when that name is absent from the query result. *)
Theorem reset_member_complement f which down can k :
  negb (reset_member (arcs f) (reset_closure (arcs f) f which down can) k) = true <->
    ~ reached f which down can (inl k).
Proof.
  split.
  - intros Hnot [id [Hid Hmem]].
    change (negb (match Prepared.id_of (arcs f) (inl k : vertex) with
      | None => false
      | Some id => FinSet.mem positive_encoding id
          (reset_closure (arcs f) f which down can)
      end) = true) in Hnot.
    rewrite Hid, Hmem in Hnot. discriminate.
  - intro Hnone.
    change (negb (match Prepared.id_of (arcs f) (inl k : vertex) with
      | None => false
      | Some id => FinSet.mem positive_encoding id
          (reset_closure (arcs f) f which down can)
      end) = true).
    destruct (Prepared.id_of (arcs f) (inl k : vertex)) as [id|] eqn:Hid;
      [|reflexivity].
    destruct (FinSet.mem positive_encoding id (reset_closure (arcs f) f which down can))
      eqn:Hmember; [|reflexivity].
    exfalso. apply Hnone. exists id. split; assumption.
Qed.

(** The solver equation records its single shared preparation and the three query dependencies. *)
Theorem solve_equation f :
  solve f =
    let p := arcs f in
    let keys := FinSet.elements (PreFrg.phis f) in
    let unsafe := reset_closure p f Down Map.empty Map.empty in
    let down := Cost.value (flags_c p keys Map.empty false unsafe) in
    let unavailable := reset_closure p f Cannot down Map.empty in
    let can := Cost.value (flags_c p keys Map.empty false unavailable) in
    let reset := reset_closure p f Later down can in
    Facts down can (Cost.value (flags_c p keys can true reset)).
Proof.
  reflexivity.
Qed.

(** On canonical raw indexes the computed flags complement all three original least-reset sets. *)
Theorem solve_reset_exact f :
  Pre.laws c ->
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.phis f) ->
  Map.wf (PreFrg.link_encoding c) (PreFrg.operands f) ->
  FinSet.wf (PreFrg.phi_encoding c) (PreFrg.unsafe f) ->
  forall k, FinSet.mem (PreFrg.phi_encoding c) k (PreFrg.phis f) = true ->
    (flag (downsafe (solve f)) k = true <-> ~ down_unsafe f k) /\
    (flag (can_available (solve f)) k = true <->
      ~ cannot f (flag (downsafe (solve f))) k) /\
    (flag (later (solve f)) k = true <->
      flag (can_available (solve f)) k = true /\
      ~ later_reset f (flag (can_available (solve f))) k).
Proof.
  intros Hlaw Hphis Hlinks Hunsafe k Hphi.
  pose proof (proj2 (FinSet.elements_spec _ (PreFrg.phi_encoding_laws c Hlaw) _ _ Hphis)
    Hphi) as Hkey.
  rewrite solve_equation. cbn zeta.
  cbn [downsafe can_available later].
  split; [|split].
  - rewrite flags_get by assumption. cbn [andb].
    rewrite reset_member_complement, down_closure_exact by assumption. reflexivity.
  - rewrite flags_get by assumption. cbn [andb].
    rewrite reset_member_complement, cannot_closure_exact by assumption. reflexivity.
  - rewrite flags_get by assumption.
    rewrite andb_true_iff, reset_member_complement, later_closure_exact by assumption.
    reflexivity.
Qed.

(** The same law-supported FRG producer yields exact down-safe, can-available and later flags. *)
Theorem solve_exact :
  Pre.laws c ->
  let f := PreOperands.build_frg c in
  forall k, FinSet.mem (PreFrg.phi_encoding c) k (PreFrg.phis f) = true ->
    (flag (downsafe (solve f)) k = true <-> ~ down_unsafe f k) /\
    (flag (can_available (solve f)) k = true <->
      ~ cannot f (flag (downsafe (solve f))) k) /\
    (flag (later (solve f)) k = true <->
      flag (can_available (solve f)) k = true /\
      ~ later_reset f (flag (can_available (solve f))) k).
Proof.
  intro Hlaw.
  destruct (PreOperands.build_frg_indexes_wf c) as [_ [_ [Hphis [Hlinks Hunsafe]]]].
  apply solve_reset_exact; assumption.
Qed.

(** Relative accounting charges preparation once and retains every query and materialisation cost. *)
Theorem solve_ticks f :
  let p := arcs f in
  let keys := FinSet.elements (PreFrg.phis f) in
  let unsafe := reset_closure p f Down Map.empty Map.empty in
  let down := Cost.value (flags_c p keys Map.empty false unsafe) in
  let unavailable := reset_closure p f Cannot down Map.empty in
  let can := Cost.value (flags_c p keys Map.empty false unavailable) in
  let reset := reset_closure p f Later down can in
  Cost.ticks (solve_c f) =
    (Cost.ticks (arcs_c f) + Cost.ticks (FinSet.elements_c (PreFrg.phis f)) +
      Cost.ticks (reset_closure_c p f Down Map.empty Map.empty) +
      Cost.ticks (flags_c p keys Map.empty false unsafe) +
      Cost.ticks (reset_closure_c p f Cannot down Map.empty) +
      Cost.ticks (flags_c p keys Map.empty false unavailable) +
      Cost.ticks (reset_closure_c p f Later down can) +
      Cost.ticks (flags_c p keys can true reset))%N.
Proof.
  cbn zeta. unfold solve_c. rewrite !Cost.ticks_bind, Cost.ticks_ret.
  fold (arcs f). fold (FinSet.elements (PreFrg.phis f)).
  fold (reset_closure (arcs f) f Down Map.empty Map.empty).
  fold (reset_closure (arcs f) f Cannot
    (Cost.value (flags_c (arcs f) (FinSet.elements (PreFrg.phis f)) Map.empty false
      (reset_closure (arcs f) f Down Map.empty Map.empty))) Map.empty).
  fold (reset_closure (arcs f) f Later
    (Cost.value (flags_c (arcs f) (FinSet.elements (PreFrg.phis f)) Map.empty false
      (reset_closure (arcs f) f Down Map.empty Map.empty)))
    (Cost.value (flags_c (arcs f) (FinSet.elements (PreFrg.phis f)) Map.empty false
      (reset_closure (arcs f) f Cannot
        (Cost.value (flags_c (arcs f) (FinSet.elements (PreFrg.phis f)) Map.empty false
          (reset_closure (arcs f) f Down Map.empty Map.empty))) Map.empty)))).
  lia.
Qed.

(** Incidence construction pays the stored-link enumeration and both copied arc cells. *)
Theorem incidence_ticks f :
  Cost.ticks (incidence_c f) =
    (Cost.ticks (Map.elements_c (PreFrg.operands f)) +
      fold_right (fun binding n => 2 + N.of_nat (length (link_arcs binding)) + n)
        0 (Map.elements (PreFrg.operands f)))%N.
Proof.
  unfold incidence_c. rewrite Cost.ticks_bind.
  fold (Map.elements (PreFrg.operands f)).
  rewrite (ticks_fold_right_c_sum _
    (fun binding => (1 + N.of_nat (length (link_arcs binding)))%N)).
  - f_equal. induction (Map.elements (PreFrg.operands f)); cbn [fold_right];
      rewrite ?IHl; lia.
  - intros binding rest. autorewrite with galois_cost. lia.
Qed.

(** An operand contributes its user arc and at most one selected-phi arc. *)
Theorem link_arcs_length binding :
  (length (link_arcs binding) <= 2)%nat.
Proof.
  destruct binding as [key [version real]]. destruct version;
    cbn [link_arcs PreFrg.operand_version length]; lia.
Qed.

(** Arc inventory is canonical enumeration of the single incidence pass. *)
Theorem edge_inventory_equation f :
  edge_inventory f = FinSet.elements (FinSet.of_list arc_encoding (incidence f)).
Proof.
  reflexivity.
Qed.

(** Node inventory canonicalises source sites, unsafe seeds and both incidence endpoints. *)
Theorem node_inventory_equation f :
  node_inventory f = FinSet.elements (FinSet.of_list vertex_encoding
    (map (fun k => inl k : vertex)
      (FinSet.elements (PreFrg.phis f) ++ FinSet.elements (PreFrg.unsafe f)) ++
      flat_map (fun ab => [fst ab; snd ab]) (edge_inventory f))).
Proof.
  reflexivity.
Qed.

(** Graph setup exposes all canonicalisation, enumeration, copying and indexing charges. *)
Theorem graph_ticks f :
  let raw := incidence f in
  let edge_set := FinSet.of_list arc_encoding raw in
  let es := FinSet.elements edge_set in
  let phis := FinSet.elements (PreFrg.phis f) in
  let unsafe := FinSet.elements (PreFrg.unsafe f) in
  let all := map (fun k => inl k : vertex) (phis ++ unsafe) ++
    flat_map (fun ab => [fst ab; snd ab]) es in
  let node_set := FinSet.of_list vertex_encoding all in
  Cost.ticks (graph_c f) =
    (Cost.ticks (incidence_c f) + Cost.ticks (FinSet.of_list_c arc_encoding raw) +
      Cost.ticks (FinSet.elements_c edge_set) + N.of_nat (length es) +
      Cost.ticks (FinSet.elements_c (PreFrg.phis f)) +
      Cost.ticks (FinSet.elements_c (PreFrg.unsafe f)) + N.of_nat (length phis) +
      2 * N.of_nat (length (phis ++ unsafe)) +
      Cost.ticks (FinSet.of_list_c vertex_encoding all) +
      Cost.ticks (FinSet.elements_c node_set) +
      Cost.ticks (Index.group_by_c vertex_encoding
        (Cost.lift (fun _ => 1%N) (@fst vertex vertex)) es))%N.
Proof.
  assert (Hends : forall es, Cost.ticks (endpoints_c es) = N.of_nat (length es)).
  { intro es. unfold endpoints_c.
    rewrite (ticks_fold_right_c_sum _ (fun _ => 0%N)) by (intros; reflexivity).
    induction es; cbn [fold_right length]; rewrite ?Nat2N.inj_succ, ?IHes; lia. }
  assert (Hnames : forall ks,
    Cost.ticks (map_c (fun k => Cost.ret (inl k : vertex)) ks) = N.of_nat (length ks)).
  { intro ks. rewrite ticks_map_c.
    induction ks; cbn [fold_right length]; rewrite ?Nat2N.inj_succ, ?IHks;
      autorewrite with galois_cost; lia. }
  cbn zeta. unfold graph_c. rewrite !Cost.ticks_bind, Cost.ticks_ret, Hends.
  fold (incidence f).
  fold (FinSet.of_list arc_encoding (incidence f)).
  fold (FinSet.elements (FinSet.of_list arc_encoding (incidence f))).
  rewrite endpoints_equation.
  fold (FinSet.elements (PreFrg.phis f)).
  fold (FinSet.elements (PreFrg.unsafe f)).
  rewrite value_app_c, value_map_c, !value_app_c, !ticks_app_c, Hnames, length_map.
  cbn [Cost.value Cost.ret].
  fold (FinSet.of_list vertex_encoding
    (map (fun k => inl k : vertex)
      (FinSet.elements (PreFrg.phis f) ++ FinSet.elements (PreFrg.unsafe f)) ++
      flat_map (fun ab => [fst ab; snd ab])
        (FinSet.elements (FinSet.of_list arc_encoding (incidence f))))).
  repeat rewrite N.add_assoc.
  rewrite !N.add_0_r.
  f_equal. f_equal. f_equal.
  assert (Htwice : forall n : BinNums.N, (2 * n = n + n)%N) by (intro n; lia).
  rewrite Htwice, N.add_assoc. reflexivity.
Qed.

(** Shared preparation adds only the public preparation call after graph setup. *)
Theorem arcs_ticks f :
  Cost.ticks (arcs_c f) =
    (Cost.ticks (graph_c f) + Cost.ticks (Prepared.prepare_c vertex_encoding (graph f)))%N.
Proof.
  unfold arcs_c. rewrite Cost.ticks_bind. reflexivity.
Qed.

(** Flag reads retain the underlying primitive map-lookup charge. *)
Theorem flag_ticks m k :
  Cost.ticks (flag_c m k) = Cost.ticks (Map.get_c (PreFrg.phi_encoding c) k m).
Proof.
  unfold flag_c. apply Map.find_or_cost.
Qed.

(** Query admission charges only a site flag read or the indexed operand read. *)
Theorem admits_ticks f which down can v :
  Cost.ticks (admits_c f which down can v) =
    match v, which with
    | inl _, Down | inr _, Later => 0%N
    | inl k, Cannot => Cost.ticks (flag_c down k)
    | inl k, Later => Cost.ticks (flag_c can k)
    | inr key, _ => Cost.ticks (Map.get_c (PreFrg.link_encoding c) key (PreFrg.operands f))
    end.
Proof.
  destruct v, which; unfold admits_c; autorewrite with galois_cost;
    rewrite ?N.add_0_r; reflexivity.
Qed.

(** Scope construction pays every admission test and canonicalises only the denied dense IDs. *)
Theorem scope_ticks p f which down can :
  let denied := filter_map (fun v => Cost.value
    (Cost.step ;; let* keep := admits_c f which down can v in
      if keep then Cost.ret None else Prepared.id_of_c p v))
      (Graph.nodes (Prepared.graph p)) in
  Cost.ticks (scope_c p f which down can) =
    (fold_right (fun v n => 2 + Cost.ticks (admits_c f which down can v) +
      (if admits f which down can v then 0 else Cost.ticks (Prepared.id_of_c p v)) + n)
      0 (Graph.nodes (Prepared.graph p)) +
      Cost.ticks (FinSet.of_list_c positive_encoding denied))%N.
Proof.
  cbn zeta. unfold scope_c. rewrite !Cost.ticks_bind, Cost.ticks_ret, value_filter_map_c.
  rewrite N.add_0_r.
  rewrite ticks_filter_map_c. f_equal.
  induction (Graph.nodes (Prepared.graph p)) as [|v rest IH]; [reflexivity|].
  cbn [fold_right]. rewrite !Cost.ticks_bind.
  fold (admits f which down can v).
  destruct (admits f which down can v); autorewrite with galois_cost; lia.
Qed.

(** Query composition retains seed conversion, scoped search and the zero-copy orientation view. *)
Theorem reset_closure_ticks p f which down can :
  let roots := seeds f which down can in
  let named := map (fun k => inl k : vertex) roots in
  let ids := Prepared.present (Prepared.id_of p) named in
  Cost.ticks (reset_closure_c p f which down can) =
    (Cost.ticks (seeds_c f which down can) + N.of_nat (length roots) +
      Cost.ticks (Prepared.present_c (Prepared.id_of_c p) named) +
      Cost.ticks (scope_c p f which down can) + Cost.ticks (directed_c p which) +
      Cost.ticks (SearchRun.run_c (directed p which) Visitor.noop
        (scope p f which down can) ids tt))%N.
Proof.
  assert (Hnames : forall ks,
    Cost.ticks (map_c (fun k => Cost.ret (inl k : vertex)) ks) = N.of_nat (length ks)).
  { intro ks. rewrite ticks_map_c.
    induction ks; cbn [fold_right length]; rewrite ?Nat2N.inj_succ, ?IHks;
      autorewrite with galois_cost; lia. }
  cbn zeta. unfold reset_closure_c. rewrite !Cost.ticks_bind, Cost.ticks_ret.
  fold (seeds f which down can). rewrite value_map_c, Hnames, Prepared.present_c_value.
  repeat rewrite N.add_assoc. rewrite N.add_0_r.
  reflexivity.
Qed.

(** Seed callbacks charge the relevant flag read only after the original operand guard passes. *)
Theorem seed_ticks which down can binding :
  let '(key, op) := binding in
  Cost.ticks (seed_c which down can binding) =
    match which, PreFrg.operand_version op with
    | Cannot, PreFrg.Unavailable _ => Cost.ticks (flag_c down (fst key))
    | Later, PreFrg.Unavailable _ => 0%N
    | Later, _ => if PreFrg.real_use op then Cost.ticks (flag_c can (fst key)) else 0%N
    | _, _ => 0%N
    end.
Proof.
  destruct binding as [key [version real]]. destruct which, version, real;
    unfold seed_c; cbn [PreFrg.operand_version PreFrg.real_use fst];
    autorewrite with galois_cost; reflexivity.
Qed.

(** Seed enumeration retains the map traversal, predicate calls and successful key copying. *)
Theorem seeds_ticks f which down can :
  Cost.ticks (seeds_c f which down can) =
    match which with
    | Down => Cost.ticks (FinSet.elements_c (PreFrg.unsafe f))
    | _ => (Cost.ticks (Map.elements_c (PreFrg.operands f)) +
        fold_right (fun binding n => 1 + Cost.ticks (seed_c which down can binding) + n)
          0 (Map.elements (PreFrg.operands f)) +
        N.of_nat (length (filter
          (fun binding => Cost.value (seed_c which down can binding))
          (Map.elements (PreFrg.operands f)))))%N
    end.
Proof.
  assert (Hcopy : forall bs : list (((B * U) * BE) * PreFrg.operand B E U),
    Cost.ticks (map_c (fun binding => Cost.ret (fst (fst binding))) bs) =
      N.of_nat (length bs)).
  { intro bs. rewrite ticks_map_c.
    induction bs; cbn [fold_right length]; rewrite ?Nat2N.inj_succ, ?IHbs;
      autorewrite with galois_cost; lia. }
  destruct which; [reflexivity| |].
  all: unfold seeds_c; rewrite !Cost.ticks_bind, Hcopy, value_filter_c, ticks_filter_c.
  all: rewrite N.add_assoc; reflexivity.
Qed.

(** Flag materialisation exposes its lookups, dense membership and actual output-key serializer. *)
Theorem flags_ticks p keys base use_base reset :
  Cost.ticks (flags_c p keys base use_base reset) =
    fold_right (fun k n =>
      (2 + Cost.ticks (Prepared.id_of_c p (inl k : vertex)) +
      (match Prepared.id_of p (inl k : vertex) with
       | None => 0
       | Some id => Cost.ticks (FinSet.mem_c positive_encoding id reset)
       end) +
      (if use_base then Cost.ticks (flag_c base k) else 0) +
      Cost.ticks (encode_c (PreFrg.phi_encoding c) k) +
      key_bits (PreFrg.phi_encoding c) k + n)%N) 0 keys.
Proof.
  unfold flags_c.
  rewrite (ticks_fold_right_c_sum _ (fun k =>
    (1 + Cost.ticks (Prepared.id_of_c p (inl k : vertex)) +
      (match Prepared.id_of p (inl k : vertex) with
       | None => 0
       | Some id => Cost.ticks (FinSet.mem_c positive_encoding id reset)
       end) +
      (if use_base then Cost.ticks (flag_c base k) else 0) +
      Cost.ticks (encode_c (PreFrg.phi_encoding c) k) +
      key_bits (PreFrg.phi_encoding c) k)%N)).
  - induction keys; cbn [fold_right]; rewrite ?IHkeys; lia.
  - intros k result. rewrite !Cost.ticks_bind, Map.set_cost.
    fold (Prepared.id_of p (inl k : vertex)).
    destruct (Prepared.id_of p (inl k : vertex)), use_base;
      autorewrite with galois_cost;
      fold (key_bits (PreFrg.phi_encoding c) k); lia.
Qed.

(** Query orientation exchanges existing indexes and converts no exit entries. *)
Theorem directed_ticks p which :
  Cost.ticks (directed_c p which) = 0%N.
Proof.
  destruct which; [|reflexivity|reflexivity].
  unfold directed_c. rewrite Prepared.reverse_c_equation. reflexivity.
Qed.

End Context.

End PreReset.
