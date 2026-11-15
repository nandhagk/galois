(** * Checked widening schedules

    This file constructs schedules from dependency graphs and checked WTOs.
    For example, a self-dependency requires its target to be a widening head.
    Builds on: Fixpoint.ScheduleSig, Fixpoint.PolicySig and Graph.WtoSig. *)

From Stdlib Require Import List PArith Arith NArith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Graph Require Import Data Spec DigraphSig WtoSig.
From Galois.Fixpoint Require Import SystemSig PolicySig ScheduleSig.

(** Setting a trie binding changes exactly the selected key. *)
Lemma schedule_get_set {A} (u v : positive) (a : A) m :
  trie_get u (PTrieCode.set v a m) =
    if Pos.eqb u v then Some a else trie_get u m.
Proof.
  destruct (Pos.eqb u v) eqn:Heq.
  - apply Pos.eqb_eq in Heq; subst u; apply PTrie.get_set_same.
  - apply Pos.eqb_neq in Heq; apply PTrie.get_set_other; exact Heq.
Qed.

(** A consistent inventory lists each key recognized by the seen map once. *)
Definition schedule_inventory (st : schedule_graph_state) : Prop :=
  NoDup (schedule_vertices st) /\
  forall v, trie_get v (schedule_seen st) <> None <-> In v (schedule_vertices st).

(** State adjacency uses the same empty-list convention as graph successors. *)
Definition schedule_adj (st : schedule_graph_state) (u : positive) : list positive :=
  match trie_get u (schedule_successors st) with Some vs => vs | None => nil end.

(** Inserting a vertex preserves the inventory and adds exactly that vertex. *)
Lemma schedule_vertex_correct st x : schedule_inventory st ->
  schedule_inventory (schedule_vertex x st) /\
  (forall v, In v (schedule_vertices (schedule_vertex x st)) <->
    v = x \/ In v (schedule_vertices st)) /\
  schedule_successors (schedule_vertex x st) = schedule_successors st.
Proof.
  destruct st as [vs seen adjacency]; intros [Hnodup Hseen].
  cbn [schedule_vertex schedule_vertices schedule_seen schedule_successors] in *.
  destruct (trie_get x seen) as [b|] eqn:Hx.
  - assert (Hin : In x vs) by (apply Hseen; rewrite Hx; discriminate).
    split; [split; assumption|].
    split; [intro v; split; [auto|intros [->|Hv]; assumption]|reflexivity].
  - assert (Hnotin : ~ In x vs) by (intro Hin; apply (proj2 (Hseen x) Hin); exact Hx).
    split.
    + split; [constructor; assumption|]. intro v.
      cbn [schedule_vertices schedule_seen]. rewrite schedule_get_set.
      destruct (Pos.eqb v x) eqn:Hvx.
      * apply Pos.eqb_eq in Hvx; subst v; split; [intro; now left|discriminate].
      * apply Pos.eqb_neq in Hvx; rewrite Hseen; cbn; intuition congruence.
    + split; [intro v; cbn; intuition congruence|reflexivity].
Qed.

(** A list of vertex insertions preserves adjacency and adds its listed keys. *)
Lemma schedule_vertices_correct xs st : schedule_inventory st ->
  schedule_inventory (fold_left (fun acc v => schedule_vertex v acc) xs st) /\
  (forall v,
    In v (schedule_vertices (fold_left (fun acc v => schedule_vertex v acc) xs st)) <->
    In v xs \/ In v (schedule_vertices st)) /\
  schedule_successors (fold_left (fun acc v => schedule_vertex v acc) xs st) =
    schedule_successors st.
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hinv.
  - cbn; split; [exact Hinv|]. split; [intro v; tauto|reflexivity].
  - cbn [fold_left].
    destruct (schedule_vertex_correct st x Hinv) as [Hnext [Hmembers Hadj]].
    destruct (IH _ Hnext) as [Hfinal [Hfinalmembers Hfinaladj]].
    split; [exact Hfinal|]. split.
    + intro v; rewrite Hfinalmembers, Hmembers; cbn; intuition congruence.
    + now rewrite Hfinaladj, Hadj.
Qed.

(** An edge insertion preserves the inventory and prepends one adjacency occurrence. *)
Lemma schedule_edge_correct st u v :
  schedule_inventory st -> schedule_inventory (schedule_edge u v st) /\
  schedule_vertices (schedule_edge u v st) = schedule_vertices st /\
  forall x y, In y (schedule_adj (schedule_edge u v st) x) <->
    (x = u /\ y = v) \/ In y (schedule_adj st x).
Proof.
  destruct st as [vs seen adjacency]; intro Hinv.
  split; [exact Hinv|]. split; [reflexivity|]. intros x y.
  unfold schedule_edge, schedule_adj; cbn [schedule_successors].
  rewrite schedule_get_set. destruct (Pos.eqb x u) eqn:Hxu.
  - apply Pos.eqb_eq in Hxu; subst x; cbn; intuition congruence.
  - apply Pos.eqb_neq in Hxu; tauto.
Qed.

(** Inserting all writes of one read adds precisely that row of the edge product. *)
Lemma schedule_writes_correct writes st u : schedule_inventory st ->
  schedule_inventory (fold_left (fun acc v => schedule_edge u v acc) writes st) /\
  schedule_vertices (fold_left (fun acc v => schedule_edge u v acc) writes st) =
    schedule_vertices st /\
  forall x y,
    In y (schedule_adj (fold_left (fun acc v => schedule_edge u v acc) writes st) x) <->
    (x = u /\ In y writes) \/ In y (schedule_adj st x).
Proof.
  revert st; induction writes as [|v writes IH]; intros st Hinv.
  - cbn; split; [exact Hinv|]. split; [reflexivity|intros x y; tauto].
  - cbn [fold_left].
    destruct (schedule_edge_correct st u v Hinv) as [Hnext [Hvertices Hedges]].
    destruct (IH _ Hnext) as [Hfinal [Hfinalvertices Hfinaledges]].
    split; [exact Hfinal|]. split.
    + now rewrite Hfinalvertices, Hvertices.
    + intros x y; rewrite Hfinaledges, Hedges; cbn; intuition congruence.
Qed.

(** Inserting a dependency product preserves the inventory and adds its edges. *)
Lemma schedule_product_correct reads writes st : schedule_inventory st ->
  schedule_inventory
    (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
      reads st) /\
  schedule_vertices
    (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
      reads st) = schedule_vertices st /\
  forall x y,
    In y (schedule_adj
      (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
        reads st) x) <->
    (In x reads /\ In y writes) \/ In y (schedule_adj st x).
Proof.
  revert st; induction reads as [|u reads IH]; intros st Hinv.
  - cbn; split; [exact Hinv|]. split; [reflexivity|intros x y; tauto].
  - cbn [fold_left].
    destruct (schedule_writes_correct writes st u Hinv) as [Hnext [Hvertices Hedges]].
    destruct (IH _ Hnext) as [Hfinal [Hfinalvertices Hfinaledges]].
    split; [exact Hfinal|]. split.
    + now rewrite Hfinalvertices, Hvertices.
    + intros x y; rewrite Hfinaledges, Hedges; cbn; intuition congruence.
Qed.

(** A row adds its declared vertices and exactly its read-to-write edge product. *)
Lemma schedule_row_correct {R K} (code : K -> positive) target deps sides (r : R) st :
  schedule_inventory st ->
  schedule_inventory (schedule_graph_row code target deps sides st r) /\
  (forall c, In c (schedule_vertices (schedule_graph_row code target deps sides st r)) <->
    In c (map code ((target r :: sides r) ++ deps r)) \/
      In c (schedule_vertices st)) /\
  forall u v, In v (schedule_adj (schedule_graph_row code target deps sides st r) u) <->
    (In u (map code (deps r)) /\ In v (map code (target r :: sides r))) \/
      In v (schedule_adj st u).
Proof.
  intro Hinv; unfold schedule_graph_row.
  destruct (schedule_vertices_correct
    (map code (target r :: sides r) ++ map code (deps r)) st Hinv)
    as [Hlisted [Hvertices Hadj]].
  destruct (schedule_product_correct (map code (deps r))
    (map code (target r :: sides r)) _ Hlisted) as [Hfinal [Hfinalvertices Hedges]].
  split; [exact Hfinal|]. split.
  - intro c; rewrite Hfinalvertices, Hvertices, map_app; reflexivity.
  - intros u v; rewrite Hedges; unfold schedule_adj; now rewrite Hadj.
Qed.

(** Folding rows preserves distinct vertices and accumulates their declared graph. *)
Lemma schedule_rows_correct {R K} (code : K -> positive) target deps sides (rows : list R) st :
  schedule_inventory st ->
  schedule_inventory (fold_left (schedule_graph_row code target deps sides) rows st) /\
  (forall c,
    In c (schedule_vertices (fold_left (schedule_graph_row code target deps sides) rows st)) <->
    (exists r, In r rows /\ In c (map code ((target r :: sides r) ++ deps r))) \/
      In c (schedule_vertices st)) /\
  forall u v,
    In v (schedule_adj (fold_left (schedule_graph_row code target deps sides) rows st) u) <->
    (exists r, In r rows /\ In u (map code (deps r)) /\
      In v (map code (target r :: sides r))) \/ In v (schedule_adj st u).
Proof.
  revert st; induction rows as [|r rows IH]; intros st Hinv.
  - cbn; split; [exact Hinv|]. split.
    + intro c; split; [auto|intros [[r [Hnil _]]|Hin]; [contradiction|exact Hin]].
    + intros u v; split; [auto|intros [[r [Hnil _]]|Hin]; [contradiction|exact Hin]].
  - cbn [fold_left].
    destruct (schedule_row_correct code target deps sides r st Hinv)
      as [Hnext [Hvertices Hedges]].
    destruct (IH _ Hnext) as [Hfinal [Hfinalvertices Hfinaledges]].
    split; [exact Hfinal|]. split.
    + intro c; rewrite Hfinalvertices, Hvertices; split.
      * intros [[q [Hq Hc]]|[Hc|Hc]].
        -- left; exists q; split; [now right|exact Hc].
        -- left; exists r; split; [now left|exact Hc].
        -- now right.
      * intros [[q [[Hq|Hq] Hc]]|Hc].
        -- subst q; right; now left.
        -- left; exists q; auto.
        -- right; now right.
    + intros u v; rewrite Hfinaledges, Hedges; split.
      * intros [[q [Hq [Hu Hv]]]|[[Hu Hv]|Hold]].
        -- left; exists q; split; [now right|auto].
        -- left; exists r; split; [now left|auto].
        -- now right.
      * intros [[q [[Hq|Hq] [Hu Hv]]]|Hold].
        -- subst q; right; left; auto.
        -- left; exists q; auto.
        -- right; now right.
Qed.

(** Empty graph construction starts with a consistent inventory. *)
Lemma schedule_empty_inventory : schedule_inventory (ScheduleGraphState nil Empty Empty).
Proof.
  split; [constructor|]. intro v; cbn [schedule_seen schedule_vertices].
  rewrite PTrie.get_empty; tauto.
Qed.

(** Constructed graph vertices are distinct and list every declared key. *)
Lemma schedule_graph_vertices {R K} (code : K -> positive) target deps sides (rows : list R) :
  NoDup (verts (schedule_graph code target deps sides rows)) /\
  forall c, In c (verts (schedule_graph code target deps sides rows)) <->
    exists r x, In r rows /\ In x ((target r :: sides r) ++ deps r) /\ code x = c.
Proof.
  pose proof (schedule_rows_correct code target deps sides rows
    (ScheduleGraphState nil Empty Empty) schedule_empty_inventory)
    as [[Hnodup Hseen] [Hvertices Hedges]].
  unfold schedule_graph.
  destruct (fold_left (schedule_graph_row code target deps sides) rows
    (ScheduleGraphState nil Empty Empty)) as [vs seen adjacency].
  cbn [schedule_vertices verts] in *; rewrite <- rev_alt.
  split; [now apply NoDup_rev|]. intro c; rewrite <- in_rev, Hvertices.
  split.
  - intros [[r [Hr Hmap]]|Hnil]; [|contradiction].
    apply in_map_iff in Hmap as [x [Hcode Hx]]. exists r, x; auto.
  - intros [r [x [Hr [Hx Hcode]]]]. left; exists r; split; [exact Hr|].
    apply in_map_iff; exists x; auto.
Qed.

(** Constructed graph adjacency contains exactly the declared edge products. *)
Lemma schedule_graph_edges {R K} (code : K -> positive) target deps sides (rows : list R) u v :
  edge (schedule_graph code target deps sides rows) u v <->
    exists r x y, In r rows /\ In x (deps r) /\ In y (target r :: sides r) /\
      code x = u /\ code y = v.
Proof.
  pose proof (schedule_rows_correct code target deps sides rows
    (ScheduleGraphState nil Empty Empty) schedule_empty_inventory) as [_ [_ Hedges]].
  unfold schedule_graph, edge, succs.
  destruct (fold_left (schedule_graph_row code target deps sides) rows
    (ScheduleGraphState nil Empty Empty)) as [vs seen adjacency].
  change (In v (schedule_adj (ScheduleGraphState vs seen adjacency) u) <->
    exists r x y, In r rows /\ In x (deps r) /\ In y (target r :: sides r) /\
      code x = u /\ code y = v).
  rewrite Hedges; unfold schedule_adj; cbn [schedule_successors].
  rewrite PTrie.get_empty; cbn.
  split.
  - intros [[r [Hr [Hu Hv]]]|Hnil]; [|contradiction].
    apply in_map_iff in Hu as [x [Hx Hread]].
    change (In v (map code (target r :: sides r))) in Hv.
    apply in_map_iff in Hv as [y [Hy Hwrite]]. exists r, x, y; auto.
  - intros [r [x [y [Hr [Hread [Hwrite [Hx Hy]]]]]]].
    left; exists r; split; [exact Hr|]. split.
    + apply in_map_iff; exists x; auto.
    + change (In v (map code (target r :: sides r))).
      apply in_map_iff; exists y; auto.
Qed.

(** Folding a uniform head configuration overwrites exactly the listed keys. *)
Lemma schedule_head_fold (cfg : head_cfg) vs m c :
  trie_get c (fold_left (fun acc v => PTrieCode.set v cfg acc) vs m) =
    if existsb (Pos.eqb c) vs then Some cfg else trie_get c m.
Proof.
  revert m; induction vs as [|v vs IH]; intro m; [reflexivity|].
  cbn [fold_left existsb]; rewrite IH, schedule_get_set.
  destruct (Pos.eqb c v), (existsb (Pos.eqb c) vs); reflexivity.
Qed.

(** Updating the largest read rank preserves exactly its strict upper bounds. *)
Lemma schedule_rank_step_below (best : option positive) rank bound :
  (match (match best with
    | None => Some rank
    | Some old => Some (if Pos.ltb old rank then rank else old)
    end) with
   | None => True
   | Some current => (current < bound)%positive
   end) <->
  (match best with None => True | Some old => (old < bound)%positive end) /\
    (rank < bound)%positive.
Proof.
  destruct best as [old|]; [|tauto].
  destruct (Pos.ltb old rank) eqn:Hlt.
  - apply Pos.ltb_lt in Hlt; split; [intro H; split; [lia|exact H]|tauto].
  - apply Pos.ltb_ge in Hlt; split; [intro H; split; [exact H|lia]|tauto].
Qed.

(** The maximum-read fold has precisely the common strict upper bounds of its inputs. *)
Lemma schedule_read_fold_below {A} (pol : policy A) reads best bound :
  (match fold_left
    (fun acc v => let rank := schedule_priority pol v in
      match acc with
      | None => Some rank
      | Some old => Some (if Pos.ltb old rank then rank else old)
      end) reads best with
   | None => True
   | Some rank => (rank < bound)%positive
   end) <->
  (match best with None => True | Some rank => (rank < bound)%positive end) /\
    (forall v, In v reads -> (schedule_priority pol v < bound)%positive).
Proof.
  revert best; induction reads as [|v reads IH]; intro best.
  - cbn; tauto.
  - cbn [fold_left]; rewrite IH, schedule_rank_step_below; split.
    + intros [[Hbest Hv] Htail]; split; [exact Hbest|].
      intros x [<-|Hx]; [exact Hv|now apply Htail].
    + intros [Hbest Hall]; split.
      * split; [exact Hbest|apply Hall; now left].
      * intros x Hx; apply Hall; now right.
Qed.

(** Read-rank comparison is equivalent to comparing every declared read. *)
Lemma schedule_read_rank_below {A} (pol : policy A) reads bound :
  (match schedule_read_rank pol reads with
   | None => True
   | Some rank => (rank < bound)%positive
   end) <-> forall v, In v reads -> (schedule_priority pol v < bound)%positive.
Proof.
  unfold schedule_read_rank; rewrite schedule_read_fold_below; tauto.
Qed.

(** A write passes exactly when its rank exceeds the read maximum or it is a head. *)
Lemma schedule_write_cut_spec {A} (pol : policy A) rank v :
  schedule_write_cut pol rank v = true <->
    (rank < schedule_priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
Proof.
  unfold schedule_write_cut.
  destruct (Pos.ltb rank (schedule_priority pol v)) eqn:Hlt.
  - apply Pos.ltb_lt in Hlt; tauto.
  - apply Pos.ltb_ge in Hlt.
    destruct (trie_get v (heads pol)) as [cfg|] eqn:Hhead.
    + split; [intro; right; eauto|reflexivity].
    + split; [discriminate|intros [Hrank|[cfg Hcfg]]; [lia|discriminate]].
Qed.

(** Row checking is equivalent to checking every dependency-to-write pair. *)
Lemma schedule_cut_row_spec {R K A} (code : K -> positive) target deps sides
    (pol : policy A) (r : R) :
  schedule_cut_row code target deps sides pol r = true <->
    forall x y, In x (deps r) -> In y (target r :: sides r) ->
      (schedule_priority pol (code x) < schedule_priority pol (code y))%positive \/
      exists cfg, trie_get (code y) (heads pol) = Some cfg.
Proof.
  unfold schedule_cut_row.
  destruct (schedule_read_rank pol (map code (deps r))) as [rank|] eqn:Hrank.
  - rewrite forallb_forall.
    split.
    + intros Hcuts x y Hx Hy.
      specialize (Hcuts y Hy); apply schedule_write_cut_spec in Hcuts.
      destruct Hcuts as [Hlt|Hhead]; [left|now right].
      pose proof (proj1 (schedule_read_rank_below pol (map code (deps r))
        (schedule_priority pol (code y)))) as Hbelow.
      rewrite Hrank in Hbelow; apply Hbelow; [exact Hlt|now apply in_map].
    + intros Hcuts y Hy; apply schedule_write_cut_spec.
      destruct (trie_get (code y) (heads pol)) as [cfg|] eqn:Hhead; [right; eauto|].
      left.
      pose proof (proj2 (schedule_read_rank_below pol (map code (deps r))
        (schedule_priority pol (code y)))) as Hbelow.
      rewrite Hrank in Hbelow; apply Hbelow.
      intros v Hvin; apply in_map_iff in Hvin as [x [<- Hx]].
      destruct (Hcuts x y Hx Hy) as [Hlt|[cfg Hcfg]]; [exact Hlt|congruence].
  - split; [intros _ x y Hx Hy|reflexivity].
    left.
    pose proof (proj1 (schedule_read_rank_below pol (map code (deps r))
      (schedule_priority pol (code y)))) as Hbelow.
    rewrite Hrank in Hbelow; apply Hbelow; [exact I|now apply in_map].
Qed.

(** The graph's structural maximum agrees with the natural maximum. *)
Lemma schedule_max_eq a b : graph_max a b = Nat.max a b.
Proof.
  revert b; induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
Qed.

(** Pointwise bounds on encoded vertices bound their maximum width. *)
Lemma schedule_vertex_width_le vs width :
  (forall v, In v vs -> Pos.size_nat v <= width) -> vertex_width vs <= width.
Proof.
  unfold vertex_width; induction vs as [|v vs IH]; intro Hbound; [cbn; lia|].
  cbn [fold_right]; rewrite schedule_max_eq; apply Nat.max_lub.
  - apply Hbound; now left.
  - apply IH; intros u Hu; apply Hbound; now right.
Qed.

(** Every element's width is bounded by the maximum width of its list. *)
Lemma schedule_vertex_width_member vs v : In v vs -> Pos.size_nat v <= vertex_width vs.
Proof.
  unfold vertex_width; induction vs as [|u vs IH]; intro Hin; [contradiction|].
  cbn [fold_right]; rewrite schedule_max_eq.
  destruct Hin as [<-|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Pointwise bounds survive a fold of structural maxima. *)
Lemma schedule_width_fold_le (f : positive -> nat) vs width :
  (forall v, In v vs -> f v <= width) ->
  fold_right (fun v w => graph_max (f v) w) 0 vs <= width.
Proof.
  induction vs as [|v vs IH]; intro Hbound; [cbn; lia|].
  cbn [fold_right]; rewrite schedule_max_eq; apply Nat.max_lub.
  - apply Hbound; now left.
  - apply IH; intros u Hu; apply Hbound; now right.
Qed.

(** A well-formed graph with bounded listed keys has bounded vertex and edge identifiers. *)
Lemma schedule_graph_width_le g width : wf_graph g ->
  (forall v, In v (verts g) -> Pos.size_nat v <= width) -> graph_width g <= width.
Proof.
  intros [_ Hclosed] Hbound; destruct g as [vs adjacency].
  unfold graph_width; rewrite schedule_max_eq; apply Nat.max_lub.
  - now apply schedule_vertex_width_le.
  - apply schedule_width_fold_le; intros u Hu.
    apply schedule_vertex_width_le; intros v Hv.
    apply Hbound; apply (Hclosed u v); [exact Hu|exact Hv].
Qed.

(** Paths starting at a listed vertex stay in a well-formed graph's inventory. *)
Lemma schedule_path_listed g u vs v : wf_graph g -> path g u vs v ->
  In u (verts g) -> In v (verts g).
Proof.
  intros [_ Hclosed] Hpath; induction Hpath as [u|u v vs w Hedge Hpath IH]; intro Hu.
  - exact Hu.
  - apply IH; eapply Hclosed; eauto.
Qed.

(** Rooting a well-formed graph at all its vertices reaches only listed vertices. *)
Lemma schedule_reach_listed g v : wf_graph g ->
  reach g (verts g) v -> In v (verts g).
Proof.
  intros Hwf [u [vs [Hu Hpath]]]; eapply schedule_path_listed; eauto.
Qed.

(** The source vertex inventory is one part of the graph's width budget. *)
Lemma schedule_graph_vertex_width g : vertex_width (verts g) <= graph_width g.
Proof.
  destruct g as [vs adjacency]; unfold graph_width; cbn [verts].
  rewrite schedule_max_eq; apply Nat.le_max_l.
Qed.

(** Distinct positive keys remain distinct after conversion to natural numbers. *)
Lemma schedule_nat_keys_nodup vs : NoDup vs -> NoDup (map Pos.to_nat vs).
Proof.
  intro Hnodup; induction Hnodup as [|v vs Hfresh Hnodup IH]; cbn [map].
  - constructor.
  - constructor; [|exact IH].
    intros Hin; apply in_map_iff in Hin as [u [Heq Hu]].
    apply Pos2Nat.inj in Heq; subst u; contradiction.
Qed.

(** Distinct keys of width at most [width] fit into the corresponding finite range. *)
Lemma schedule_key_count vs width : NoDup vs ->
  (forall v, In v vs -> Pos.size_nat v <= width) -> length vs <= 2 ^ width.
Proof.
  intros Hnodup Hwidth.
  assert (Hincl : incl (map Pos.to_nat vs) (seq 0 (2 ^ width))).
  { intros n Hin; apply in_map_iff in Hin as [v [<- Hv]].
    apply in_seq; split; [lia|].
    eapply Nat.lt_le_trans; [apply Pos.size_nat_upper|].
    apply Nat.pow_le_mono_r; [lia|now apply Hwidth]. }
  pose proof (NoDup_incl_length (schedule_nat_keys_nodup vs Hnodup) Hincl) as Hlen.
  rewrite length_map, length_seq in Hlen; exact Hlen.
Qed.

(** A positive rank within the key population uses at most one extra bit. *)
Lemma schedule_rank_width rank width : Pos.to_nat rank <= 2 ^ width ->
  Pos.size_nat rank <= width + 1.
Proof.
  intro Hbound; apply Pos.size_nat_least.
  assert (Hnonzero : 2 ^ width <> 0) by (apply Nat.pow_nonzero; lia).
  assert (Hpow : 0 < 2 ^ width) by lia.
  replace (width + 1) with (S width) by lia; cbn [Nat.pow]; lia.
Qed.

(** A mapped list maximum inherits every pointwise bound. *)
Lemma schedule_map_max_le {A} (f : A -> nat) xs bound :
  (forall x, In x xs -> f x <= bound) -> fold_right Nat.max 0 (map f xs) <= bound.
Proof.
  induction xs as [|x xs IH]; intro Hbound; [cbn; lia|].
  cbn [map fold_right]; apply Nat.max_lub.
  - apply Hbound; now left.
  - apply IH; intros y Hy; apply Hbound; now right.
Qed.

(** The row occurrence list has exactly the declared aggregate size. *)
Lemma schedule_occurrence_length {R K} (code : K -> positive) target deps sides
    (rows : list R) :
  length (flat_map (fun r => map code ((target r :: sides r) ++ deps r)) rows) =
    fold_right Nat.add 0
      (map (fun r => length (deps r) + length (sides r) + 1) rows).
Proof.
  induction rows as [|r rows IH]; [reflexivity|].
  cbn [flat_map map fold_right]; rewrite length_app, length_map, length_app, IH.
  cbn [length]; lia.
Qed.

(** Summing the listed adjacency lengths counts all retained edge occurrences. *)
Definition schedule_mass_on vs st : nat :=
  fold_right (fun u n => length (schedule_adj st u) + n) 0 vs.

(** No adjacency binding outside the inventory contains an edge occurrence. *)
Definition schedule_supported st : Prop :=
  forall u, ~ In u (schedule_vertices st) -> schedule_adj st u = nil.

(** Edge insertion changes only its source's adjacency list. *)
Lemma schedule_edge_adj st u v x :
  schedule_adj (schedule_edge u v st) x =
    if Pos.eqb x u then v :: schedule_adj st u else schedule_adj st x.
Proof.
  destruct st as [vs seen adjacency]; unfold schedule_edge, schedule_adj.
  cbn [schedule_successors]; rewrite schedule_get_set.
  destruct (Pos.eqb x u); reflexivity.
Qed.

(** An edge outside a source list leaves that list's adjacency mass unchanged. *)
Lemma schedule_mass_edge_outside vs st u v : ~ In u vs ->
  schedule_mass_on vs (schedule_edge u v st) = schedule_mass_on vs st.
Proof.
  induction vs as [|x vs IH]; intro Houtside; [reflexivity|].
  change (length (schedule_adj (schedule_edge u v st) x) +
    schedule_mass_on vs (schedule_edge u v st) =
    length (schedule_adj st x) + schedule_mass_on vs st).
  rewrite schedule_edge_adj.
  assert (Hxu : Pos.eqb x u = false).
  { apply Pos.eqb_neq; intro Heq; subst x; apply Houtside; now left. }
  rewrite Hxu, IH; [reflexivity|intro Hin; apply Houtside; now right].
Qed.

(** One new edge adds one occurrence to the mass over distinct containing sources. *)
Lemma schedule_mass_edge_inside vs st u v : NoDup vs -> In u vs ->
  schedule_mass_on vs (schedule_edge u v st) = S (schedule_mass_on vs st).
Proof.
  intro Hnodup; induction Hnodup as [|x vs Hfresh Hnodup IH]; intro Hin;
    [contradiction|].
  change (length (schedule_adj (schedule_edge u v st) x) +
    schedule_mass_on vs (schedule_edge u v st) =
    S (length (schedule_adj st x) + schedule_mass_on vs st)).
  rewrite schedule_edge_adj.
  destruct Hin as [<-|Hin].
  - rewrite Pos.eqb_refl; cbn [length].
    rewrite schedule_mass_edge_outside by exact Hfresh; reflexivity.
  - assert (Hxu : Pos.eqb x u = false).
    { apply Pos.eqb_neq; intro H; subst x; contradiction. }
    rewrite Hxu, IH by exact Hin; lia.
Qed.

(** Adding a new inventory key preserves support and contributes no old edges. *)
Lemma schedule_vertex_mass st x : schedule_inventory st -> schedule_supported st ->
  schedule_supported (schedule_vertex x st) /\
  schedule_mass_on (schedule_vertices (schedule_vertex x st)) (schedule_vertex x st) =
    schedule_mass_on (schedule_vertices st) st.
Proof.
  intros Hinv Hsupport.
  destruct (schedule_vertex_correct st x Hinv) as [_ [Hvertices Hadj]].
  split.
  - intros u Houtside; unfold schedule_adj; rewrite Hadj; apply Hsupport.
    intro Hin; apply Houtside; apply Hvertices; now right.
  - destruct st as [vs seen adjacency]; cbn [schedule_vertex].
    destruct (trie_get x seen) as [b|] eqn:Hx; [reflexivity|].
    destruct Hinv as [Hnodup Hseen].
    assert (Hnotin : ~ In x vs).
    { intro Hin; apply (proj2 (Hseen x) Hin); exact Hx. }
    specialize (Hsupport x Hnotin).
    unfold schedule_mass_on; cbn [schedule_vertices fold_right].
    change (length (schedule_adj (ScheduleGraphState vs seen adjacency) x) +
      schedule_mass_on vs (ScheduleGraphState vs seen adjacency) =
      schedule_mass_on vs (ScheduleGraphState vs seen adjacency)).
    rewrite Hsupport; reflexivity.
Qed.

(** Listing all keys preserves supported adjacency mass. *)
Lemma schedule_vertices_mass xs st : schedule_inventory st -> schedule_supported st ->
  schedule_supported (fold_left (fun acc v => schedule_vertex v acc) xs st) /\
  schedule_mass_on
    (schedule_vertices (fold_left (fun acc v => schedule_vertex v acc) xs st))
    (fold_left (fun acc v => schedule_vertex v acc) xs st) =
      schedule_mass_on (schedule_vertices st) st.
Proof.
  revert st; induction xs as [|x xs IH]; intros st Hinv Hsupport.
  - split; [exact Hsupport|reflexivity].
  - cbn [fold_left].
    destruct (schedule_vertex_correct st x Hinv) as [Hnext _].
    destruct (schedule_vertex_mass st x Hinv Hsupport) as [Hnextsupport Hmass].
    destruct (IH _ Hnext Hnextsupport) as [Hfinal Hfinalmass].
    split; [exact Hfinal|now rewrite Hfinalmass, Hmass].
Qed.

(** Edges whose sources are listed preserve adjacency support. *)
Lemma schedule_edge_supported st u v : schedule_supported st ->
  In u (schedule_vertices st) -> schedule_supported (schedule_edge u v st).
Proof.
  intros Hsupport Hu x Houtside; rewrite schedule_edge_adj.
  assert (Hvertices : schedule_vertices (schedule_edge u v st) = schedule_vertices st)
    by (destruct st; reflexivity).
  rewrite Hvertices in Houtside.
  destruct (Pos.eqb x u) eqn:Hxu.
  - apply Pos.eqb_eq in Hxu; subst x; contradiction.
  - now apply Hsupport.
Qed.

(** A read's writes add their exact number of adjacency occurrences. *)
Lemma schedule_writes_mass writes st u : schedule_inventory st -> schedule_supported st ->
  In u (schedule_vertices st) ->
  schedule_supported (fold_left (fun acc v => schedule_edge u v acc) writes st) /\
  schedule_mass_on
    (schedule_vertices (fold_left (fun acc v => schedule_edge u v acc) writes st))
    (fold_left (fun acc v => schedule_edge u v acc) writes st) =
      schedule_mass_on (schedule_vertices st) st + length writes.
Proof.
  revert st; induction writes as [|v writes IH]; intros st Hinv Hsupport Hu.
  - cbn [fold_left length]; split; [exact Hsupport|lia].
  - cbn [fold_left length].
    destruct (schedule_edge_correct st u v Hinv) as [Hnext [Hvertices Hedges]].
    assert (Hnextsupport : schedule_supported (schedule_edge u v st))
      by (apply schedule_edge_supported; assumption).
    assert (Hnextu : In u (schedule_vertices (schedule_edge u v st)))
      by (now rewrite Hvertices).
    destruct (IH _ Hnext Hnextsupport Hnextu) as [Hfinal Hmass].
    split; [exact Hfinal|]. rewrite Hmass, Hvertices.
    rewrite schedule_mass_edge_inside; [lia|exact (proj1 Hinv)|exact Hu].
Qed.

(** A dependency product adds its full occurrence count. *)
Lemma schedule_product_mass reads writes st :
  schedule_inventory st -> schedule_supported st ->
  (forall u, In u reads -> In u (schedule_vertices st)) ->
  schedule_supported
    (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
      reads st) /\
  schedule_mass_on
    (schedule_vertices
      (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
        reads st))
    (fold_left (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc)
      reads st) =
    schedule_mass_on (schedule_vertices st) st + length reads * length writes.
Proof.
  revert st; induction reads as [|u reads IH]; intros st Hinv Hsupport Hreads.
  - cbn [fold_left length]; split; [exact Hsupport|lia].
  - cbn [fold_left length].
    destruct (schedule_writes_correct writes st u Hinv) as [Hnext [Hvertices Hedges]].
    destruct (schedule_writes_mass writes st u Hinv Hsupport (Hreads u (or_introl eq_refl)))
      as [Hnextsupport Hmass].
    assert (Hnextreads : forall x, In x reads ->
      In x (schedule_vertices (fold_left (fun acc v => schedule_edge u v acc) writes st))).
    { intros x Hx; rewrite Hvertices; apply Hreads; now right. }
    destruct (IH _ Hnext Hnextsupport Hnextreads) as [Hfinal Hfinalmass].
    split; [exact Hfinal|]. rewrite Hfinalmass, Hmass; lia.
Qed.

(** A row's mass increment is the product of its read and write counts. *)
Lemma schedule_row_mass {R K} (code : K -> positive) target deps sides (r : R) st :
  schedule_inventory st -> schedule_supported st ->
  schedule_supported (schedule_graph_row code target deps sides st r) /\
  schedule_mass_on (schedule_vertices (schedule_graph_row code target deps sides st r))
    (schedule_graph_row code target deps sides st r) =
  schedule_mass_on (schedule_vertices st) st + length (deps r) * (length (sides r) + 1).
Proof.
  intros Hinv Hsupport; unfold schedule_graph_row.
  destruct (schedule_vertices_correct
    (map code (target r :: sides r) ++ map code (deps r)) st Hinv)
    as [Hlisted [Hvertices Hadj]].
  destruct (schedule_vertices_mass
    (map code (target r :: sides r) ++ map code (deps r)) st Hinv Hsupport)
    as [Hlistedsupport Hmass].
  assert (Hreads : forall u, In u (map code (deps r)) ->
    In u (schedule_vertices (fold_left (fun acc v => schedule_vertex v acc)
      (map code (target r :: sides r) ++ map code (deps r)) st))).
  { intros u Hu; apply Hvertices; left; apply in_or_app; now right. }
  destruct (schedule_product_mass (map code (deps r)) (map code (target r :: sides r))
    _ Hlisted Hlistedsupport Hreads) as [Hfinal Hfinalmass].
  split; [exact Hfinal|]. rewrite Hfinalmass, Hmass, !length_map; cbn [length]; lia.
Qed.

(** Folding rows sums their edge products without losing duplicate occurrences. *)
Lemma schedule_rows_mass {R K} (code : K -> positive) target deps sides (rows : list R) st :
  schedule_inventory st -> schedule_supported st ->
  schedule_mass_on
    (schedule_vertices (fold_left (schedule_graph_row code target deps sides) rows st))
    (fold_left (schedule_graph_row code target deps sides) rows st) =
  schedule_mass_on (schedule_vertices st) st +
    fold_right Nat.add 0 (map (fun r => length (deps r) * (length (sides r) + 1)) rows).
Proof.
  revert st; induction rows as [|r rows IH]; intros st Hinv Hsupport.
  - cbn [fold_left fold_right map]; lia.
  - cbn [fold_left fold_right map].
    destruct (schedule_row_correct code target deps sides r st Hinv) as [Hnext _].
    destruct (schedule_row_mass code target deps sides r st Hinv Hsupport)
      as [Hnextsupport Hmass].
    rewrite IH by assumption; rewrite Hmass; lia.
Qed.

(** Adjacency mass adds over concatenated source inventories. *)
Lemma schedule_mass_app xs ys st :
  schedule_mass_on (xs ++ ys) st = schedule_mass_on xs st + schedule_mass_on ys st.
Proof.
  unfold schedule_mass_on; induction xs as [|x xs IH]; cbn [app fold_right]; lia.
Qed.

(** Reversing the vertex inventory preserves its adjacency mass. *)
Lemma schedule_mass_rev vs st : schedule_mass_on (rev vs) st = schedule_mass_on vs st.
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  cbn [rev]; rewrite schedule_mass_app, IH.
  unfold schedule_mass_on; cbn [fold_right]; lia.
Qed.

(** Empty construction has no supported adjacency occurrences. *)
Lemma schedule_empty_supported : schedule_supported (ScheduleGraphState nil Empty Empty).
Proof.
  intros u Hu; unfold schedule_adj; cbn [schedule_successors].
  rewrite PTrie.get_empty; reflexivity.
Qed.

(** Graph construction retains exactly the total dependency-product occurrence count. *)
Lemma schedule_graph_edge_count {R K} (code : K -> positive) target deps sides (rows : list R) :
  graph_e (schedule_graph code target deps sides rows) =
    fold_right Nat.add 0 (map (fun r => length (deps r) * (length (sides r) + 1)) rows).
Proof.
  pose proof (schedule_rows_mass code target deps sides rows
    (ScheduleGraphState nil Empty Empty) schedule_empty_inventory schedule_empty_supported)
    as Hmass.
  unfold schedule_graph.
  destruct (fold_left (schedule_graph_row code target deps sides) rows
    (ScheduleGraphState nil Empty Empty)) as [vs seen adjacency].
  cbn [schedule_vertices] in Hmass.
  change (schedule_mass_on vs (ScheduleGraphState vs seen adjacency) =
    fold_right Nat.add 0 (map (fun r => length (deps r) * (length (sides r) + 1)) rows))
    in Hmass.
  unfold graph_e; rewrite <- rev_alt.
  change (schedule_mass_on (rev vs) (ScheduleGraphState vs seen adjacency) =
    fold_right Nat.add 0 (map (fun r => length (deps r) * (length (sides r) + 1)) rows)).
  now rewrite schedule_mass_rev.
Qed.

Module ScheduleCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L)
    (G : DIGRAPH_OPS) (W : WTO_OPS) <: SCHEDULE_OPS L S.
  Definition dep_graph (p : S.prog) : digraph :=
    schedule_graph S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p).

  Definition of_wto (w : wto) (cfg : head_cfg) (wp : L.wparam) (n : nat)
      : policy L.wparam :=
    @Policy L.wparam (W.ranks w) (schedule_head_map cfg (W.heads w)) wp n.

  Definition plan (p : S.prog) (cfg : head_cfg) (wp : L.wparam) (n : nat)
      : option (policy L.wparam) :=
    let graph := dep_graph p in
    let prepared := G.prepare graph in
    let roots := verts graph in
    let order := W.build prepared roots in
    if W.check prepared roots order then Some (of_wto order cfg wp n) else None.

  Definition cuts (p : S.prog) (pol : policy L.wparam) : bool :=
    forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol)
      (S.rows p).
End ScheduleCode.

Module Schedule (L : WLATTICE) (S : SYSTEM L) (G : DIGRAPH) (W : WTO)
    <: SCHEDULE L S G W.
  Include ScheduleCode L S G W.
  Include SCHEDULE_SPEC L S.
  (** The dependency graph has exactly the declared dependency edges. *)
  Lemma dep_graph_edges : forall p u v,
    edge (dep_graph p) u v <-> dependency_edge p u v.
  Proof.
    intros p u v; apply schedule_graph_edges.
  Qed.
  (** The graph lists exactly the key codes read or written by a row. *)
  Lemma dep_graph_vertices : forall p c,
    In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\ In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\
        S.key_code x = c.
  Proof.
    intros p c; apply (proj2 (schedule_graph_vertices
      S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p))).
  Qed.

  (** Graph construction makes a well-formed graph for every row description. *)
  Lemma dep_graph_wf p : wf_graph (dep_graph p).
  Proof.
    split.
    - apply (proj1 (schedule_graph_vertices
        S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p))).
    - intros u v Hu Hedge; apply dep_graph_edges in Hedge.
      destruct Hedge as [r [x [y [Hr [Hx [Hy [Hxu Hyv]]]]]]].
      apply dep_graph_vertices; exists r, y; repeat split; try assumption.
      apply in_or_app; now left.
  Qed.
  (** WTO priorities use the WTO's public rank projection. *)
  Lemma of_wto_prio : forall w cfg wp n, prio (of_wto w cfg wp n) = W.ranks w.
  Proof.
    reflexivity.
  Qed.
  (** WTO loop heads receive the supplied head configuration. *)
  Lemma of_wto_heads : forall w cfg wp n c,
    trie_get c (heads (of_wto w cfg wp n)) =
      if existsb (Pos.eqb c) (W.heads w) then Some cfg else None.
  Proof.
    intros w cfg wp n c; unfold of_wto; cbn [heads].
    unfold schedule_head_map; rewrite schedule_head_fold, PTrie.get_empty; reflexivity.
  Qed.
  (** Schedule construction retains widening parameters. *)
  Lemma of_wto_wp : forall w cfg wp n, PolicySig.wp (of_wto w cfg wp n) = wp.
  Proof.
    reflexivity.
  Qed.
  (** Schedule construction retains the requested narrowing pass count. *)
  Lemma of_wto_passes : forall w cfg wp n, passes (of_wto w cfg wp n) = n.
  Proof.
    reflexivity.
  Qed.
  (** Planning accepts a built WTO only when its checker accepts it. *)
  Lemma plan_spec : forall p cfg wp n,
    let g := G.prepare (dep_graph p) in
    let roots := verts (dep_graph p) in
    let w := W.build g roots in
    plan p cfg wp n = if W.check g roots w then Some (of_wto w cfg wp n) else None.
  Proof.
    reflexivity.
  Qed.
  (** Every non-increasing dependency edge enters a configured head. *)
  Lemma cuts_spec : forall p pol,
    cuts p pol = true <-> forall u v, dependency_edge p u v ->
      (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  Proof.
    intros p pol; unfold cuts; rewrite forallb_forall; split.
    - intros Hcuts u v [r [x [y [Hr [Hx [Hy [<- <-]]]]]]].
      apply (proj1 (schedule_cut_row_spec S.key_code (S.target p) (S.deps p)
        (S.sides p) pol r) (Hcuts r Hr) x y Hx Hy).
    - intros Hcuts r Hr.
      apply (proj2 (schedule_cut_row_spec S.key_code (S.target p) (S.deps p)
        (S.sides p) pol r)).
      intros x y Hx Hy; apply Hcuts; exists r, x, y; auto.
  Qed.
  (** A checked WTO cuts every non-increasing dependency edge. *)
  Lemma of_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  Proof.
    intros p w cfg wp n Hcheck; apply cuts_spec; intros u v Hedge.
    assert (Hu : In u (verts (dep_graph p))).
    { destruct Hedge as [r [x [y [Hr [Hx [Hy [Hxu Hyv]]]]]]].
      apply dep_graph_vertices; exists r, x; repeat split; try assumption.
      apply in_or_app; now right. }
    assert (Hpreparededge : edge (base (G.prepare (dep_graph p))) u v).
    { rewrite G.prepare_base; now apply dep_graph_edges. }
    assert (Hreach : reach (base (G.prepare (dep_graph p))) (verts (dep_graph p)) u).
    { exists u, (u :: nil); split; [exact Hu|constructor]. }
    destruct (W.ranks_forward _ _ _ _ _ Hcheck Hpreparededge Hreach)
      as [ru [rv [Hru [Hrv [Hforward|[Hhead Hback]]]]]].
    - left; unfold priority; rewrite of_wto_prio, Hru, Hrv; exact Hforward.
    - right; exists cfg; rewrite of_wto_heads.
      assert (Hmember : existsb (Pos.eqb v) (W.heads w) = true).
      { apply existsb_exists; exists v; split; [exact Hhead|apply Pos.eqb_refl]. }
      now rewrite Hmember.
  Qed.
  (** Every accepted schedule cuts the program's dependency edges. *)
  Lemma plan_cuts : forall p cfg wp n pol,
    plan p cfg wp n = Some pol -> cuts p pol = true.
  Proof.
    intros p cfg wp n pol; rewrite plan_spec.
    destruct (W.check (G.prepare (dep_graph p)) (verts (dep_graph p))
      (W.build (G.prepare (dep_graph p)) (verts (dep_graph p)))) eqn:Hcheck;
      intro Hplan; [|discriminate].
    injection Hplan as <-; now apply of_wto_cuts.
  Qed.
End Schedule.

Module ScheduleT (L : WLATTICE_T) (S : SYSTEM_T L)
    (G : DIGRAPH_T) (W : WTO_T) <: SCHEDULE_ALL L S G W.
  Include Schedule L S G W.

  TimeFun dep_graph.
  TimeFun of_wto.
  TimeFun plan.
  TimeFun cuts.

  Definition c_sched : N := 1%N. (* STUB *)

  (** Dependency graph construction charges every declared occurrence. *)
  Lemma T_dep_graph_le : forall p, S.wf p ->
    (T_dep_graph p <= c_sched * (N.of_nat (row_count p + occurrence_count p +
      edge_count p + 1) * N.of_nat (S.kw p + 1) +
      N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** WTO conversion charges traversal, ranks and encoded vertices. *)
  Lemma T_of_wto_le : forall w cfg wp n,
    (T_of_wto w cfg wp n <= c_sched * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Planning pays for graph preparation and the nesting depth of the built WTO. *)
  Lemma T_plan_le : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
        N.of_nat (S.kw p + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Cut checking is linear in declared occurrences and program key width. *)
  Lemma T_cuts_le : forall p pol, S.wf p ->
    (T_cuts p pol <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Every planned priority fits the program key width. *)
  Lemma plan_prio_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
  Proof.
    intros p cfg wp n pol Hwf; rewrite plan_spec.
    set (w := W.build (G.prepare (dep_graph p)) (verts (dep_graph p))).
    destruct (W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w) eqn:Hcheck;
      intro Hplan; [|discriminate].
    injection Hplan as <-.
    destruct (W.check_sound _ _ _ Hcheck) as [Hnodup [Hcoverage Hedges]].
    assert (Hwidth : forall c, In c (verts (dep_graph p)) -> Pos.size_nat c <= S.kw p).
    { intros c Hc; apply dep_graph_vertices in Hc as [r [x [Hr [Hx <-]]]].
      apply (S.key_bits_le p r x Hwf Hr Hx). }
    assert (Hlength : length (wto_order w) <= 2 ^ S.kw p).
    { apply schedule_key_count; [exact Hnodup|]. intros c Hc; apply Hwidth.
      apply Hcoverage in Hc; rewrite G.prepare_base in Hc.
      exact (schedule_reach_listed _ _ (dep_graph_wf p) Hc). }
    unfold prio_width; apply schedule_map_max_le; intros c Hc.
    apply in_flat_map in Hc as [r [Hr Hc]].
    apply in_map_iff in Hc as [x [<- Hx]].
    assert (Hroot : In (S.key_code x) (verts (dep_graph p))).
    { apply dep_graph_vertices; exists r, x; auto. }
    assert (Hin : In (S.key_code x) (wto_order w)).
    { apply Hcoverage; exists (S.key_code x), (S.key_code x :: nil).
      split; [exact Hroot|constructor]. }
    apply In_nth_error in Hin as [i Hi].
    pose proof (W.ranks_spec w Hnodup (S.key_code x) i Hi) as Hrank.
    unfold priority; rewrite of_wto_prio, Hrank.
    apply schedule_rank_width; rewrite SuccNat2Pos.id_succ.
    assert (Hindex : i < length (wto_order w)).
    { apply nth_error_Some; rewrite Hi; discriminate. }
    lia.
  Qed.

  Definition k_graph : N := 1%N. (* STUB *)
  Definition k_heads : N := 8%N.
  Definition k_cuts : N := 1%N. (* STUB *)
  Definition k_plan : N := 8%N.

  (** Construction uses the shared first-order graph builder. *)
  Lemma F1_graph : forall p, dep_graph p =
    schedule_graph S.key_code (S.target p) (S.deps p) (S.sides p) (S.rows p).
  Proof.
    reflexivity.
  Qed.

  (** The graph builder lists each read or write code exactly once. *)
  Lemma F2_vertices : forall p, NoDup (verts (dep_graph p)) /\
    forall c, In c (verts (dep_graph p)) <->
      exists r x, In r (S.rows p) /\
        In x ((S.target p r :: S.sides p r) ++ S.deps p r) /\ S.key_code x = c.
  Proof.
    intro p; apply schedule_graph_vertices.
  Qed.

  (** Every emitted adjacency occurrence comes from a declared dependency product. *)
  Lemma F3_edges : forall p u v,
    edge (dep_graph p) u v <-> dependency_edge p u v.
  Proof.
    exact dep_graph_edges.
  Qed.

  (** Preparation retains a well-formed graph whose vertices are all roots. *)
  Lemma F4_prepared : forall p,
    wf_graph (dep_graph p) /\ base (G.prepare (dep_graph p)) = dep_graph p /\
    forall u, In u (verts (dep_graph p)) ->
      reach (base (G.prepare (dep_graph p))) (verts (dep_graph p)) u.
  Proof.
    intro p; split; [apply dep_graph_wf|]. split; [apply G.prepare_base|].
    intros u Hu; exists u, (u :: nil); split; [exact Hu|constructor].
  Qed.

  (** WTO conversion pairs its public ranks with its configured structural heads. *)
  Lemma F5_policy : forall w cfg wp n, of_wto w cfg wp n =
    @Policy L.wparam (W.ranks w) (schedule_head_map cfg (W.heads w)) wp n.
  Proof.
    reflexivity.
  Qed.

  (** Cut checking uses the maximum dependency rank for each row. *)
  Lemma F6_cut_code : forall p pol, cuts p pol =
    forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol)
      (S.rows p).
  Proof.
    reflexivity.
  Qed.

  (** Maximum-rank checking is equivalent to the public dependency-edge criterion. *)
  Lemma F7_cut_spec : forall p pol, cuts p pol = true <-> forall u v,
    dependency_edge p u v -> (priority pol u < priority pol v)%positive \/
      exists cfg, trie_get v (heads pol) = Some cfg.
  Proof.
    exact cuts_spec.
  Qed.

  (** Checked WTO forward ranks discharge every non-head dependency. *)
  Lemma F8_wto_cuts : forall p w cfg wp n,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    cuts p (of_wto w cfg wp n) = true.
  Proof.
    exact of_wto_cuts.
  Qed.

  (** Program vertices and edge occurrences fit the declared occurrence budgets. *)
  Lemma F9_graph_sizes : forall p,
    graph_n (dep_graph p) <= occurrence_count p /\
    graph_e (dep_graph p) = edge_count p.
  Proof.
    intro p; split.
    - assert (Hincl : incl (verts (dep_graph p))
        (flat_map (fun r => map S.key_code ((S.target p r :: S.sides p r) ++ S.deps p r))
          (S.rows p))).
      { intros c Hc; apply dep_graph_vertices in Hc as [r [x [Hr [Hx Hcode]]]].
        apply in_flat_map; exists r; split; [exact Hr|].
        apply in_map_iff; exists x; auto. }
      pose proof (NoDup_incl_length (proj1 (dep_graph_wf p)) Hincl) as Hlength.
      rewrite schedule_occurrence_length in Hlength.
      destruct (dep_graph p); exact Hlength.
    - apply schedule_graph_edge_count.
  Qed.

  (** All dependency graph identifiers fit the program key budget. *)
  Lemma F10_width : forall p, S.wf p -> graph_width (dep_graph p) <= S.kw p.
  Proof.
    intros p Hwf; apply schedule_graph_width_le; [apply dep_graph_wf|].
    intros v Hv; apply dep_graph_vertices in Hv as [r [x [Hr [Hx <-]]]].
    apply (S.key_bits_le p r x Hwf Hr Hx).
  Qed.

  (** Unique bounded-width identifiers bound the width of their assigned positive ranks. *)
  Lemma F11_rank_width : forall p cfg wp n pol, S.wf p ->
    plan p cfg wp n = Some pol -> prio_width p pol <= S.kw p + 1.
  Proof.
    exact plan_prio_width.
  Qed.

  (** Accepted WTO conversion scans distinct program vertices with bounded identifiers. *)
  Lemma F12_checked_size : forall p w,
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    length (wto_order w) <= graph_n (dep_graph p) /\
    vertex_width (wto_order w) <= graph_width (dep_graph p).
  Proof.
    intros p w Hcheck.
    destruct (W.check_sound _ _ _ Hcheck) as [Hnodup [Hcoverage Hedges]].
    assert (Hlisted : forall v, In v (wto_order w) -> In v (verts (dep_graph p))).
    { intros v Hv; apply Hcoverage in Hv; rewrite G.prepare_base in Hv.
      exact (schedule_reach_listed _ _ (dep_graph_wf p) Hv). }
    split.
    - unfold graph_n; destruct (dep_graph p) as [vs adjacency] eqn:Hgraph.
      eapply NoDup_incl_length; [exact Hnodup|exact Hlisted].
    - eapply Nat.le_trans; [|apply schedule_graph_vertex_width].
      apply schedule_vertex_width_le; intros v Hv.
      apply schedule_vertex_width_member; now apply Hlisted.
  Qed.

  (** Graph construction charges readers, encoded occurrences and emitted edges. *)
  Lemma T1_graph : forall p, S.wf p ->
    (T_dep_graph p <= k_graph *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** WTO conversion charges the public projections and configured-head insertion. *)
  Lemma T2_policy : forall w cfg wp n,
    (T_of_wto w cfg wp n <= k_heads *
      (W.T_ranks w + W.T_heads w + T_schedule_head_map cfg (W.heads w) + 1))%N.
  Proof.
    intros w cfg wp n; unfold k_heads; time_step.
  Qed.

  (** Maximum-rank cut checking retains the linear public occurrence bound. *)
  Lemma T3_cuts : forall p pol, S.wf p ->
    (T_cuts p pol <= k_cuts *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Planning pays each graph, WTO and conversion phase explicitly. *)
  Lemma T4_plan_phases : forall p cfg wp n,
    let graph := dep_graph p in
    let prepared := G.prepare graph in
    let roots := verts graph in
    let order := W.build prepared roots in
    (T_plan p cfg wp n <= k_plan * (T_dep_graph p + G.T_prepare graph +
      W.T_build prepared roots + W.T_check prepared roots order +
      (if W.check prepared roots order then T_of_wto order cfg wp n else 0) + 1))%N.
  Proof.
    intros p cfg wp n; unfold k_plan; time_step.
  Qed.

  (** The phase bounds discharge the unchanged public schedule contract. *)
  Lemma T5_plan_public : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
       N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
       N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof. Admitted. (* STUB *)
End ScheduleT.
