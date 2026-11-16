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

(** The unique graph inventory fits the declared occurrence list. *)
Lemma schedule_graph_vertex_count {R K} (code : K -> positive) target deps sides
    (rows : list R) :
  graph_n (schedule_graph code target deps sides rows) <=
    fold_right Nat.add 0
      (map (fun r => length (deps r) + length (sides r) + 1) rows).
Proof.
  destruct (schedule_graph_vertices code target deps sides rows) as [Hnodup Hvertices].
  assert (Hincl : incl (verts (schedule_graph code target deps sides rows))
    (flat_map (fun r => map code ((target r :: sides r) ++ deps r)) rows)).
  { intros c Hc; apply Hvertices in Hc as [r [x [Hr [Hx Hcode]]]].
    apply in_flat_map; exists r; split; [exact Hr|].
    apply in_map_iff; exists x; auto. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
  rewrite schedule_occurrence_length in Hlength.
  destruct (schedule_graph code target deps sides rows); exact Hlength.
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

(** A timed fold needs a uniform callback bound only on the elements it visits. *)
Lemma schedule_T_fold_in : forall A B (f : A -> B -> A) Tf xs acc k,
  (forall state x, In x xs -> (Tf state x <= k)%N) ->
  (List.T_fold_left f Tf xs acc <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f Tf xs; induction xs as [|x xs IH]; intros acc k Hcallback.
  - time_step.
  - pose proof (Hcallback acc x (or_introl eq_refl)) as Hhead.
    pose proof (IH (f acc x) k
      (fun state y Hy => Hcallback state y (or_intror Hy))) as Htail.
    time_step.
Qed.

(** Timed mapping charges the input occurrences with their encoding bounds. *)
Lemma schedule_T_map_in : forall A B (f : A -> B) Tf xs k,
  (forall x, In x xs -> (Tf x <= k)%N) ->
  (ListDef.T_map f Tf xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f Tf xs; induction xs as [|x xs IH]; intros k Hcallback.
  - time_step.
  - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
    pose proof (IH k (fun y Hy => Hcallback y (or_intror Hy))) as Htail.
    time_step.
Qed.

(** Boolean traversal charges only callback bounds for elements of its input. *)
Lemma schedule_T_forallb_in : forall A (f : A -> bool) Tf xs k,
  (forall x, In x xs -> (Tf x <= k)%N) ->
  (List.T_forallb f Tf xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A f Tf xs; induction xs as [|x xs IH]; intros k Hcallback.
  - time_step.
  - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
    pose proof (IH k (fun y Hy => Hcallback y (or_intror Hy))) as Htail.
    time_step.
Qed.

(** A positive width budget absorbs a callback's constant call overhead. *)
Lemma schedule_step_budget time coefficient small big :
  (time <= coefficient * small)%N -> (small <= big)%N -> (1 <= big)%N ->
  (1 + time <= (coefficient + 1) * big)%N.
Proof.
  intros Htime Hwidth Hpositive; nia.
Qed.

(** Every width budget includes one unit for constant-time work. *)
Lemma schedule_width_positive width : (1 <= N.of_nat (width + 1))%N.
Proof.
  apply (time_of_nat_le 1 (width + 1)); lia.
Qed.

(** The row's eight phase envelopes fit one occurrence-and-reader budget. *)
Lemma schedule_row_arithmetic (code trie keys reads sides work : N) :
  (1 + (code * (work + 1) + code * (sides + 1) * (keys + 1) +
    ((code * (keys + 1) + 1) * (sides + 1) + 1) +
    (code * (reads + 1) * (keys + 1) + ((code * (keys + 1) + 1) * reads + 1) +
      ((sides + 1 + 1) +
        (((32 * (trie + 1) + 1) * (keys + 1) + 1) * (sides + 1 + reads) + 1) +
        ((((32 * (trie + 1) + 1) * (keys + 1) + 1) * (sides + 1) + 2 + 1) *
          reads + 1)))) <=
    128 * (code + trie + 1) *
      ((reads + sides + reads * (sides + 1) + 2) * (keys + 1) + work + 1))%N.
Proof.
  nia.
Qed.

(** Head-map construction performs one width-bounded insertion per head. *)
Lemma schedule_T_head_map cfg vs width :
  (forall v, In v vs -> Pos.size_nat v <= width) ->
  (T_schedule_head_map cfg vs <= (PTrieT.c_trie + 4) *
    N.of_nat ((length vs + 1) * (width + 1)))%N.
Proof.
  intro Hwidth.
  assert (Hcallback : forall acc v, In v vs ->
    (1 + PTrieCode.T_set v cfg acc <= (PTrieT.c_trie + 2) * N.of_nat (width + 1))%N).
  { intros acc v Hv; pose proof (PTrieT.T_set_le head_cfg v cfg acc) as Hset.
    pose proof (Hwidth v Hv) as Hbits; nia. }
  pose proof (schedule_T_fold_in _ _ (fun acc v => PTrieCode.set v cfg acc)
    _ vs Empty _ Hcallback) as Hfold.
  unfold T_schedule_head_map; time_cbn; rewrite Nat2N.inj_mul; nia.
Qed.

(** A vertex insertion pays for one lookup and at most one trie update. *)
Lemma schedule_T_vertex v st :
  (T_schedule_vertex v st <= 32 * (PTrieT.c_trie + 1) *
    N.of_nat (Pos.size_nat v + 1))%N.
Proof.
  destruct st as [vs seen adjacency].
  pose proof (PTrieT.T_trie_get_le bool v seen) as Hget.
  pose proof (PTrieT.T_set_le bool v true seen) as Hset.
  unfold T_schedule_vertex; time_cbn.
  destruct (trie_get v seen); time_cbn; nia.
Qed.

(** An edge insertion pays for source-key lookup and insertion. *)
Lemma schedule_T_edge u v st :
  (T_schedule_edge u v st <= 32 * (PTrieT.c_trie + 1) *
    N.of_nat (Pos.size_nat u + 1))%N.
Proof.
  destruct st as [vs seen adjacency].
  pose proof (PTrieT.T_trie_get_le (list positive) u adjacency) as Hget.
  pose proof (PTrieT.T_set_le (list positive) u
    (v :: match trie_get u adjacency with Some xs => xs | None => nil end) adjacency) as Hset.
  unfold T_schedule_edge; time_cbn; nia.
Qed.

(** Structural heads form a subcollection of the WTO's linear inventory. *)
Lemma schedule_heads_in w : incl (wto_heads w) (wto_order w).
Proof.
  induction w as [|v rest IH|h inside IHinside rest IHrest]; intros x Hx.
  - contradiction.
  - cbn [wto_heads wto_order] in *; right; now apply IH.
  - cbn [wto_heads wto_order] in *; destruct Hx as [<-|Hx]; [now left|].
    right; apply in_app_or in Hx as [Hin|Hin]; apply in_or_app.
    + left; now apply IHinside.
    + right; now apply IHrest.
Qed.

(** A structural head occupies one position in the WTO's linear inventory. *)
Lemma schedule_heads_length w : length (wto_heads w) <= length (wto_order w).
Proof.
  induction w; cbn [wto_heads wto_order length]; rewrite ?length_app; lia.
Qed.

(** Rank comparison pays only for the first rank's bits. *)
Lemma schedule_T_ltb left right :
  (Pos.T_ltb left right <= N.of_nat (Pos.size_nat left) + 2)%N.
Proof.
  pose proof (Pos.T_compare_le left right) as Hcompare.
  unfold Pos.T_ltb; time_cbn; destruct (Pos.compare left right); time_cbn; lia.
Qed.

(** A priority lookup pays for the encoded key and its record projection. *)
Lemma schedule_T_priority {A} (pol : policy A) v :
  (T_schedule_priority pol v <= 4 * N.of_nat (Pos.size_nat v + 1))%N.
Proof.
  pose proof (PTrieT.T_trie_get_le positive v (prio pol)) as Hget.
  unfold T_schedule_priority, T_prio; time_cbn; lia.
Qed.

(** Write checking pays for the write key and the maximum read rank. *)
Lemma schedule_T_write_cut {A} (pol : policy A) rank v :
  (T_schedule_write_cut pol rank v <=
    16 * N.of_nat (Pos.size_nat v + Pos.size_nat rank + 1))%N.
Proof.
  pose proof (schedule_T_priority pol v) as Hprio.
  pose proof (schedule_T_ltb rank (schedule_priority pol v)) as Hcompare.
  pose proof (PTrieT.T_trie_get_le head_cfg v (heads pol)) as Hget.
  unfold T_schedule_write_cut, T_heads; time_cbn.
  destruct (Pos.ltb rank (schedule_priority pol v)); time_cbn; lia.
Qed.

(** The read maximum can start from an earlier bounded accumulator. *)
Definition schedule_read_from {A} (pol : policy A) reads best :=
  fold_left (fun acc v => let rank := schedule_priority pol v in
    match acc with
    | None => Some rank
    | Some old => Some (if Pos.ltb old rank then rank else old)
    end) reads best.

TimeFun schedule_read_from.

(** Taking the maximum preserves the bit-width bound of every supplied rank. *)
Lemma schedule_read_from_width {A} (pol : policy A) reads best bound :
  (match best with None => True | Some rank => Pos.size_nat rank <= bound end) ->
  (forall v, In v reads -> Pos.size_nat (schedule_priority pol v) <= bound) ->
  match schedule_read_from pol reads best with
  | None => True
  | Some rank => Pos.size_nat rank <= bound
  end.
Proof.
  unfold schedule_read_from; revert best; induction reads as [|v reads IH];
    intros best Hbest Hreads; [exact Hbest|].
  cbn [fold_left]; apply IH.
  - destruct best as [rank|]; [destruct (Pos.ltb rank (schedule_priority pol v))|];
      cbn; try assumption; apply Hreads; now left.
  - intros x Hx; apply Hreads; now right.
Qed.

(** Read-maximum computation charges each key and its bounded accumulated rank. *)
Lemma schedule_T_read_from {A} (pol : policy A) reads best keys ranks :
  (match best with None => True | Some rank => Pos.size_nat rank <= ranks end) ->
  (forall v, In v reads -> Pos.size_nat v <= keys /\
    Pos.size_nat (schedule_priority pol v) <= ranks) ->
  (T_schedule_read_from pol reads best <=
    32 * N.of_nat ((length reads + 1) * (keys + ranks + 1)))%N.
Proof.
  revert best; induction reads as [|v reads IH]; intros best Hbest Hreads.
  - unfold T_schedule_read_from, List.T_fold_left; cbn beta iota zeta.
    cbn [length].
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add; nia.
  - destruct (Hreads v (or_introl eq_refl)) as [Hv Hrank].
    assert (Htail : forall x, In x reads -> Pos.size_nat x <= keys /\
      Pos.size_nat (schedule_priority pol x) <= ranks).
    { intros x Hx; apply Hreads; now right. }
    pose proof (schedule_T_priority pol v) as Hprio.
    destruct best as [old|].
    + pose proof (schedule_T_ltb old (schedule_priority pol v)) as Hcompare.
      destruct (Pos.ltb old (schedule_priority pol v)) eqn:Hlt.
      * pose proof (IH (Some (schedule_priority pol v)) Hrank Htail) as Htime.
        unfold T_schedule_read_from, List.T_fold_left in Htime |- *.
        cbn beta iota zeta in Htime |- *; rewrite Hlt; cbn beta iota zeta.
        clear - Htime Hprio Hcompare Hv Hbest; cbn [length].
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add,
          ?time_of_nat_succ in *; nia.
      * pose proof (IH (Some old) Hbest Htail) as Htime.
        unfold T_schedule_read_from, List.T_fold_left in Htime |- *.
        cbn beta iota zeta in Htime |- *; rewrite Hlt; cbn beta iota zeta.
        clear - Htime Hprio Hcompare Hv Hbest; cbn [length].
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add,
          ?time_of_nat_succ in *; nia.
    + pose proof (IH (Some (schedule_priority pol v)) Hrank Htail) as Htime.
      unfold T_schedule_read_from, List.T_fold_left in Htime |- *.
      cbn beta iota zeta in Htime |- *; clear - Htime Hprio Hv; cbn [length].
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add,
        ?time_of_nat_succ in *; nia.
Qed.

(** Every mapped member is bounded by the fold's maximum. *)
Lemma schedule_map_max_member {A} (f : A -> nat) xs x :
  In x xs -> f x <= fold_right Nat.max 0 (map f xs).
Proof.
  induction xs as [|y ys IH]; intro Hx; [contradiction|].
  cbn [map fold_right]; destruct Hx as [<-|Hx].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hx|apply Nat.le_max_r].
Qed.

(** Read, write and reader envelopes fit the row's linear occurrence budget. *)
Lemma schedule_cut_row_arithmetic (code keys ranks reads sides work : N) :
  (1 + (code * (reads + 1) * (keys + 1) +
    ((code * (keys + 1) + 1) * reads + 1) +
    32 * ((reads + 1) * (keys + ranks + 1))) +
    (code * (work + 1) + code * (sides + 1) * (keys + 1) +
      (((code + 17) * (keys + ranks + 1) + 2) * (sides + 1) + 1)) <=
    128 * (code + 1) *
      ((reads + sides + 2) * (keys + ranks + 1) + work + 1))%N.
Proof.
  nia.
Qed.


(** The sum of graph, preparation, WTO and conversion charges fits one plan coefficient. *)
Lemma schedule_plan_arithmetic (code prepare wto trie base nested work : N) :
  (base <= nested)%N -> (1 <= nested)%N ->
  (8 * (1024 * (code + trie + 1) * (base + work) + prepare * base +
    2 * wto * nested + 2 * wto * base + 16 * (wto + trie + 4) * base + 1) <=
    32768 * (code + prepare + wto + trie + 1) * (nested + work))%N.
Proof.
  intros Hdepth Hnonempty; nia.
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

  (** A graph row pays for key occurrences, emitted edges and its target reader. *)
  Lemma graph_row_time_bound p r st : S.wf p -> In r (S.rows p) ->
    (T_schedule_graph_row S.key_code S.T_key_code (S.target p) (S.T_target p)
      (S.deps p) (S.T_deps p) (S.sides p) (S.T_sides p) st r <=
      128 * (S.c_sys + PTrieT.c_trie + 1) *
        (N.of_nat (length (S.deps p r) + length (S.sides p r) +
          length (S.deps p r) * (length (S.sides p r) + 1) + 2) *
          N.of_nat (S.kw p + 1) + S.row_work p 0 + 1))%N.
  Proof.
    intros Hwf Hr.
    set (writes := map S.key_code (S.target p r :: S.sides p r)).
    set (reads := map S.key_code (S.deps p r)).
    set (width := N.of_nat (S.kw p + 1)).
    set (step := ((32 * (PTrieT.c_trie + 1) + 1) * width)%N).
    assert (Hbits : forall x, In x ((S.target p r :: S.sides p r) ++ S.deps p r) ->
      S.key_bits x <= S.kw p) by (intros x Hx; exact (S.key_bits_le p r x Hwf Hr Hx)).
    assert (Hcode : forall x, In x ((S.target p r :: S.sides p r) ++ S.deps p r) ->
      (S.T_key_code x <= S.c_sys * width)%N).
    { intros x Hx; pose proof (S.T_key_code_le x) as Htime.
      eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l.
      unfold width; apply time_of_nat_le; apply Nat.add_le_mono_r; now apply Hbits. }
    assert (Hlisted : forall v, In v (writes ++ reads) -> Pos.size_nat v <= S.kw p).
    { intros v Hv; unfold writes, reads in Hv; rewrite <- map_app in Hv.
      apply in_map_iff in Hv as [x [<- Hx]]; apply Hbits; exact Hx. }
    assert (Hread : forall v, In v reads -> Pos.size_nat v <= S.kw p).
    { intros v Hv; apply Hlisted; apply in_or_app; now right. }
    assert (Hvertex : forall acc v, In v (writes ++ reads) ->
      (1 + T_schedule_vertex v acc <= step)%N).
    { intros acc v Hv; pose proof (schedule_T_vertex v acc) as Htime.
      unfold step; eapply schedule_step_budget; [exact Htime| |].
      - unfold width; apply time_of_nat_le; apply Nat.add_le_mono_r; now apply Hlisted.
      - apply schedule_width_positive. }
    pose proof (schedule_T_fold_in _ _ (fun acc v => schedule_vertex v acc)
      _ (writes ++ reads) st _ Hvertex) as Hvertices.
    assert (Hinner : forall acc u, In u reads ->
      (List.T_fold_left (fun acc v => schedule_edge u v acc)
        (fun acc v => 1 + T_schedule_edge u v acc)%N writes acc <=
        (step + 1) * N.of_nat (length writes) + 1)%N).
    { intros acc u Hu; apply schedule_T_fold_in; intros next v Hv.
      pose proof (schedule_T_edge u v next) as Htime.
      unfold step; eapply schedule_step_budget; [exact Htime| |].
      - unfold width; apply time_of_nat_le; apply Nat.add_le_mono_r; now apply Hread.
      - apply schedule_width_positive. }
    assert (Houter : forall acc u, In u reads ->
      (1 + List.T_fold_left (fun acc v => schedule_edge u v acc)
        (fun acc v => 1 + T_schedule_edge u v acc)%N writes acc <=
        (step + 1) * N.of_nat (length writes) + 2)%N).
    { intros acc u Hu; pose proof (Hinner acc u Hu) as Hbound; clear - Hbound; lia. }
    pose proof (schedule_T_fold_in _ _
      (fun acc u => fold_left (fun acc v => schedule_edge u v acc) writes acc) _ reads
      (fold_left (fun acc v => schedule_vertex v acc) (writes ++ reads) st) _ Houter)
      as Hproduct.
    assert (Hmapwrite :
      (ListDef.T_map S.key_code S.T_key_code (S.target p r :: S.sides p r) <=
        (S.c_sys * width + 1) * N.of_nat (length (S.target p r :: S.sides p r)) + 1)%N).
    { apply schedule_T_map_in; intros x Hx; apply Hcode; apply in_or_app; now left. }
    assert (Hmapread : (ListDef.T_map S.key_code S.T_key_code (S.deps p r) <=
      (S.c_sys * width + 1) * N.of_nat (length (S.deps p r)) + 1)%N).
    { apply schedule_T_map_in; intros x Hx; apply Hcode; apply in_or_app; now right. }
    pose proof (Datatypes.T_app_le writes reads) as Happ.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (S.T_sides_le p r Hwf Hr) as Hsides.
    assert (Hwriteslen : length writes = length (S.sides p r) + 1).
    { unfold writes; rewrite length_map, Nat.add_1_r; reflexivity. }
    assert (Hreadslen : length reads = length (S.deps p r))
      by (unfold reads; apply length_map).
    rewrite length_app, Hwriteslen, Hreadslen in Hvertices.
    rewrite Hwriteslen, Hreadslen in Hproduct; rewrite Hwriteslen in Happ.
    cbn [length] in Hmapwrite.
    unfold T_schedule_graph_row; fold writes; fold reads; cbn beta iota zeta.
    clear - Hvertices Hproduct Hmapwrite Hmapread Happ Htarget Hdeps Hsides.
    unfold step, width in *.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul, !Nat2N.inj_add, ?time_of_nat_succ in *.
    eapply N.le_trans; [|exact (schedule_row_arithmetic S.c_sys PTrieT.c_trie
      (N.of_nat (S.kw p)) (N.of_nat (length (S.deps p r)))
      (N.of_nat (length (S.sides p r))) (S.row_work p 0))].
    lia.
  Qed.

  (** Summing row construction charges preserves the declared row and occurrence budgets. *)
  Lemma graph_rows_time_bound p rs st : S.wf p -> incl rs (S.rows p) ->
    (List.T_fold_left (schedule_graph_row S.key_code (S.target p) (S.deps p) (S.sides p))
      (fun acc r => T_schedule_graph_row S.key_code S.T_key_code (S.target p) (S.T_target p)
        (S.deps p) (S.T_deps p) (S.sides p) (S.T_sides p) acc r) rs st <=
      256 * (S.c_sys + PTrieT.c_trie + 1) *
        (N.of_nat ((fold_right Nat.add 0 (map (fun r => length (S.deps p r) +
          length (S.sides p r) + length (S.deps p r) * (length (S.sides p r) + 1) + 2)
          rs) + 1)%nat) * N.of_nat (S.kw p + 1) +
          N.of_nat (length rs) * (S.row_work p 0 + 1)))%N.
  Proof.
    intro Hwf; revert st; induction rs as [|r rs IH]; intros st Hincl.
    - time_step.
    - pose proof (graph_row_time_bound p r st Hwf (Hincl r (or_introl eq_refl))) as Hrow.
      pose proof (IH (schedule_graph_row S.key_code (S.target p) (S.deps p) (S.sides p) st r)
        (fun x Hx => Hincl x (or_intror Hx))) as Htail.
      time_step.
  Qed.

  (** Row construction units decompose into rows, key occurrences and edge occurrences. *)
  Lemma graph_row_units p rs :
    fold_right Nat.add 0 (map (fun r => length (S.deps p r) + length (S.sides p r) +
      length (S.deps p r) * (length (S.sides p r) + 1) + 2) rs) =
    length rs + fold_right Nat.add 0
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs) +
      fold_right Nat.add 0
        (map (fun r => length (S.deps p r) * (length (S.sides p r) + 1)) rs).
  Proof.
    induction rs as [|r rs IH]; cbn [map fold_right length]; lia.
  Qed.

  (** Finishing the inventory and reading the row list fit the same graph budget. *)
  Lemma dep_graph_time_bound p : S.wf p ->
    (T_dep_graph p <= 1024 * (S.c_sys + PTrieT.c_trie + 1) *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (S.kw p + 1) + N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    intro Hwf.
    pose proof (graph_rows_time_bound p (S.rows p) (ScheduleGraphState nil Empty Empty)
      Hwf (fun x Hx => Hx)) as Hfold.
    rewrite graph_row_units in Hfold.
    pose proof (schedule_graph_vertex_count S.key_code (S.target p) (S.deps p)
      (S.sides p) (S.rows p)) as Hvertices.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    unfold T_dep_graph, T_schedule_graph; time_cbn.
    unfold schedule_graph in Hvertices.
    destruct (fold_left (schedule_graph_row S.key_code (S.target p) (S.deps p) (S.sides p))
      (S.rows p) (ScheduleGraphState nil Empty Empty)) as [vs seen adjacency].
    cbn [graph_n] in Hvertices; rewrite <- rev_alt, length_rev in Hvertices.
    pose proof (List.T_rev_append_le vs (@nil positive)) as Hrev.
    unfold row_count, occurrence_count, edge_count; time_cbn.
    match type of Hfold with (?t <= _)%N =>
      lazymatch goal with |- (_ <= ?bound)%N =>
        change (1 + (S.T_rows p + (1 + (t + List.T_rev_append vs nil))) <= bound)%N
      end
    end.
    pose proof (time_of_nat_le _ _ Hvertices) as Hlength.
    clear - Hfold Hlength Hrows Hrev.
    rewrite !Nat2N.inj_add in *; nia.
  Qed.

  (** Policy conversion combines the public rank and head traversals with head insertions. *)
  Lemma of_wto_time_bound w cfg wp n :
    (T_of_wto w cfg wp n <= 8 * (W.c_wto + PTrieT.c_trie + 4) *
      N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof.
    assert (Hwidth : forall v, In v (W.heads w) ->
      Pos.size_nat v <= vertex_width (wto_order w)).
    { intros v Hv; apply schedule_vertex_width_member.
      apply schedule_heads_in; now rewrite <- W.heads_spec. }
    pose proof (schedule_T_head_map cfg (W.heads w) _ Hwidth) as Hmap.
    pose proof (W.T_heads_le w) as Hheads.
    pose proof (W.T_ranks_le w) as Hranks.
    pose proof (schedule_heads_length w) as Hlength.
    rewrite <- W.heads_spec in Hlength.
    rewrite Nat2N.inj_mul in Hmap.
    unfold T_of_wto; time_cbn; nia.
  Qed.

  (** Each declared occurrence has a bounded code and a bounded policy rank. *)
  Lemma declared_widths p pol r : S.wf p -> In r (S.rows p) ->
    forall x, In x ((S.target p r :: S.sides p r) ++ S.deps p r) ->
      Pos.size_nat (S.key_code x) <= S.kw p /\
      Pos.size_nat (schedule_priority pol (S.key_code x)) <= prio_width p pol.
  Proof.
    intros Hwf Hr x Hx; split; [exact (S.key_bits_le p r x Hwf Hr Hx)|].
    unfold prio_width.
    apply (schedule_map_max_member (fun c => Pos.size_nat (priority pol c)) _ (S.key_code x)).
    apply in_flat_map; exists r; split; [exact Hr|].
    apply in_map; exact Hx.
  Qed.

  (** A checked write pays for encoding, priority lookup and rank comparison. *)
  Lemma cut_callback_time_bound p pol r rank : S.wf p -> In r (S.rows p) ->
    Pos.size_nat rank <= prio_width p pol ->
    forall x, In x (S.target p r :: S.sides p r) ->
      (1 + (S.T_key_code x + T_schedule_write_cut pol rank (S.key_code x)) <=
        (S.c_sys + 17) * N.of_nat (S.kw p + prio_width p pol + 1))%N.
  Proof.
    intros Hwf Hr Hrank x Hx.
    pose proof (proj1 (declared_widths p pol r Hwf Hr x (in_or_app _ _ _ (or_introl Hx))))
      as Hkey.
    pose proof (S.T_key_code_le x) as Hcode.
    pose proof (schedule_T_write_cut pol rank (S.key_code x)) as Hcut.
    assert (Hcode_bound : (S.T_key_code x <=
      S.c_sys * N.of_nat (S.kw p + prio_width p pol + 1))%N).
    { eapply N.le_trans; [exact Hcode|]; apply N.mul_le_mono_l.
      apply time_of_nat_le; change (Pos.size_nat (S.key_code x) + 1 <=
        S.kw p + prio_width p pol + 1); lia. }
    assert (Hcut_bound : (T_schedule_write_cut pol rank (S.key_code x) <=
      16 * N.of_nat (S.kw p + prio_width p pol + 1))%N).
    { eapply N.le_trans; [exact Hcut|]; apply N.mul_le_mono_l.
      apply time_of_nat_le; lia. }
    pose proof (schedule_width_positive (S.kw p + prio_width p pol)) as Hpositive.
    clear - Hcode_bound Hcut_bound Hpositive; nia.
  Qed.

  (** Each cut row scans its reads and writes without expanding dependency products. *)
  Lemma cut_row_time_bound p pol r : S.wf p -> In r (S.rows p) ->
    (T_schedule_cut_row S.key_code S.T_key_code (S.target p) (S.T_target p)
      (S.deps p) (S.T_deps p) (S.sides p) (S.T_sides p) pol r <=
      128 * (S.c_sys + 1) *
        (N.of_nat (length (S.deps p r) + length (S.sides p r) + 2) *
          N.of_nat (S.kw p + prio_width p pol + 1) + S.row_work p 0 + 1))%N.
  Proof.
    intros Hwf Hr.
    assert (Hread : forall c, In c (map S.key_code (S.deps p r)) ->
      Pos.size_nat c <= S.kw p /\
      Pos.size_nat (schedule_priority pol c) <= prio_width p pol).
    { intros c Hc; apply in_map_iff in Hc as [x [<- Hx]].
      apply (declared_widths p pol r Hwf Hr); apply in_or_app; now right. }
    pose proof (schedule_T_read_from pol (map S.key_code (S.deps p r)) None
      (S.kw p) (prio_width p pol) I Hread) as Hreadtime.
    change (T_schedule_read_rank pol (map S.key_code (S.deps p r)) <=
      32 * N.of_nat ((length (map S.key_code (S.deps p r)) + 1) *
        (S.kw p + prio_width p pol + 1)))%N in Hreadtime.
    rewrite length_map in Hreadtime.
    pose proof (schedule_read_from_width pol (map S.key_code (S.deps p r)) None
      (prio_width p pol) I (fun c Hc => proj2 (Hread c Hc))) as Hmaximum.
    change (match schedule_read_rank pol (map S.key_code (S.deps p r)) with
      | None => True
      | Some rank => Pos.size_nat rank <= prio_width p pol
      end) in Hmaximum.
    assert (Hmap : (ListDef.T_map S.key_code S.T_key_code (S.deps p r) <=
      (S.c_sys * N.of_nat (S.kw p + 1) + 1) * N.of_nat (length (S.deps p r)) + 1)%N).
    { apply schedule_T_map_in; intros x Hx.
      eapply N.le_trans; [apply S.T_key_code_le|]; apply N.mul_le_mono_l.
      apply time_of_nat_le; apply Nat.add_le_mono_r.
      apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_sides_le p r Hwf Hr) as Hsides.
    unfold T_schedule_cut_row; cbn beta iota zeta.
    destruct (schedule_read_rank pol (map S.key_code (S.deps p r))) as [rank|] eqn:Hrank.
    - pose proof (schedule_T_forallb_in _
        (fun x => schedule_write_cut pol rank (S.key_code x)) _
        (S.target p r :: S.sides p r) _
        (cut_callback_time_bound p pol r rank Hwf Hr Hmaximum)) as Hwrites.
      clear - Hdeps Htarget Hsides Hmap Hreadtime Hwrites.
      cbn [length] in Hwrites.
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add,
        ?time_of_nat_succ in *.
      eapply N.le_trans; [|exact (schedule_cut_row_arithmetic S.c_sys
        (N.of_nat (S.kw p)) (N.of_nat (prio_width p pol))
        (N.of_nat (length (S.deps p r))) (N.of_nat (length (S.sides p r)))
        (S.row_work p 0))].
      lia.
    - clear - Hdeps Htarget Hsides Hmap Hreadtime.
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_add,
        ?time_of_nat_succ in *.
      eapply N.le_trans; [|exact (schedule_cut_row_arithmetic S.c_sys
        (N.of_nat (S.kw p)) (N.of_nat (prio_width p pol))
        (N.of_nat (length (S.deps p r))) (N.of_nat (length (S.sides p r)))
        (S.row_work p 0))].
      lia.
  Qed.

  (** Row traversal preserves the linear read-and-write occurrence budget. *)
  Lemma cut_rows_time_bound p pol rs : S.wf p -> incl rs (S.rows p) ->
    (List.T_forallb (schedule_cut_row S.key_code (S.target p) (S.deps p) (S.sides p) pol)
      (fun r => T_schedule_cut_row S.key_code S.T_key_code (S.target p) (S.T_target p)
        (S.deps p) (S.T_deps p) (S.sides p) (S.T_sides p) pol r) rs <=
      256 * (S.c_sys + 1) *
        (N.of_nat ((fold_right Nat.add 0 (map (fun r => length (S.deps p r) +
          length (S.sides p r) + 2) rs) + 1)%nat) *
          N.of_nat (S.kw p + prio_width p pol + 1) +
          N.of_nat (length rs) * (S.row_work p 0 + 1)))%N.
  Proof.
    intro Hwf; induction rs as [|r rs IH]; intro Hincl.
    - time_step.
    - pose proof (cut_row_time_bound p pol r Hwf (Hincl r (or_introl eq_refl))) as Hrow.
      pose proof (IH (fun x Hx => Hincl x (or_intror Hx))) as Htail.
      time_step.
  Qed.

  (** A row's cut units are its declared occurrences plus one traversal unit. *)
  Lemma cut_row_units p rs :
    fold_right Nat.add 0 (map (fun r => length (S.deps p r) + length (S.sides p r) + 2) rs) =
    length rs + fold_right Nat.add 0
      (map (fun r => length (S.deps p r) + length (S.sides p r) + 1) rs).
  Proof.
    induction rs as [|r rs IH]; cbn [map fold_right length]; lia.
  Qed.

  (** Reading the row list and checking its rows fits the public cut budget. *)
  Lemma cuts_time_bound p pol : S.wf p ->
    (T_cuts p pol <= 1024 * (S.c_sys + 1) *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    intro Hwf.
    pose proof (cut_rows_time_bound p pol (S.rows p) Hwf (fun x Hx => Hx)) as Hfold.
    rewrite cut_row_units in Hfold.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    unfold T_cuts; cbn beta iota zeta.
    match type of Hfold with (?t <= _)%N =>
      lazymatch goal with |- (_ <= ?bound)%N =>
        change (1 + (S.T_rows p + t) <= bound)%N
      end
    end.
    unfold row_count, occurrence_count; clear - Hfold Hrows.
    rewrite ?Nat2N.inj_add in *; nia.
  Qed.

  Definition c_sched : N :=
    32768 * (S.c_sys + G.c_prepare + W.c_wto + PTrieT.c_trie + 1).

  (** Dependency graph construction charges every declared occurrence. *)
  Lemma T_dep_graph_le : forall p, S.wf p ->
    (T_dep_graph p <= c_sched * (N.of_nat (row_count p + occurrence_count p +
      edge_count p + 1) * N.of_nat (S.kw p + 1) +
      N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    intros p Hwf; pose proof (dep_graph_time_bound p Hwf) as Hbound.
    unfold c_sched; nia.
  Qed.

  (** WTO conversion charges traversal, ranks and encoded vertices. *)
  Lemma T_of_wto_le : forall w cfg wp n,
    (T_of_wto w cfg wp n <= c_sched * N.of_nat (length (wto_order w) + 1) *
      N.of_nat (vertex_width (wto_order w) + Nat.log2 (length (wto_order w)) + 1))%N.
  Proof.
    intros w cfg wp n; pose proof (of_wto_time_bound w cfg wp n) as Hbound.
    unfold c_sched; nia.
  Qed.

  (** Cut checking is linear in declared occurrences and program key width. *)
  Lemma T_cuts_le : forall p pol, S.wf p ->
    (T_cuts p pol <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + 1) *
        N.of_nat (S.kw p + prio_width p pol + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    intros p pol Hwf; pose proof (cuts_time_bound p pol Hwf) as Hbound.
    unfold c_sched; nia.
  Qed.

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

  Definition k_graph : N := 1024 * (S.c_sys + PTrieT.c_trie + 1).
  Definition k_heads : N := 8%N.
  Definition k_cuts : N := 1024 * (S.c_sys + 1).
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
  Proof.
    exact dep_graph_time_bound.
  Qed.

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
  Proof.
    exact cuts_time_bound.
  Qed.

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

  (** Distinct accepted identifiers bound the logarithm of the emitted rank count. *)
  Lemma checked_order_log_width p w : S.wf p ->
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    Nat.log2 (length (wto_order w)) <= S.kw p.
  Proof.
    intros Hwf Hcheck.
    destruct (F12_checked_size p w Hcheck) as [Hlength Hwidth].
    pose proof (F10_width p Hwf) as Hgraph_width.
    assert (Hcount : length (wto_order w) <= 2 ^ S.kw p).
    { apply schedule_key_count; [exact (proj1 (W.check_sound _ _ _ Hcheck))|].
      intros v Hv; pose proof (schedule_vertex_width_member _ _ Hv); lia. }
    pose proof (Nat.log2_le_mono _ _ Hcount) as Hlog.
    rewrite Nat.log2_pow2 in Hlog by lia; exact Hlog.
  Qed.

  (** Accepted conversion is linear in program occurrences and bounded rank widths. *)
  Lemma checked_conversion_time p w cfg wp n : S.wf p ->
    W.check (G.prepare (dep_graph p)) (verts (dep_graph p)) w = true ->
    (T_of_wto w cfg wp n <= 16 * (W.c_wto + PTrieT.c_trie + 4) *
      N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
      N.of_nat (S.kw p + 1))%N.
  Proof.
    intros Hwf Hcheck.
    pose proof (of_wto_time_bound w cfg wp n) as Htime.
    destruct (F12_checked_size p w Hcheck) as [Hlength Hwidth].
    destruct (F9_graph_sizes p) as [Hvertices Hedges].
    pose proof (F10_width p Hwf) as Hgraph_width.
    pose proof (checked_order_log_width p w Hwf Hcheck) as Hlog.
    assert (Hcount : (N.of_nat (length (wto_order w) + 1) <=
      N.of_nat (row_count p + occurrence_count p + edge_count p + 1))%N)
      by (apply time_of_nat_le; lia).
    assert (Hbits : (N.of_nat (vertex_width (wto_order w) +
      Nat.log2 (length (wto_order w)) + 1) <= 2 * N.of_nat (S.kw p + 1))%N).
    { replace (2 * N.of_nat (S.kw p + 1))%N with (N.of_nat (2 * (S.kw p + 1)))
        by (rewrite Nat2N.inj_mul; reflexivity).
      apply time_of_nat_le; lia. }
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans with (m :=
      (8 * (W.c_wto + PTrieT.c_trie + 4) *
        N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        (2 * N.of_nat (S.kw p + 1)))%N).
    - apply N.mul_le_mono; [apply N.mul_le_mono_l; exact Hcount|exact Hbits].
    - nia.
  Qed.

  (** Planning pays for graph preparation and the nesting depth of the built WTO. *)
  Lemma T_plan_le : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
        N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
        N.of_nat (S.kw p + 1) +
        N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    intros p cfg wp n Hwf.
    set (size := N.of_nat (row_count p + occurrence_count p + edge_count p + 1)).
    set (width := N.of_nat (S.kw p + 1)).
    set (depth := N.of_nat (wto_depth
      (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1)).
    destruct (F9_graph_sizes p) as [Hvertices Hedges].
    pose proof (F10_width p Hwf) as Hgraph_width.
    pose proof (schedule_graph_vertex_width (dep_graph p)) as Hroot_width.
    assert (Hprepare_size : (N.of_nat (graph_n (dep_graph p) +
      graph_e (dep_graph p) + 1) <= size)%N)
      by (unfold size; apply time_of_nat_le; clear - Hvertices Hedges; lia).
    assert (Hwto_size : (N.of_nat (graph_n (dep_graph p) + graph_e (dep_graph p) +
      length (verts (dep_graph p)) + 1) <= 2 * size)%N).
    { assert (Hroots : length (verts (dep_graph p)) = graph_n (dep_graph p))
        by (destruct (dep_graph p); reflexivity).
      unfold size.
      replace (2 * N.of_nat (row_count p + occurrence_count p + edge_count p + 1))%N with
        (N.of_nat (2 * (row_count p + occurrence_count p + edge_count p + 1)))
        by (rewrite Nat2N.inj_mul; reflexivity).
      apply time_of_nat_le; rewrite Hroots; clear - Hvertices Hedges; lia. }
    assert (Hprepare_width : (N.of_nat (graph_width (dep_graph p) + 1) <= width)%N)
      by (unfold width; apply time_of_nat_le; clear - Hgraph_width; lia).
    assert (Hwto_width : (N.of_nat (graph_max (graph_width (dep_graph p))
      (vertex_width (verts (dep_graph p))) + 1) <= width)%N).
    { unfold width; apply time_of_nat_le; rewrite schedule_max_eq.
      clear - Hgraph_width Hroot_width; lia. }
    assert (Hprepare : (G.T_prepare (dep_graph p) <= G.c_prepare * size * width)%N).
    { eapply N.le_trans; [apply G.T_prepare_le|].
      apply N.mul_le_mono;
        [apply N.mul_le_mono_l; exact Hprepare_size|exact Hprepare_width]. }
    assert (Hbuild : (W.T_build (G.prepare (dep_graph p)) (verts (dep_graph p)) <=
      2 * W.c_wto * size * depth * width)%N).
    { pose proof (W.T_build_le (G.prepare (dep_graph p)) (verts (dep_graph p))) as Htime.
      rewrite G.prepare_base in Htime; fold depth in Htime.
      eapply N.le_trans; [exact Htime|].
      replace (2 * W.c_wto * size * depth * width)%N with
        (W.c_wto * (2 * size) * depth * width)%N by (clear - size depth width; nia).
      apply N.mul_le_mono; [|exact Hwto_width].
      apply N.mul_le_mono_r; apply N.mul_le_mono_l; exact Hwto_size. }
    assert (Hcheck_time : (W.T_check (G.prepare (dep_graph p)) (verts (dep_graph p))
      (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) <=
      2 * W.c_wto * size * width)%N).
    { pose proof (W.T_check_le (G.prepare (dep_graph p)) (verts (dep_graph p))
        (W.build (G.prepare (dep_graph p)) (verts (dep_graph p)))) as Htime.
      rewrite G.prepare_base in Htime; eapply N.le_trans; [exact Htime|].
      replace (2 * W.c_wto * size * width)%N with
        (W.c_wto * (2 * size) * width)%N by (clear - size width; nia).
      apply N.mul_le_mono; [apply N.mul_le_mono_l; exact Hwto_size|exact Hwto_width]. }
    assert (Hconvert : ((if W.check (G.prepare (dep_graph p)) (verts (dep_graph p))
      (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) then
      T_of_wto (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) cfg wp n else 0) <=
      16 * (W.c_wto + PTrieT.c_trie + 4) * size * width)%N).
    { destruct (W.check (G.prepare (dep_graph p)) (verts (dep_graph p))
        (W.build (G.prepare (dep_graph p)) (verts (dep_graph p)))) eqn:Hcheck.
      - apply checked_conversion_time; assumption.
      - apply N.le_0_l. }
    pose proof (T4_plan_phases p cfg wp n) as Hphases.
    pose proof (T1_graph p Hwf) as Hgraph.
    cbn zeta in Hphases; unfold k_plan in Hphases; unfold k_graph in Hgraph.
    fold size width in Hgraph; unfold c_sched; fold size width depth.
    assert (Hsize : (1 <= size)%N) by (apply schedule_width_positive).
    assert (Hwidth : (1 <= width)%N) by (apply schedule_width_positive).
    assert (Hdepth : (1 <= depth)%N) by (apply schedule_width_positive).
    assert (Hgrowing : (size * width <= size * depth * width)%N)
      by (clear - Hdepth; nia).
    assert (Hnonempty : (1 <= size * depth * width)%N)
      by (clear - Hsize Hwidth Hdepth; nia).
    pose proof (schedule_plan_arithmetic S.c_sys G.c_prepare W.c_wto PTrieT.c_trie
      (size * width) (size * depth * width)
      (N.of_nat (row_count p) * (S.row_work p 0 + 1)) Hgrowing Hnonempty) as Harithmetic.
    clear - Hprepare Hbuild Hcheck_time Hconvert Hphases Hgraph Harithmetic.
    eapply N.le_trans; [|exact Harithmetic].
    eapply N.le_trans; [exact Hphases|].
    apply N.mul_le_mono_l; rewrite ?N.mul_assoc in *.
    apply N.add_le_mono; [|reflexivity].
    apply N.add_le_mono; [|exact Hconvert].
    apply N.add_le_mono; [|exact Hcheck_time].
    apply N.add_le_mono; [|exact Hbuild].
    apply N.add_le_mono; [exact Hgraph|exact Hprepare].
  Qed.

  (** The phase bounds discharge the unchanged public schedule contract. *)
  Lemma T5_plan_public : forall p cfg wp n, S.wf p ->
    (T_plan p cfg wp n <= c_sched *
      (N.of_nat (row_count p + occurrence_count p + edge_count p + 1) *
       N.of_nat (wto_depth (W.build (G.prepare (dep_graph p)) (verts (dep_graph p))) + 1) *
       N.of_nat (S.kw p + 1) +
       N.of_nat (row_count p) * (S.row_work p 0 + 1)))%N.
  Proof.
    exact T_plan_le.
  Qed.
End ScheduleT.
