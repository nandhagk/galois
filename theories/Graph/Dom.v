(** * Low-high dominator certificates

    The checker validates preorder intervals and low-high witnesses independently of production.
    For example, a direct parent edge supplies the low-high witness of its child.
    Builds on: first-order graphs, canonical tries and dominator certificate signatures. *)

From Stdlib Require Import List Bool PArith NArith Sorting.Sorted.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig DomSig DomProducer DomOrder.
Import List.ListNotations.

Module N.
  TimeFun N.min.
  TimeFun N.max.
End N.

Fixpoint dom_key_fits (width : nat) (v : positive) : bool :=
  match width, v with
  | O, _ => false
  | S _, xH => true
  | S rest, xO tail | S rest, xI tail => dom_key_fits rest tail
  end.
TimeFun dom_key_fits.

(** Structural comparison recurses on the bounded reconstructed candidate. *)
Fixpoint dom_map_eq_ne (expected candidate : trie_ne positive) : bool :=
  match expected, candidate with
  | N001 r, N001 r' => dom_map_eq_ne r r'
  | N010 v, N010 v' => Pos.eqb v v'
  | N011 v r, N011 v' r' => Pos.eqb v v' && dom_map_eq_ne r r'
  | N100 l, N100 l' => dom_map_eq_ne l l'
  | N101 l r, N101 l' r' => dom_map_eq_ne l l' && dom_map_eq_ne r r'
  | N110 l v, N110 l' v' => dom_map_eq_ne l l' && Pos.eqb v v'
  | N111 l v r, N111 l' v' r' =>
    dom_map_eq_ne l l' && Pos.eqb v v' && dom_map_eq_ne r r'
  | _, _ => false
  end.
TimeFun dom_map_eq_ne.

Definition dom_map_eq (expected candidate : ptrie positive) : bool :=
  match expected, candidate with
  | Empty, Empty => true
  | Nodes a, Nodes b => dom_map_eq_ne a b
  | _, _ => false
  end.
TimeFun dom_map_eq.

Definition dom_scan (g : prepared) : dom_scan_data :=
  DomScanData (fold_left (fun acc v => PTrieCode.set v true acc) (nodes g) Empty)
    (graph_n (base g)) (graph_e (base g)) (graph_width (base g)).
TimeFun dom_scan.

Record dom_read_state := DomReadState {
  read_remaining : list positive;
  read_budget : N;
  read_next : N;
  read_positions : ptrie N
}.
TimeFun read_remaining.
TimeFun read_budget.
TimeFun read_next.
TimeFun read_positions.

Definition dom_read_step (width : nat) (listed : ptrie bool) (s : dom_read_state)
    : dom_read_state + option (ptrie N) :=
  match s with
  | DomReadState [] _ _ pos => inr (Some pos)
  | DomReadState (v :: rest) budget next pos =>
    if N.eqb budget 0%N then inr None else
      if dom_key_fits width v then
        match trie_get v listed, trie_get v pos with
        | Some _, None => inl (DomReadState rest (N.pred budget) (N.succ next)
            (PTrieCode.set v next pos))
        | _, _ => inr None
        end
      else inr None
  end.
TimeFun dom_read_step.

Definition dom_read_order (count width : nat) (listed : ptrie bool) (o : list positive)
    (next : N) (pos : ptrie N) : option (ptrie N) :=
  let budget := N.of_nat count in
  match loopN (dom_read_step width listed) (N.succ budget) (DomReadState o budget next pos) with
  | inl _ => None
  | inr result => result
  end.
TimeFun dom_read_order.


Definition dom_read_known (info : dom_scan_data) (r : positive)
    (o : list positive) : option (ptrie N) :=
  match o with
  | [] => None
  | h :: _ =>
    if dom_key_fits (dom_width info) r then
      if Pos.eqb h r then
        dom_read_order (dom_count info) (dom_width info) (dom_listed info) o 0%N Empty
      else None
    else None
  end.
TimeFun dom_read_known.

Definition dom_read (g : prepared) (r : positive) (o : list positive) :=
  dom_read_known (dom_scan g) r o.
TimeFun dom_read.

Definition dom_rebuild (width : nat) (r : positive) (m : ptrie positive)
    (pos : ptrie N) (acc : option (ptrie positive)) (v : positive)
    : option (ptrie positive) :=
  match acc with
  | None => None
  | Some built =>
    if Pos.eqb v r then
      match trie_get v m with None => Some built | Some _ => None end
    else
      match trie_get v m with
      | None => None
      | Some p =>
        if dom_key_fits width p then
          match trie_get p pos, trie_get v pos with
          | Some pp, Some pv => if N.ltb pp pv then Some (PTrieCode.set v p built) else None
          | _, _ => None
          end
        else None
      end
  end.
TimeFun dom_rebuild.

Definition dom_map_check_known (info : dom_scan_data) (r : positive) (m : ptrie positive)
    (o : list positive) : bool :=
  match dom_read_known info r o with
  | None => false
  | Some pos =>
    match fold_left (dom_rebuild (dom_width info) r m pos) o (Some Empty) with
    | None => false
    | Some built => dom_map_eq built m
    end
  end.
TimeFun dom_map_check_known.

Definition dom_map_check (g : prepared) (r : positive) (m : ptrie positive)
    (o : list positive) := dom_map_check_known (dom_scan g) r m o.
TimeFun dom_map_check.

Definition dom_size_get (sizes : ptrie N) (v : positive) : N :=
  match trie_get v sizes with Some n => n | None => 1%N end.
TimeFun dom_size_get.

Definition dom_add_size (m : ptrie positive) (sizes : ptrie N) (v : positive) : ptrie N :=
  let own := dom_size_get sizes v in
  let sizes := PTrieCode.set v own sizes in
  match trie_get v m with
  | None => sizes
  | Some p => PTrieCode.set p (N.add (dom_size_get sizes p) own) sizes
  end.
TimeFun dom_add_size.

Definition dom_sizes (m : ptrie positive) (o : list positive) : ptrie N :=
  fold_left (dom_add_size m) (rev_append o []) Empty.
TimeFun dom_sizes.

Definition dom_interval (pos sizes : ptrie N) (u v : positive) : bool :=
  match trie_get u pos, trie_get v pos with
  | Some pu, Some pv => N.leb pu pv &&
      N.leb (N.add pv (dom_size_get sizes v)) (N.add pu (dom_size_get sizes u))
  | _, _ => false
  end.
TimeFun dom_interval.

Definition dom_sizes_ok (m : ptrie positive) (pos sizes : ptrie N) (o : list positive)
    : bool :=
  forallb (fun v => match trie_get v m with
    | None => true
    | Some p => dom_interval pos sizes p v
    end) o.
TimeFun dom_sizes_ok.

Definition dom_edge_update (r : positive) (m : ptrie positive) (pos sizes : ptrie N)
    (u : positive) (acc : option (ptrie (bool * N * N))) (v : positive)
    : option (ptrie (bool * N * N)) :=
  match acc, trie_get u pos, trie_get v pos with
  | Some flags, Some pu, Some _ =>
    if Pos.eqb v r then Some flags else
      match trie_get v m with
      | None => None
      | Some p =>
        if dom_interval pos sizes p u then
          let '(direct, lo, hi) := match trie_get v flags with
            | None => (false, pu, pu)
            | Some info => info
            end in
          Some (PTrieCode.set v (direct || Pos.eqb u p, N.min lo pu, N.max hi pu) flags)
        else None
      end
  | _, _, _ => None
  end.
TimeFun dom_edge_update.

Definition dom_edges_from (g : prepared) (r : positive) (m : ptrie positive)
    (pos sizes : ptrie N) (acc : option (ptrie (bool * N * N))) (u : positive)
    : option (ptrie (bool * N * N)) :=
  fold_left (dom_edge_update r m pos sizes u) (succs (base g) u) acc.
TimeFun dom_edges_from.

Definition dom_low_high (r : positive) (pos sizes : ptrie N)
    (flags : ptrie (bool * N * N)) (v : positive) : bool :=
  if Pos.eqb v r then true else
    match trie_get v pos, trie_get v flags with
    | Some pv, Some (direct, lo, hi) =>
      direct || (N.ltb lo pv && N.leb (N.add pv (dom_size_get sizes v)) hi)
    | _, _ => false
    end.
TimeFun dom_low_high.

Definition dom_edges (g : prepared) (r : positive) (m : ptrie positive)
    (o : list positive) (pos sizes : ptrie N) : bool :=
  match fold_left (dom_edges_from g r m pos sizes) o (Some Empty) with
  | None => false
  | Some flags => forallb (dom_low_high r pos sizes flags) o
  end.
TimeFun dom_edges.

(** Accepted orders can be numbered directly without inspecting the graph again. *)
Definition dom_positions (o : list positive) : ptrie N :=
  snd (fold_left (fun acc v =>
    let '(next, pos) := acc in
    (N.succ next, PTrieCode.set v next pos)) o (0%N, Empty)).
TimeFun dom_positions.

Module DomCode <: DOM_OPS.
  Definition build := dom_build_candidate.

  Definition check (g : prepared) (r : positive) (m : ptrie positive)
      (o : list positive) : bool :=
    let info := dom_scan g in
    match dom_read_known info r o with
    | None => false
    | Some pos =>
      if dom_map_check_known info r m o then
        let sizes := dom_sizes m o in
        dom_sizes_ok m pos sizes o && dom_edges g r m o pos sizes
      else false
    end.

  Definition tree (g : prepared) (r : positive) (m : ptrie positive)
      (o : list positive) : domtree :=
      let pos := dom_positions o in
      let sizes := dom_sizes m o in
      let children := fold_left (fun rows v => match trie_get v m with
        | None => rows
        | Some p => let old := match trie_get p rows with None => [] | Some vs => vs end in
            PTrieCode.set p (v :: old) rows
        end) o Empty in
      let ends := fold_left (fun ends v => match trie_get v pos with
        | None => ends
        | Some pv => PTrieCode.set v (N.pred (N.add pv (dom_size_get sizes v))) ends
        end) o Empty in
      DomTree m (PTrieCode.map (fun vs => rev_append vs []) children) pos ends.

  Definition dominates_b (t : domtree) (u v : positive) : bool :=
    match trie_get u (pre t), trie_get u (post t),
        trie_get v (pre t), trie_get v (post t) with
    | Some a, Some b, Some c, Some d => N.leb a c && N.leb d b
    | _, _, _, _ => false
    end.
End DomCode.

Module Dom <: DOM.
  Include DomCode.
  Include DOM_SPEC.

  Lemma check_sound : forall g r m o, check g r m o = true -> dom_exact g r m.
  Proof. Admitted.

  Lemma tree_idom : forall g r m o, check g r m o = true -> idom (tree g r m o) = m.
  Proof. Admitted.

  Lemma tree_exact : forall g r m o, check g r m o = true -> domtree_exact g r (tree g r m o).
  Proof. Admitted.

  Lemma dominates_b_spec : forall g r m o u v,
    check g r m o = true -> reach (base g) [r] v ->
    reflect (dominates (base g) r u v) (dominates_b (tree g r m o) u v).
  Proof. Admitted.

  Lemma kids_spec : forall g r m o, check g r m o = true -> forall u,
    (forall v, In v (children (tree g r m o) u) <-> trie_get v m = Some u) /\
    NoDup (children (tree g r m o) u) /\
    StronglySorted (preorder_before (tree g r m o)) (children (tree g r m o) u).
  Proof. Admitted.
End Dom.

Module DomT <: DOM_ALL.
  Include Dom.
  TimeFun build.
  TimeFun check.
  TimeFun tree.
  TimeFun dominates_b.
  Definition c_dom : N := 1%N. (* STUB *)

  Definition scan := dom_scan.
  TimeFun scan.
  Definition read := dom_read_known.
  TimeFun read.
  Definition map_check := dom_map_check_known.
  TimeFun map_check.
  Definition sizes := dom_sizes.
  TimeFun sizes.
  Definition sizes_ok := dom_sizes_ok.
  TimeFun sizes_ok.
  Definition edges g m o :=
    match dom_read g (match o with [] => 1%positive | h :: _ => h end) o with
    | None => false
    | Some pos =>
      dom_edges g (match o with [] => 1%positive | h :: _ => h end) m o pos (dom_sizes m o)
    end.
  TimeFun edges.
  Definition pos_of (o : list positive) (v : positive) : N :=
    fst (fold_left (fun acc u =>
      let '(found, next) := acc in
      (if Pos.eqb u v then next else found, N.succ next)) o (0%N, 0%N)).
  TimeFun pos_of.
  Definition size_of m o v := dom_size_get (dom_sizes m o) v.
  TimeFun size_of.
  Definition lt_dfs := dom_lt_dfs.
  TimeFun lt_dfs.
  Definition lt_semi := dom_lt_parents.
  TimeFun lt_semi.
  Definition lt_order := dom_build_order.
  TimeFun lt_order.
  Definition lt_ops := dom_lt_ops.
  TimeFun lt_ops.
  Definition lt_forest := dom_lt_replay.
  Definition lt_init := dom_lt_replay_initial.
  TimeFun lt_init.
  Definition run_ops := dom_lt_run_ops.
  TimeFun run_ops.
  Definition k_scan : N := 1%N. (* STUB *)
  Definition k_read : N := 1%N. (* STUB *)
  Definition k_map : N := 1%N. (* STUB *)
  Definition k_size : N := 1%N. (* STUB *)
  Definition k_edge : N := 1%N. (* STUB *)
  Definition k_tree : N := 1%N. (* STUB *)
  Definition k_dfs : N := 1%N. (* STUB *)
  Definition k_semi : N := 1%N. (* STUB *)
  Definition k_le : N := 1%N. (* STUB *)
  Definition k_order : N := 1%N. (* STUB *)
  Definition k_build : N := 1%N. (* STUB *)
  Definition k_check : N := 1%N. (* STUB *)

  Lemma F0_path_last : forall g a vs b, path g a vs b ->
  (vs = [b] /\ a = b) \/
  exists vs' c, path g a vs' c /\ edge g c b /\ vs = vs' ++ [b].
  Proof. Admitted. (* STUB *)

  Lemma F1_dominates_trans : forall g r x y v,
  dominates g r x y -> dominates g r y v -> dominates g r x v.
  Proof. Admitted. (* STUB *)

  Lemma F2_check_cert : forall g r m o, check g r m o = true -> dom_cert (base g) r m o.
  Proof. Admitted. (* STUB *)

  (** An accepted order holds listed vertices only. *)
  Lemma F2b_check_listed : forall g r m o, check g r m o = true ->
    forall v, In v o -> In v (verts (base g)).
  Proof. Admitted. (* STUB *)

  Lemma F3_anc_before : forall g r m o u v, dom_cert g r m o ->
  tree_anc m u v -> u <> v -> order_before o u v.
  Proof. Admitted. (* STUB *)

  Lemma F4_root_anc : forall g r m o v, dom_cert g r m o -> In v o -> tree_anc m r v.
  Proof. Admitted. (* STUB *)

  Lemma F5_reach_listed : forall g r m o v, dom_cert g r m o ->
  reach g [r] v -> In v o.
  Proof. Admitted. (* STUB *)

  Lemma F6_listed_reach : forall g r m o v, dom_cert g r m o ->
  In v o -> reach g [r] v.
  Proof. Admitted. (* STUB *)

  Lemma F7_anc_dominates : forall g r m o u v, dom_cert g r m o ->
  In v o -> tree_anc m u v -> dominates g r u v.
  Proof. Admitted. (* STUB *)

  Lemma F8_anc_dec : forall g r m o u v, dom_cert g r m o -> In v o ->
  tree_anc m u v \/ ~ tree_anc m u v.
  Proof. Admitted. (* STUB *)

  Lemma F9a_low_path : forall g r m o v, dom_cert g r m o -> In v o ->
  exists vs, path g r vs v /\ forall y, In y vs -> y = v \/ order_before o y v.
  Proof. Admitted. (* STUB *)

  Lemma F9b_high_path : forall g r m o v p, dom_cert g r m o -> trie_get v m = Some p ->
  exists vs, path g p vs v /\
    forall y, In y vs -> y = p \/ y = v \/ order_before o v y.
  Proof. Admitted. (* STUB *)

  Lemma F9c_avoid : forall g r m o x v, dom_cert g r m o -> In v o ->
  ~ tree_anc m x v -> exists vs, path g r vs v /\ ~ In x vs.
  Proof. Admitted. (* STUB *)

  Lemma F9_dominates_anc : forall g r m o x v, dom_cert g r m o ->
  In v o -> dominates g r x v -> tree_anc m x v.
  Proof. Admitted. (* STUB *)

  Lemma F10_cert_exact : forall g r m o, dom_cert (base g) r m o -> dom_exact g r m.
  Proof. Admitted. (* STUB *)

  Lemma F11_intervals : forall g r m o u v, dom_cert g r m o -> In u o -> In v o ->
  (tree_anc m u v <->
   (pos_of o u <= pos_of o v /\ pos_of o v + size_of m o v <= pos_of o u + size_of m o u)%N).
  Proof. Admitted. (* STUB *)

  Lemma F12_tree_exact : forall g r m o, check g r m o = true ->
  domtree_exact g r (tree g r m o).
  Proof. Admitted. (* STUB *)

  Lemma T1_scan : forall g,
    (T_scan g <= k_scan * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_read : forall g r o,
    (T_read (scan g) r o <= k_read * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_map : forall g r m o,
    (T_map_check (scan g) r m o <= k_map * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_sizes : forall g m o, NoDup o -> length o <= graph_n (base g) ->
    (forall v, In v o -> In v (nodes g)) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_sizes m o <= k_size * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_edges : forall g m o, length o <= graph_n (base g) ->
    (forall v, In v o -> In v (verts (base g))) ->
    (forall v p, In v o -> trie_get v m = Some p -> In p o) ->
    (T_edges g m o <= k_edge * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_tree : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= k_tree * N.of_nat ((graph_n (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_dfs : forall g r, prepared_ok g ->
    (T_lt_dfs g r <= k_dfs * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma F13_ops_length : forall g r, prepared_ok g ->
    length (lt_ops g r) <= 2 * (graph_n (base g) + graph_e (base g)) + 1.
  Proof. Admitted. (* STUB *)

  Lemma T8_link_eval : forall g r, prepared_ok g ->
    (T_run_ops (lt_ops g r) (lt_init g r) <= k_le *
      N.of_nat ((length (lt_ops g r) + graph_n (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T9_semi : forall g r, prepared_ok g ->
    (T_lt_semi g r <= k_semi * N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1)) + T_run_ops (lt_ops g r) (lt_init g r))%N.
  Proof. Admitted. (* STUB *)

  Lemma T10_order : forall g r, prepared_ok g ->
    (T_lt_order g r <= k_order *
      N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
        (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_check_le : forall g r m o,
    (T_check g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_tree_le : forall g r m o, check g r m o = true ->
    (T_tree g r m o <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_dominates_b_le : forall t u v,
    (T_dominates_b t u v <= c_dom * N.of_nat (query_width t u v + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_build_le : forall g r, prepared_ok g ->
    (T_build g r <= c_dom * N.of_nat (graph_n (base g) + graph_e (base g) + 1) *
      N.of_nat (Nat.log2 (graph_n (base g)) + 1) * N.of_nat (graph_width (base g) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma check_bigO : bigO (fun _ : prepared * positive * ptrie positive * list positive => True)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_check g r m o).
  Proof. Admitted. (* STUB *)

  Lemma tree_bigO : bigO (fun '(g, r, m, o) => check g r m o = true)
    (fun '(g, _, _, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (graph_width (base g) + 1))) (fun '(g, r, m, o) => T_tree g r m o).
  Proof. Admitted. (* STUB *)

  Lemma dominates_b_bigO : bigO (fun _ : domtree * positive * positive => True)
    (fun '(t, u, v) => N.of_nat (query_width t u v + 1))
    (fun '(t, u, v) => T_dominates_b t u v).
  Proof. Admitted. (* STUB *)

  Lemma build_bigO : bigO (fun '(g, _) => prepared_ok g)
    (fun '(g, _) => N.of_nat ((graph_n (base g) + graph_e (base g) + 1) *
      (Nat.log2 (graph_n (base g)) + 1) * (graph_width (base g) + 1)))
    (fun '(g, r) => T_build g r).
  Proof. Admitted. (* STUB *)

  (** A successful read lists distinct listed vertices within the budget, headed by the root. *)
  Lemma F2c_read : forall g r o pos, read (scan g) r o = Some pos ->
    NoDup o /\ length o <= graph_n (base g) /\ hd_error o = Some r /\
    (forall v, In v o -> In v (nodes g)) /\
    (forall v, In v o -> exists i, trie_get v pos = Some i).
  Proof. Admitted. (* STUB *)

  (** A successful parent check keeps every parent of an ordered vertex in the order. *)
  Lemma F2d_map : forall g r m o, map_check (scan g) r m o = true ->
    forall v p, In v o -> trie_get v m = Some p -> In p o.
  Proof. Admitted. (* STUB *)

  (** Parent containment tests charge each accepted order entry. *)
  Lemma T4b_sizes_ok : forall g r m o pos,
      read (scan g) r o = Some pos -> map_check (scan g) r m o = true ->
      (T_sizes_ok m pos (sizes m o) o <= k_size * N.of_nat ((graph_n (base g) + 1) *
        (graph_width (base g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Building runs the search, the semidominator phases and the order phase. *)
  Lemma T11b_build : forall g r, prepared_ok g ->
      (T_build g r <= T_lt_dfs g r + T_lt_semi g r + T_lt_order g r + k_build)%N.
  Proof. Admitted. (* STUB *)

  (** The checker runs its phases in order and stops at the first rejection. *)
  Lemma T11_check : forall g r m o,
      (T_check g r m o <= k_check * (T_scan g + T_read (scan g) r o +
        T_map_check (scan g) r m o +
        match read (scan g) r o with
        | Some pos => if map_check (scan g) r m o
            then T_sizes m o + T_sizes_ok m pos (sizes m o) o + T_edges g m o else 0
        | None => 0
        end + 1))%N.
  Proof. Admitted. (* STUB *)

End DomT.
