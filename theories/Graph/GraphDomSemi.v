(** * One discovery-ranked dominance prologue

    Virtual preparation and one search feed a reverse-order link/eval settlement pass.
    For example, ranks at a diamond's join share the branch vertex as their settled minimum.
    Builds on: GraphDomVirtual, GraphDomErase, GraphDomLink and the public search engine. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseIndex.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSearch GraphSearchExact GraphReach GraphDomVirtual GraphDomErase GraphDomLink.
Import List.ListNotations Cost.Notations.

Module DomSemi.

(** Ranked rows retain original labels beside every converted source-rank occurrence. *)
Record layout (L : Type) := Layout {
  reverse_order : list positive;
  parents : Map.t positive positive;
  predecessors : Map.t positive (list (L * positive));
  real_ids : Map.t positive positive
}.
Arguments Layout {L}.
Arguments reverse_order {L}.
Arguments parents {L}.
Arguments predecessors {L}.
Arguments real_ids {L}.

Definition empty_layout {L} : layout L := Layout [] Map.empty Map.empty Map.empty.

(** Sources not discovered by the single search have no rank and are filtered explicitly. *)
Definition ranked_predecessors_c {V E} (q : Prepared.t V E) (r : Search.result E) v :=
  let* incoming := Prepared.pred_edges_c q v in
  filter_map_c (fun eu =>
    let '(e, u) := eu in
    let* rank := Map.get_c positive_encoding u (Search.pre_num r) in
    Cost.ret (option_map (fun rank => (e, rank)) rank)) incoming.

(** Every retained occurrence carries its original label and the actual recorded source rank. *)
Theorem ranked_predecessors_equation {V E} (q : Prepared.t V E) (r : Search.result E) v :
  Cost.value (ranked_predecessors_c q r v) =
    filter_map (fun eu =>
      option_map (fun rank => (fst eu, rank))
        (Map.get positive_encoding (snd eu) (Search.pre_num r))) (Prepared.pred_edges q v).
Proof.
  unfold ranked_predecessors_c. autorewrite with galois_cost.
  fold (Prepared.pred_edges q v). unfold filter_map.
  induction (Prepared.pred_edges q v) as [|[e u] rest IH]; [reflexivity|].
  cbn [fold_right fst snd]. autorewrite with galois_cost.
  fold (Map.get positive_encoding u (Search.pre_num r)).
  destruct (Map.get positive_encoding u (Search.pre_num r)); now rewrite IH.
Qed.

Local Lemma filter_map_in {A B} (f : A -> option B) xs y :
  In y (filter_map f xs) <-> exists x, In x xs /\ f x = Some y.
Proof.
  unfold filter_map. induction xs as [|x rest IH]; cbn [fold_right]; [firstorder|].
  destruct (f x) as [b|] eqn:Hx; cbn [In]; rewrite IH; split.
  - intros [<-|[a [Ha Hfa]]]; [exists x; auto|exists a; auto].
  - intros [a [[<-|Ha] Hfa]]; [left; congruence|right; exists a; auto].
  - intros [a [Ha Hfa]]. exists a. auto.
  - intros [a [[<-|Ha] Hfa]]; [congruence|exists a; auto].
Qed.

(** Ranked predecessor membership retains exactly every labelled occurrence with a present source rank. *)
Theorem ranked_predecessors_spec {V E} (q : Prepared.t V E) (r : Search.result E) v e k :
  In (e, k) (Cost.value (ranked_predecessors_c q r v)) <->
    exists u, In (e, u) (Prepared.pred_edges q v) /\
      Map.get positive_encoding u (Search.pre_num r) = Some k.
Proof.
  rewrite ranked_predecessors_equation, filter_map_in.
  split.
  - intros [[label u] [Hin Hrank]]. cbn [fst snd] in Hrank.
    destruct (Map.get positive_encoding u (Search.pre_num r)) as [rank|] eqn:Hget;
      [|discriminate].
    injection Hrank as <- <-. exists u. auto.
  - intros [u [Hin Hrank]]. exists (e, u). split; [exact Hin|].
    cbn [fst snd]. now rewrite Hrank.
Qed.

(** Layout construction charges parent conversion, incoming conversion and real-ID transport. *)
Definition layout_step_c {V E} (p : Prepared.t V E)
    (q : Prepared.t (option V) (E + V)) (r : Search.result (E + V))
    (st : layout (E + V)) v :=
  let* rank := Map.get_c positive_encoding v (Search.pre_num r) in
  match rank with
  | None => Cost.ret st
  | Some rank =>
    let* incoming := ranked_predecessors_c q r v in
    let* predecessors := Map.set_c positive_encoding rank incoming (predecessors st) in
    let* via := Map.get_c positive_encoding v (Search.parent_edge r) in
    let* parents :=
      match via with
      | None => Cost.ret (parents st)
      | Some (_, u) =>
        let* parent_rank := Map.get_c positive_encoding u (Search.pre_num r) in
        match parent_rank with
        | None => Cost.ret (parents st)
        | Some parent_rank => Map.set_c positive_encoding rank parent_rank (parents st)
        end
      end in
    let* real := DomErase.real_id_c p q v in
    let* real_ids :=
      match real with
      | None => Cost.ret (real_ids st)
      | Some original => Map.set_c positive_encoding rank original (real_ids st)
      end in
    Cost.ret (Layout (rank :: reverse_order st) parents predecessors real_ids)
  end.

Definition layout_c {V E} (p : Prepared.t V E)
    (q : Prepared.t (option V) (E + V)) (r : Search.result (E + V)) :=
  fold_left_c (layout_step_c p q r) (Search.preorder r) empty_layout.

(** A present labelled search parent converts through its actual recorded source rank. *)
Definition parent_rank {L} (r : Search.result L) v :=
  match Map.get positive_encoding v (Search.parent_edge r) with
  | None => None
  | Some (_, u) => Map.get positive_encoding u (Search.pre_num r)
  end.

(** Parent-rank conversion has no value when either required recorded lookup is absent. *)
Theorem parent_rank_equation {L} (r : Search.result L) v :
  parent_rank r v =
    match Map.get positive_encoding v (Search.parent_edge r) with
    | None => None
    | Some (_, u) => Map.get positive_encoding u (Search.pre_num r)
    end.
Proof.
  reflexivity.
Qed.

(** Each layout step inserts only a successfully converted labelled parent. *)
Theorem layout_step_parents {V E} (p : Prepared.t V E) q r st v :
  parents (Cost.value (layout_step_c p q r st v)) =
    match Map.get positive_encoding v (Search.pre_num r), parent_rank r v with
    | Some rank, Some parent => Map.set positive_encoding rank parent (parents st)
    | _, _ => parents st
    end.
Proof.
  unfold layout_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Search.pre_num r)).
  rewrite parent_rank_equation.
  destruct (Map.get positive_encoding v (Search.pre_num r)); [|reflexivity].
  autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Search.parent_edge r)).
  destruct (Map.get positive_encoding v (Search.parent_edge r)) as [[e u]|];
    autorewrite with galois_cost; [|reflexivity].
  fold (Map.get positive_encoding u (Search.pre_num r)).
  destruct (Map.get positive_encoding u (Search.pre_num r)); reflexivity.
Qed.

(** The stored reverse order adds exactly the successfully read discovery rank at each step. *)
Theorem layout_step_order {V E} (p : Prepared.t V E) q r st v :
  reverse_order (Cost.value (layout_step_c p q r st v)) =
    match Map.get positive_encoding v (Search.pre_num r) with
    | None => reverse_order st
    | Some rank => rank :: reverse_order st
    end.
Proof.
  unfold layout_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Search.pre_num r)).
  destruct (Map.get positive_encoding v (Search.pre_num r)); reflexivity.
Qed.

(** The actual parent index is the insertion fold of the two recorded rank conversions. *)
Theorem layout_parents {V E} (p : Prepared.t V E) q r :
  parents (Cost.value (layout_c p q r)) =
    fold_left (fun parent_map v =>
      match Map.get positive_encoding v (Search.pre_num r), parent_rank r v with
      | Some rank, Some parent => Map.set positive_encoding rank parent parent_map
      | _, _ => parent_map
      end) (Search.preorder r) Map.empty.
Proof.
  unfold layout_c. rewrite value_fold_left_c.
  assert (Hfold : forall xs st,
    parents (fold_left (fun st v => Cost.value (layout_step_c p q r st v)) xs st) =
      fold_left (fun parent_map v =>
        match Map.get positive_encoding v (Search.pre_num r), parent_rank r v with
        | Some rank, Some parent => Map.set positive_encoding rank parent parent_map
        | _, _ => parent_map
        end) xs (parents st)).
  { intro xs. induction xs as [|v rest IH]; intro st; [reflexivity|].
    cbn [fold_left]. rewrite IH, layout_step_parents. reflexivity. }
  apply Hfold.
Qed.

(** This proof-reference list contains each successful rank conversion in input order. *)
Definition ranks_of (f : positive -> option positive) xs :=
  fold_right (fun v tail =>
    match f v with
    | None => tail
    | Some rank => rank :: tail
    end) [] xs.

(** Empty rank conversion has no occurrences. *)
Theorem ranks_of_nil f : ranks_of f [] = [].
Proof.
  reflexivity.
Qed.

(** Rank conversion preserves an input occurrence exactly when its lookup succeeds. *)
Theorem ranks_of_cons f v xs :
  ranks_of f (v :: xs) =
    match f v with
    | None => ranks_of f xs
    | Some rank => rank :: ranks_of f xs
    end.
Proof.
  reflexivity.
Qed.

(** The reverse settlement order is exactly the reversed successful search-rank list. *)
Theorem layout_order {V E} (p : Prepared.t V E) q r :
  reverse_order (Cost.value (layout_c p q r)) =
    rev (ranks_of (fun v => Map.get positive_encoding v (Search.pre_num r))
      (Search.preorder r)).
Proof.
  unfold layout_c. rewrite value_fold_left_c.
  assert (Hfold : forall xs st,
    reverse_order (fold_left (fun st v => Cost.value (layout_step_c p q r st v)) xs st) =
      rev (ranks_of (fun v => Map.get positive_encoding v (Search.pre_num r)) xs) ++
        reverse_order st).
  { intro xs. induction xs as [|v rest IH]; intro st.
    - rewrite ranks_of_nil. reflexivity.
    - cbn [fold_left]. rewrite IH, layout_step_order, ranks_of_cons.
      destruct (Map.get positive_encoding v (Search.pre_num r)); [|reflexivity].
      cbn [rev]. rewrite <- app_assoc. reflexivity. }
  rewrite Hfold. cbn [empty_layout reverse_order]. now rewrite app_nil_r.
Qed.

(** The real-ID field inserts exactly the successfully ranked and successfully converted vertices. *)
Theorem layout_step_real_ids {V E} (p : Prepared.t V E) q r st v :
  real_ids (Cost.value (layout_step_c p q r st v)) =
    match Map.get positive_encoding v (Search.pre_num r), DomErase.real_id p q v with
    | Some rank, Some original => Map.set positive_encoding rank original (real_ids st)
    | _, _ => real_ids st
    end.
Proof.
  unfold layout_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Search.pre_num r)).
  destruct (Map.get positive_encoding v (Search.pre_num r)); [|reflexivity].
  autorewrite with galois_cost. fold (DomErase.real_id p q v).
  destruct (DomErase.real_id p q v); reflexivity.
Qed.

(** Predecessor rows are stored under the target's actual discovery rank, including empty rows. *)
Theorem layout_step_predecessors {V E} (p : Prepared.t V E) q r st v :
  predecessors (Cost.value (layout_step_c p q r st v)) =
    match Map.get positive_encoding v (Search.pre_num r) with
    | None => predecessors st
    | Some rank => Map.set positive_encoding rank
        (Cost.value (ranked_predecessors_c q r v)) (predecessors st)
    end.
Proof.
  unfold layout_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Search.pre_num r)).
  destruct (Map.get positive_encoding v (Search.pre_num r)); reflexivity.
Qed.

(** The inverse-map field is a fold of the actual rank and real-name conversions. *)
Theorem layout_real_ids {V E} (p : Prepared.t V E) q r :
  real_ids (Cost.value (layout_c p q r)) =
    fold_left (fun inverse v =>
      match Map.get positive_encoding v (Search.pre_num r), DomErase.real_id p q v with
      | Some rank, Some original => Map.set positive_encoding rank original inverse
      | _, _ => inverse
      end) (Search.preorder r) Map.empty.
Proof.
  unfold layout_c. rewrite value_fold_left_c.
  assert (Hfold : forall xs st,
    real_ids (fold_left (fun st v => Cost.value (layout_step_c p q r st v)) xs st) =
      fold_left (fun inverse v =>
        match Map.get positive_encoding v (Search.pre_num r), DomErase.real_id p q v with
        | Some rank, Some original => Map.set positive_encoding rank original inverse
        | _, _ => inverse
        end) xs (real_ids st)).
  { intro xs. induction xs as [|v rest IH]; intro st; [reflexivity|].
    cbn [fold_left]. rewrite IH, layout_step_real_ids. reflexivity. }
  apply Hfold.
Qed.

(** The actual predecessor index is a fold of target-rank conversions and converted labelled rows. *)
Theorem layout_predecessors {V E} (p : Prepared.t V E) q r :
  predecessors (Cost.value (layout_c p q r)) =
    fold_left (fun rows v =>
      match Map.get positive_encoding v (Search.pre_num r) with
      | None => rows
      | Some rank => Map.set positive_encoding rank
          (Cost.value (ranked_predecessors_c q r v)) rows
      end) (Search.preorder r) Map.empty.
Proof.
  unfold layout_c. rewrite value_fold_left_c.
  assert (Hfold : forall xs st,
    predecessors (fold_left (fun st v => Cost.value (layout_step_c p q r st v)) xs st) =
      fold_left (fun rows v =>
        match Map.get positive_encoding v (Search.pre_num r) with
        | None => rows
        | Some rank => Map.set positive_encoding rank
            (Cost.value (ranked_predecessors_c q r v)) rows
        end) xs (predecessors st)).
  { intro xs. induction xs as [|v rest IH]; intro st; [reflexivity|].
    cbn [fold_left]. rewrite IH, layout_step_predecessors. reflexivity. }
  apply Hfold.
Qed.

(** The settlement state separates semidominator data from link/eval metadata. *)
Record state := State {
  semis : Map.t positive positive;
  links : DomLink.t
}.

Definition initial := State Map.empty DomLink.empty.

Definition predecessor_c (settled : Map.t positive positive)
    (acc : DomLink.t * positive) (source : positive) :=
  let '(links, best) := acc in
  let* result := DomLink.eval_c (DomLink.identity_value_c settled) links source in
  let '(links', chosen) := result in
  let* candidate := DomLink.identity_value_c settled chosen in
  let* best' := DomLink.minimum_c (fun rank => Cost.ret rank) best candidate in
  Cost.ret (links', best').

(** Each predecessor uses the actual compressed representative before comparing settled scores. *)
Theorem predecessor_value settled links best source :
  Cost.value (predecessor_c settled (links, best) source) =
    let '(links', chosen) :=
      Cost.value (DomLink.eval_c (DomLink.identity_value_c settled) links source) in
    (links', Cost.value (DomLink.minimum_c (fun rank => Cost.ret rank)
      best (DomLink.identity_value settled chosen))).
Proof.
  unfold predecessor_c. autorewrite with galois_cost.
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c settled) links source)).
  autorewrite with galois_cost. reflexivity.
Qed.

(** A nonroot is settled from its predecessor occurrences before its DFS parent is linked. *)
Definition settle_c {L} (ranked : layout L) (st : state) w :=
  let* parent := Map.get_c positive_encoding w (parents ranked) in
  match parent with
  | None => Cost.ret st
  | Some parent =>
    let* incoming := Index.find_c positive_encoding w (predecessors ranked) in
    let* answer := fold_left_c
      (fun acc eu => predecessor_c (semis st) acc (snd eu))
      incoming (links st, parent) in
    let '(links', best) := answer in
    let* semis := Map.set_c positive_encoding w best (semis st) in
    let* links := DomLink.link_c links' w parent in
    Cost.ret (State semis links)
  end.

(** Settlement reads the actual incoming row and links only after writing the selected minimum. *)
Theorem settle_value {L} (ranked : layout L) st w :
  Cost.value (settle_c ranked st w) =
    match Map.get positive_encoding w (parents ranked) with
    | None => st
    | Some parent =>
      let '(links', best) := fold_left
        (fun acc eu => Cost.value (predecessor_c (semis st) acc (snd eu)))
        (Index.find positive_encoding w (predecessors ranked)) (links st, parent) in
      State (Map.set positive_encoding w best (semis st))
        (Cost.value (DomLink.link_c links' w parent))
    end.
Proof.
  unfold settle_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding w (parents ranked)).
  destruct (Map.get positive_encoding w (parents ranked)); [|reflexivity].
  autorewrite with galois_cost.
  fold (Index.find positive_encoding w (predecessors ranked)).
  destruct (fold_left
    (fun acc eu => Cost.value (predecessor_c (semis st) acc (snd eu)))
    (Index.find positive_encoding w (predecessors ranked)) (links st, p)).
  autorewrite with galois_cost. reflexivity.
Qed.

(** Settlement preserves semidominator-map representation validity on arbitrary intermediate data. *)
Theorem settle_wf {L} (ranked : layout L) st w :
  Map.wf positive_encoding (semis st) ->
  Map.wf positive_encoding (semis (Cost.value (settle_c ranked st w))).
Proof.
  intro Hmap. unfold settle_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding w (parents ranked)).
  destruct (Map.get positive_encoding w (parents ranked)) as [parent|];
    autorewrite with galois_cost; [|exact Hmap].
  destruct (fold_left
    (fun acc eu => Cost.value (predecessor_c (semis st) acc (snd eu)))
    (Cost.value (Index.find_c positive_encoding w (predecessors ranked)))
    (links st, parent)) as [links' best].
  autorewrite with galois_cost. cbn [semis]. now apply Map.wf_set.
Qed.

Local Lemma settle_fold_wf {L} (ranked : layout L) xs :
  forall st, Map.wf positive_encoding (semis st) ->
  Map.wf positive_encoding
    (semis (fold_left (fun st w => Cost.value (settle_c ranked st w)) xs st)).
Proof.
  induction xs as [|w rest IH]; intros st Hmap; [exact Hmap|].
  cbn [fold_left]. apply IH. now apply settle_wf.
Qed.

(** Both finishers receive the same labelled search, ranked layout and settlement state. *)
Record semi (V E : Type) := Semi {
  prepared : Prepared.t (option V) (E + V);
  search : Search.result (E + V);
  ranked : layout (E + V);
  settled : state
}.
Arguments Semi {V E}.
Arguments prepared {V E}.
Arguments search {V E}.
Arguments ranked {V E}.
Arguments settled {V E}.

(** The prologue builds the virtual graph once and performs exactly one input-graph search. *)
Definition semi_c {V E} (p : Prepared.t V E) : Cost.t (semi V E) :=
  let* q := DomVirtual.virtual_c p in
  let* run := SearchRun.run_c q Visitor.noop Reach.unrestricted (Prepared.entry_ids q) tt in
  let r := fst run in
  let* ranked := layout_c p q r in
  let* settled := fold_left_c (settle_c ranked) (reverse_order ranked) initial in
  Cost.ret (Semi q r ranked settled).

Definition compute {V E} (p : Prepared.t V E) := Cost.value (semi_c p).

(** A ranked arc observes an actual retained labelled predecessor occurrence. *)
Definition ranked_arc {V E} (shared : semi V E) u e v : Prop :=
  In (e, u) (Index.find positive_encoding v (predecessors (ranked shared))).

(** The shared settlement always constructs canonical semidominator-map storage. *)
Theorem semidominators_wf {V E} (p : Prepared.t V E) :
  Map.wf positive_encoding (semis (settled (compute p))).
Proof.
  unfold compute, semi_c. autorewrite with galois_cost.
  cbn [settled]. apply settle_fold_wf. apply Map.wf_empty.
Qed.

(** The stored prepared graph is exactly the single constructed virtual value. *)
Theorem prepared_equation {V E} (p : Prepared.t V E) :
  prepared (compute p) = DomVirtual.virtual p.
Proof.
  reflexivity.
Qed.

(** The stored search is the actual noop-visitor run on the stored virtual prepared graph. *)
Theorem search_equation {V E} (p : Prepared.t V E) :
  search (compute p) =
    fst (Cost.value (SearchRun.run_c (DomVirtual.virtual p) Visitor.noop Reach.unrestricted
      (Prepared.entry_ids (DomVirtual.virtual p)) tt)).
Proof.
  reflexivity.
Qed.

(** The stored ranked layout is the actual conversion of the stored labelled search. *)
Theorem ranked_equation {V E} (p : Prepared.t V E) :
  ranked (compute p) =
    Cost.value (layout_c p (prepared (compute p)) (search (compute p))).
Proof.
  reflexivity.
Qed.

(** The shared state is the reverse fold over the same stored ranked layout. *)
Theorem settled_equation {V E} (p : Prepared.t V E) :
  settled (compute p) =
    fold_left (fun st w => Cost.value (settle_c (ranked (compute p)) st w))
      (reverse_order (ranked (compute p))) initial.
Proof.
  unfold compute, semi_c. autorewrite with galois_cost. reflexivity.
Qed.

(** The prologue's actual search satisfies the public exactness contract on every ready input. *)
Theorem search_exact {V E} (p : Prepared.t V E) :
  Prepared.ready p ->
  Search.exact (prepared (compute p)) Reach.unrestricted
    (Prepared.entry_ids (prepared (compute p))) (search (compute p)).
Proof.
  intro Hready. rewrite prepared_equation, search_equation.
  apply SearchExact.run_exact. now apply DomVirtual.virtual_ready.
Qed.

(** The actual search gives every discovered virtual ID one distinct recorded discovery rank. *)
Theorem discovery_rank_injective {V E} (p : Prepared.t V E) u v k :
  Prepared.ready p ->
  Map.get positive_encoding u (Search.pre_num (search (compute p))) = Some k ->
  Map.get positive_encoding v (Search.pre_num (search (compute p))) = Some k -> u = v.
Proof.
  intros Hready Hu Hv.
  apply (Search.pre_num_index _ _ _ _ (search_exact p Hready)) in Hu, Hv.
  congruence.
Qed.

(** A missing source rank means semantic entry-unreachability, with no replacement rank assigned. *)
Theorem missing_rank_unreachable {V E} (p : Prepared.t V E) n u :
  Prepared.ready p ->
  Prepared.id_of (prepared (compute p)) n = Some u ->
  Map.get positive_encoding u (Search.pre_num (search (compute p))) = None ->
  ~ reachable (Prepared.graph (prepared (compute p))) n.
Proof.
  intros Hready Hname Hmissing Hreachable.
  pose proof (DomVirtual.virtual_ready p Hready) as Hq.
  rewrite <- prepared_equation in Hq.
  pose proof (proj2 (Reach.entries_exact _ n u Hq Hname) Hreachable) as Hseen.
  apply (Reach.exact _ _ _ u Hq) in Hseen.
  apply (Search.pre_complete _ _ _ _ (search_exact p Hready)) in Hseen.
  apply In_nth_error in Hseen. destruct Hseen as [k Hk].
  assert (Hrank :
    Map.get positive_encoding u (Search.pre_num (search (compute p))) =
      Some (Pos.of_succ_nat k)).
  { apply (Search.pre_num_index _ _ _ _ (search_exact p Hready)).
    rewrite SuccNat2Pos.id_succ. exact Hk. }
  congruence.
Qed.

(** Ranked-output erasure uses the inverse map constructed by this same prologue. *)
Definition erase_c {V E} (shared : semi V E) parents :=
  DomErase.with_c
    (fun rank => Map.get_c positive_encoding rank (real_ids (ranked shared))) parents.

Definition erase {V E} (shared : semi V E) parents := Cost.value (erase_c shared parents).

(** Ranked erasure rebuilds canonical sentinel-free storage for every computational prologue. *)
Theorem erase_wf {V E} (shared : semi V E) parents :
  Map.wf positive_encoding (erase shared parents).
Proof.
  apply DomErase.with_wf.
Qed.

End DomSemi.
