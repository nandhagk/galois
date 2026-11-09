(** * Prepared gen/kill problems

    May and must generators reuse valid set lattices and prepare edge sets once.
    For example, liveness is backward may with uses generated after definitions are killed.
    Builds on: FrameworkDense, BaseIndex and LatticeSet. *)

From Stdlib Require Import List Bool NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore LatticeSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkDense.
Import List.ListNotations Cost.Notations.

Module Bitvector.

(** The universe is support and measure data, independent of the valid runtime carrier. *)
Record t (N E U : Type) := Make {
  cfg : Cfg.t N E;
  fact_enc : encoding U;
  universe : list U;
  dir : direction;
  gen_c : E -> Cost.t (list U);
  kill_c : E -> Cost.t (list U);
  boundary_c : N -> Cost.t (option (list U))
}.
Arguments Make {N E U}.
Arguments cfg {N E U}.
Arguments fact_enc {N E U}.
Arguments universe {N E U}.
Arguments dir {N E U}.
Arguments gen_c {N E U}.
Arguments kill_c {N E U}.
Arguments boundary_c {N E U}.

Definition gen {N E U} (P : t N E U) e := Cost.value (gen_c P e).
Definition kill {N E U} (P : t N E U) e := Cost.value (kill_c P e).
Definition boundary {N E U} (P : t N E U) n := Cost.value (boundary_c P n).

(** Pure gen, kill and boundary readers use the primitive one-tick convention. *)
Definition of_pure {N E U} cfg enc facts dir gen kill boundary : t N E U :=
  Make cfg enc facts dir (fun e => Cost.step ;; Cost.ret (gen e))
    (fun e => Cost.step ;; Cost.ret (kill e))
    (fun n => Cost.step ;; Cost.ret (boundary n)).

(** Boundary preparation uses the same raw seed inventory as the dense generator. *)
Definition seeds {N E U} (P : t N E U) :=
  match dir P with
  | Forward => Graph.entries (Cfg.graph (cfg P))
  | Backward => Graph.nodes (Cfg.graph (cfg P))
  end.

(** Prepared maps contain valid fact sets and retain all boundary nodes. *)
Record prepared {N E U} (P : t N E U) := Prep {
  gen_sets : Map.t E (set_t (fact_enc P));
  kill_sets : Map.t E (set_t (fact_enc P));
  boundaries : Map.t N (option (set_t (fact_enc P)))
}.
Arguments Prep {N E U P}.
Arguments gen_sets {N E U P}.
Arguments kill_sets {N E U P}.
Arguments boundaries {N E U P}.

Definition prepare_sets_c {N E U} (P : t N E U) es
    (reader : E -> Cost.t (list U)) :=
  let* pairs := fw_flat_map_c (fun e =>
    Cost.step ;;
    let* xs := reader e in
    map_c (fun x => Cost.ret (e, x)) xs) es in
  let* idx := Index.group_by_c (Cfg.edge_enc (cfg P))
    (fun p => Cost.ret (fst p)) pairs in
  Map.map_c (fun bucket =>
    let* xs := map_c (fun p => Cost.ret (snd p)) bucket in
    set_of_list_c (fact_enc P) xs) idx.

(** Boundary conversion visits each generated seed occurrence and retains its reader charge. *)
Definition boundary_rows_c {N E U} (P : t N E U) :=
  map_c (fun n =>
    Cost.step ;;
    let* b := boundary_c P n in
    match b with
    | None => Cost.ret (n, None)
    | Some xs => Cost.map (fun s => (n, Some s)) (set_of_list_c (fact_enc P) xs)
    end) (seeds P).

(** Preparation groups occurrences once and constructs canonical valid sets outside transfers. *)
Definition prepare_c {N E U} (P : t N E U) : Cost.t (prepared P) :=
  let* es := fw_edges_c (cfg P) in
  let* gs := prepare_sets_c P es (gen_c P) in
  let* ks := prepare_sets_c P es (kill_c P) in
  let* bs := boundary_rows_c P in
  let* bm := Map.of_list_c (Cfg.node_enc (cfg P)) bs in
  Cost.ret (Prep gs ks bm).

Definition prepare {N E U} (P : t N E U) := Cost.value (prepare_c P).

(** Group preparation preserves map well-formedness independently of encoding laws. *)
Theorem prepare_sets_wf {N E U} (P : t N E U) es reader :
  Map.wf (Cfg.edge_enc (cfg P)) (Cost.value (prepare_sets_c P es reader)).
Proof.
  unfold prepare_sets_c; rewrite !Cost.value_bind, Map.map_c_value, Index.group_by_c_value.
  apply Map.wf_map, Index.wf_group_by.
Qed.

(** The occurrence model retains repeated edge/fact occurrences in input order. *)
Definition occurrences {N E U} (P : t N E U) es (reader : E -> Cost.t (list U)) :=
  flat_map (fun e => map (fun x => (e, x)) (Cost.value (reader e))) es.

(** Prepared edge sets are the stable grouped source occurrences converted to valid sets. *)
Theorem prepare_sets_equation {N E U} (P : t N E U) es reader e :
  Map.get (Cfg.edge_enc (cfg P)) e (Cost.value (prepare_sets_c P es reader)) =
    Map.get (Cfg.edge_enc (cfg P)) e
      (Map.map (fun bucket => set_of_list (fact_enc P) (map snd bucket))
        (Index.group_by (Cfg.edge_enc (cfg P)) fst (occurrences P es reader))).
Proof.
  unfold prepare_sets_c; rewrite !Cost.value_bind, Map.map_c_value, Index.group_by_c_value.
  rewrite fw_flat_map_value.
  assert (Hxs : flat_map (fun x => Cost.value
    (Cost.step ;; let* xs := reader x in map_c (fun y => Cost.ret (x, y)) xs)) es =
    occurrences P es reader).
  { unfold occurrences; induction es as [|a es IH]; cbn [flat_map];
      autorewrite with galois_cost; rewrite ?IH; reflexivity. }
  rewrite Hxs.
  rewrite !Map.get_map.
  set (idx := Index.group_by (Cfg.edge_enc (cfg P)) (@fst E U) (occurrences P es reader)).
  change (option_map (fun bucket => Cost.value
    (let* xs := map_c (fun p => Cost.ret (snd p)) bucket in set_of_list_c (fact_enc P) xs))
    (Map.get (Cfg.edge_enc (cfg P)) e idx) =
    option_map (fun bucket => set_of_list (fact_enc P) (map snd bucket))
      (Map.get (Cfg.edge_enc (cfg P)) e idx)).
  destruct (Map.get (Cfg.edge_enc (cfg P)) e idx) as [xs|].
  - cbn [option_map]; f_equal; autorewrite with galois_cost; reflexivity.
  - reflexivity.
Qed.

Definition gen_set_c {N E U} {P : t N E U} (p : prepared P) e :=
  Map.find_or_c (Cfg.edge_enc (cfg P)) (set_empty (fact_enc P)) e (gen_sets p).

Definition kill_set_c {N E U} {P : t N E U} (p : prepared P) e :=
  Map.find_or_c (Cfg.edge_enc (cfg P)) (set_empty (fact_enc P)) e (kill_sets p).

Definition gen_set {N E U} {P : t N E U} (p : prepared P) e :=
  Cost.value (gen_set_c p e).

Definition kill_set {N E U} {P : t N E U} (p : prepared P) e :=
  Cost.value (kill_set_c p e).

Definition boundary_set_c {N E U} {P : t N E U} (p : prepared P) n :=
  Map.find_or_c (Cfg.node_enc (cfg P)) None n (boundaries p).

Definition boundary_set {N E U} {P : t N E U} (p : prepared P) n :=
  Cost.value (boundary_set_c p n).

(** Boundary rows preserve the optional source lists at every seed occurrence. *)
Theorem boundary_rows_value {N E U} (P : t N E U) :
  Cost.value (boundary_rows_c P) =
    map (fun n => (n, option_map (set_of_list (fact_enc P)) (boundary P n))) (seeds P).
Proof.
  unfold boundary_rows_c; rewrite value_map_c; apply map_ext; intro n.
  autorewrite with galois_cost; fold (boundary P n).
  destruct (boundary P n); reflexivity.
Qed.

(** The prepared boundary cache is the public map constructor on converted seed occurrences. *)
Theorem prepare_boundaries_equation {N E U} (P : t N E U) :
  boundaries (prepare P) = Map.of_list (Cfg.node_enc (cfg P))
    (map (fun n => (n, option_map (set_of_list (fact_enc P)) (boundary P n))) (seeds P)).
Proof.
  unfold prepare, prepare_c; rewrite !Cost.value_bind, boundary_rows_value; reflexivity.
Qed.

Local Lemma get_mapped_inventory {K A} (E : encoding K) (HE : encoding_laws E)
    (f : K -> A) xs n :
  In n xs -> Map.get E n (Map.of_list E (map (fun k => (k, f k)) xs)) = Some (f n).
Proof.
  intro Hn; rewrite Map.of_list_get.
  assert (Hfold : forall ys old, old = Some (f n) \/ In n ys ->
    fold_left (fun old kv => if eqb E n (fst kv) then Some (snd kv) else old)
      (map (fun k => (k, f k)) ys) old = Some (f n)).
  { induction ys as [|k ys IH]; intros old Hhit; cbn [map fold_left fst snd].
    - destruct Hhit as [->|[]]; reflexivity.
    - destruct (eqb E n k) eqn:Hkey.
      + apply (eqb_true_iff E HE) in Hkey; subst k.
        apply IH; left; reflexivity.
      + apply IH; destruct Hhit as [Hhit|[Hsame|Hhit]].
        * left; exact Hhit.
        * subst k; rewrite eqb_refl in Hkey; discriminate.
        * right; exact Hhit. }
  apply Hfold; right; exact Hn.
Qed.

(** Every listed raw seed preserves its original optional boundary without graph-closure laws. *)
Theorem prepare_boundary_source {N E U} (P : t N E U) n :
  encoding_laws (Cfg.node_enc (cfg P)) -> In n (seeds P) ->
  boundary_set (prepare P) n =
    option_map (set_of_list (fact_enc P)) (boundary P n).
Proof.
  intros HN Hn; unfold boundary_set, boundary_set_c.
  change (Map.find_or (Cfg.node_enc (cfg P)) None n (boundaries (prepare P)) =
    option_map (set_of_list (fact_enc P)) (boundary P n)).
  rewrite Map.find_or_equation, prepare_boundaries_equation.
  rewrite (get_mapped_inventory _ HN _ _ n Hn); reflexivity.
Qed.

(** Raw prepared lookup agrees with the stable source bucket, including empty buckets. *)
Theorem prepare_sets_lookup {N E U} (P : t N E U) es reader e :
  set_raw (Map.find_or (Cfg.edge_enc (cfg P)) (set_empty (fact_enc P)) e
    (Cost.value (prepare_sets_c P es reader))) =
  FinSet.of_list (fact_enc P)
    (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
      (occurrences P es reader))).
Proof.
  rewrite Map.find_or_equation, prepare_sets_equation, Map.get_map.
  pose proof (Index.find_group_by (Cfg.edge_enc (cfg P)) fst e
    (occurrences P es reader)) as Hbucket.
  rewrite Index.find_equation in Hbucket.
  destruct (Map.get (Cfg.edge_enc (cfg P)) e
    (Index.group_by (Cfg.edge_enc (cfg P)) fst (occurrences P es reader))) as [xs|].
  - cbn [option_map]; rewrite set_of_list_raw, Hbucket; reflexivity.
  - rewrite <- Hbucket; cbn [map].
    rewrite FinSet.of_list_equation; reflexivity.
Qed.

(** Prepared gen lookup retains exactly the grouped source gen occurrences. *)
Theorem prepare_gen_raw {N E U} (P : t N E U) e :
  set_raw (gen_set (prepare P) e) =
  FinSet.of_list (fact_enc P)
    (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
      (occurrences P (Cfg.edges (cfg P)) (gen_c P)))).
Proof.
  unfold gen_set, gen_set_c, prepare, prepare_c; rewrite !Cost.value_bind.
  change (set_raw (Map.find_or (Cfg.edge_enc (cfg P)) (set_empty (fact_enc P)) e
    (Cost.value (prepare_sets_c P (Cost.value (fw_edges_c (cfg P))) (gen_c P)))) =
    FinSet.of_list (fact_enc P)
      (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
        (occurrences P (Cfg.edges (cfg P)) (gen_c P))))).
  rewrite fw_edges_value; apply prepare_sets_lookup.
Qed.

(** Prepared kill lookup retains exactly the grouped source kill occurrences. *)
Theorem prepare_kill_raw {N E U} (P : t N E U) e :
  set_raw (kill_set (prepare P) e) =
  FinSet.of_list (fact_enc P)
    (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
      (occurrences P (Cfg.edges (cfg P)) (kill_c P)))).
Proof.
  unfold kill_set, kill_set_c, prepare, prepare_c; rewrite !Cost.value_bind.
  change (set_raw (Map.find_or (Cfg.edge_enc (cfg P)) (set_empty (fact_enc P)) e
    (Cost.value (prepare_sets_c P (Cost.value (fw_edges_c (cfg P))) (kill_c P)))) =
    FinSet.of_list (fact_enc P)
      (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
        (occurrences P (Cfg.edges (cfg P)) (kill_c P))))).
  rewrite fw_edges_value; apply prepare_sets_lookup.
Qed.

Local Lemma occurrence_bucket {N E U} (P : t N E U) es reader e x :
  encoding_laws (Cfg.edge_enc (cfg P)) -> In e es ->
  (In x (map snd (filter (fun ex => eqb (Cfg.edge_enc (cfg P)) (fst ex) e)
    (occurrences P es reader))) <-> In x (Cost.value (reader e))).
Proof.
  intros HE He; unfold occurrences; rewrite in_map_iff; split.
  - intros [[a y] [Hxy Hin]]; cbn in Hxy; subst y.
    apply filter_In in Hin; destruct Hin as [Hin Hkey].
    apply (eqb_true_iff _ HE) in Hkey; cbn in Hkey; subst a.
    apply in_flat_map in Hin; destruct Hin as [a [Ha Hin]].
    apply in_map_iff in Hin; destruct Hin as [y [Hpair Hy]].
    inversion Hpair; subst; exact Hy.
  - intro Hx; exists (e, x); split; [reflexivity|].
    apply filter_In; split; [|apply eqb_refl].
    apply in_flat_map; exists e; split; [exact He|apply in_map; exact Hx].
Qed.

(** On listed edges, preparation preserves gen membership without a universe premise. *)
Theorem prepare_gen_mem {N E U} (P : t N E U) e x :
  encoding_laws (Cfg.edge_enc (cfg P)) -> In e (Cfg.edges (cfg P)) ->
  FinSet.mem (fact_enc P) x (set_raw (gen_set (prepare P) e)) =
    FinSet.mem (fact_enc P) x (FinSet.of_list (fact_enc P) (gen P e)).
Proof.
  intros HE He; rewrite prepare_gen_raw, !FinSet.mem_of_list.
  apply eq_true_iff_eq; rewrite !existsb_exists; split;
    intros [y [Hy Hkey]]; exists y; split; [|exact Hkey| |exact Hkey].
  - apply (proj1 (occurrence_bucket P _ _ _ _ HE He)); exact Hy.
  - apply (proj2 (occurrence_bucket P _ _ _ _ HE He)); exact Hy.
Qed.

(** On listed edges, preparation preserves kill membership without a universe premise. *)
Theorem prepare_kill_mem {N E U} (P : t N E U) e x :
  encoding_laws (Cfg.edge_enc (cfg P)) -> In e (Cfg.edges (cfg P)) ->
  FinSet.mem (fact_enc P) x (set_raw (kill_set (prepare P) e)) =
    FinSet.mem (fact_enc P) x (FinSet.of_list (fact_enc P) (kill P e)).
Proof.
  intros HE He; rewrite prepare_kill_raw, !FinSet.mem_of_list.
  apply eq_true_iff_eq; rewrite !existsb_exists; split;
    intros [y [Hy Hkey]]; exists y; split; [|exact Hkey| |exact Hkey].
  - apply (proj1 (occurrence_bucket P _ _ _ _ HE He)); exact Hy.
  - apply (proj2 (occurrence_bucket P _ _ _ _ HE He)); exact Hy.
Qed.

(** Valid difference uses the owning container's preservation proof. *)
Definition difference_c {U} (E : encoding U) (a b : set_t E) : Cost.t (set_t E) :=
  Cost.refine (FinSet.diff_c (set_raw a) (set_raw b))
    (FinSet.wf_diff E _ _ (proj2_sig a) (proj2_sig b)).

(** A may transfer reads prepared maps and performs difference followed by union. *)
Definition may_transfer_c {N E U} {P : t N E U} (p : prepared P) e a :=
  let* k := kill_set_c p e in
  let* g := gen_set_c p e in
  let* rest := difference_c (fact_enc P) a k in
  set_union_c (fact_enc P) rest g.

Definition may_transfer {N E U} {P : t N E U} (p : prepared P) e a :=
  Cost.value (may_transfer_c p e a).

(** The prepared may transfer is the literal difference/union gen-kill expression. *)
Theorem may_transfer_raw {N E U} {P : t N E U} (p : prepared P) e a :
  set_raw (may_transfer p e a) =
    FinSet.union (FinSet.diff (set_raw a) (set_raw (kill_set p e)))
      (set_raw (gen_set p e)).
Proof.
  unfold may_transfer, may_transfer_c, difference_c.
  autorewrite with galois_cost.
  rewrite set_union_raw.
  reflexivity.
Qed.

(** Must transfers preserve fresh unreachable All and transform reached finite facts. *)
Definition must_transfer_c {N E U} {P : t N E U} (p : prepared P) e a :=
  match a with
  | All => Cost.ret All
  | Only a => Cost.map Only (may_transfer_c p e a)
  end.

Definition must_transfer {N E U} {P : t N E U} (p : prepared P) e a :=
  Cost.value (must_transfer_c p e a).

Definition may_dense {N E U} (P : t N E U) (p : prepared P) :=
  Dense.Make (cfg P) (dir P) (may (fact_enc P))
    (boundary_set_c p) (may_transfer_c p).

Definition must_dense {N E U} (P : t N E U) (p : prepared P) :=
  Dense.Make (cfg P) (dir P) (must (fact_enc P))
    (fun n => Cost.map (option_map Only) (boundary_set_c p n)) (must_transfer_c p).

(** Charged may construction binds the actual prepared indexes before building the dense system. *)
Definition may_analysis_c {N E U} (P : t N E U) :=
  let* p := prepare_c P in
  Dense.analysis_c (may_dense P p) (Policy.by_code (Cfg.node_enc (cfg P))).

(** May analysis captures its prepared indexes once. *)
Definition may_analysis {N E U} (P : t N E U) :=
  Cost.value (may_analysis_c P).

(** Charged must construction uses the same preparation and preserves the All/Only lattice. *)
Definition must_analysis_c {N E U} (P : t N E U) :=
  let* p := prepare_c P in
  Dense.analysis_c (must_dense P p) (Policy.by_code (Cfg.node_enc (cfg P))).

(** Must analysis uses All as fresh bottom and intersection as the library join. *)
Definition must_analysis {N E U} (P : t N E U) :=
  Cost.value (must_analysis_c P).

(** The charged may constructor returns exactly the original prepared analysis record. *)
Theorem may_analysis_equation {N E U} (P : t N E U) :
  may_analysis P =
    Dense.analysis (may_dense P (prepare P)) (Policy.by_code (Cfg.node_enc (cfg P))).
Proof.
  unfold may_analysis, may_analysis_c; rewrite Cost.value_bind; reflexivity.
Qed.

(** The charged must constructor returns exactly the original prepared analysis record. *)
Theorem must_analysis_equation {N E U} (P : t N E U) :
  must_analysis P =
    Dense.analysis (must_dense P (prepare P)) (Policy.by_code (Cfg.node_enc (cfg P))).
Proof.
  unfold must_analysis, must_analysis_c; rewrite Cost.value_bind; reflexivity.
Qed.

(** May construction retains preparation and the actual prepared dense-system charge once. *)
Theorem may_analysis_cost {N E U} (P : t N E U) :
  Cost.ticks (may_analysis_c P) =
    (Cost.ticks (prepare_c P) +
      Cost.ticks (Dense.system_c (may_dense P (prepare P))))%N.
Proof.
  unfold may_analysis_c; rewrite Cost.ticks_bind, Dense.analysis_cost; reflexivity.
Qed.

(** Must construction retains preparation and the actual prepared dense-system charge once. *)
Theorem must_analysis_cost {N E U} (P : t N E U) :
  Cost.ticks (must_analysis_c P) =
    (Cost.ticks (prepare_c P) +
      Cost.ticks (Dense.system_c (must_dense P (prepare P))))%N.
Proof.
  unfold must_analysis_c; rewrite Cost.ticks_bind, Dense.analysis_cost; reflexivity.
Qed.

(** May analysis laws reuse the reviewed collection lattice and dense summary. *)
Theorem may_analysis_laws {N E U} (P : t N E U) :
  encoding_laws (Cfg.node_enc (cfg P)) -> encoding_laws (Cfg.edge_enc (cfg P)) ->
  encoding_laws (fact_enc P) -> Analysis.laws (may_analysis P).
Proof.
  intros HN HE HU.
  exact (Dense.analysis_laws (may_dense P (prepare P)) _ HN HE (may_laws _ HU)).
Qed.

(** Must analysis laws reuse the reviewed All/Only lattice and dense summary. *)
Theorem must_analysis_laws {N E U} (P : t N E U) :
  encoding_laws (Cfg.node_enc (cfg P)) -> encoding_laws (Cfg.edge_enc (cfg P)) ->
  encoding_laws (fact_enc P) -> Analysis.laws (must_analysis P).
Proof.
  intros HN HE HU.
  exact (Dense.analysis_laws (must_dense P (prepare P)) _ HN HE (must_laws _ HU)).
Qed.

(** Support is a separate obligation on source occurrences and boundaries. *)
Definition supported {N E U} (P : t N E U) : Prop :=
  (forall e, In e (Cfg.edges (cfg P)) ->
    incl (gen P e) (universe P) /\ incl (kill P e) (universe P)) /\
  (forall n xs, In n (seeds P) ->
    boundary P n = Some xs -> incl xs (universe P)).

(** May post-solutions satisfy precisely the prepared gen/kill inequalities. *)
Theorem may_post_iff {N E U} (P : t N E U) s :
  encoding_laws (fact_enc P) ->
  (post_solution (Analysis.lat (may_analysis P)) (Analysis.system (may_analysis P)) s <->
    (forall n a, In n (Dense.seeds (may_dense P (prepare P))) ->
      boundary_set (prepare P) n = Some a ->
      leb (may (fact_enc P)) a (s n) = true) /\
    (forall e, In e (Cfg.edges (cfg P)) ->
      leb (may (fact_enc P)) (may_transfer (prepare P) e
        (s (Dense.from (may_dense P (prepare P)) e)))
        (s (Dense.into (may_dense P (prepare P)) e)) = true)).
Proof.
  intro HE.
  exact (Dense.post_solution_iff (may_dense P (prepare P)) s (may_laws _ HE)).
Qed.

(** Must post-solutions use the same bounds under the reviewed reverse-inclusion order. *)
Theorem must_post_iff {N E U} (P : t N E U) s :
  encoding_laws (fact_enc P) ->
  (post_solution (Analysis.lat (must_analysis P)) (Analysis.system (must_analysis P)) s <->
    (forall n a, In n (Dense.seeds (must_dense P (prepare P))) ->
      option_map Only (boundary_set (prepare P) n) = Some a ->
      leb (must (fact_enc P)) a (s n) = true) /\
    (forall e, In e (Cfg.edges (cfg P)) ->
      leb (must (fact_enc P)) (must_transfer (prepare P) e
        (s (Dense.from (must_dense P (prepare P)) e)))
        (s (Dense.into (must_dense P (prepare P)) e)) = true)).
Proof.
  intro HE.
  exact (Dense.post_solution_iff (must_dense P (prepare P)) s (must_laws _ HE)).
Qed.

(** May post-solutions retain the original listed boundary facts independently of support. *)
Theorem may_source_post_iff {N E U} (P : t N E U) s :
  encoding_laws (Cfg.node_enc (cfg P)) -> encoding_laws (fact_enc P) ->
  (post_solution (Analysis.lat (may_analysis P)) (Analysis.system (may_analysis P)) s <->
    (forall n xs, In n (seeds P) -> boundary P n = Some xs ->
      leb (may (fact_enc P)) (set_of_list (fact_enc P) xs) (s n) = true) /\
    (forall e, In e (Cfg.edges (cfg P)) ->
      leb (may (fact_enc P)) (may_transfer (prepare P) e
        (s (Dense.from (may_dense P (prepare P)) e)))
        (s (Dense.into (may_dense P (prepare P)) e)) = true)).
Proof.
  intros HN HU; rewrite may_post_iff by exact HU; split.
  - intros [Hseed Hflow]; split; [|exact Hflow].
    intros n xs Hn Hb; apply Hseed; [exact Hn|].
    rewrite prepare_boundary_source by assumption; rewrite Hb; reflexivity.
  - intros [Hseed Hflow]; split; [|exact Hflow].
    intros n a Hn Ha; rewrite prepare_boundary_source in Ha by exact HN || exact Hn.
    destruct (boundary P n) as [xs|] eqn:Hb; [|discriminate].
    inversion Ha; subst a; apply Hseed; assumption.
Qed.

(** Must post-solutions retain the original listed Only boundary facts independently of support. *)
Theorem must_source_post_iff {N E U} (P : t N E U) s :
  encoding_laws (Cfg.node_enc (cfg P)) -> encoding_laws (fact_enc P) ->
  (post_solution (Analysis.lat (must_analysis P)) (Analysis.system (must_analysis P)) s <->
    (forall n xs, In n (seeds P) -> boundary P n = Some xs ->
      leb (must (fact_enc P)) (Only (set_of_list (fact_enc P) xs)) (s n) = true) /\
    (forall e, In e (Cfg.edges (cfg P)) ->
      leb (must (fact_enc P)) (must_transfer (prepare P) e
        (s (Dense.from (must_dense P (prepare P)) e)))
        (s (Dense.into (must_dense P (prepare P)) e)) = true)).
Proof.
  intros HN HU; rewrite must_post_iff by exact HU; split.
  - intros [Hseed Hflow]; split; [|exact Hflow].
    intros n xs Hn Hb; apply Hseed; [exact Hn|].
    rewrite prepare_boundary_source by assumption; rewrite Hb; reflexivity.
  - intros [Hseed Hflow]; split; [|exact Hflow].
    intros n a Hn Ha; rewrite prepare_boundary_source in Ha by exact HN || exact Hn.
    destruct (boundary P n) as [xs|] eqn:Hb; [|discriminate].
    inversion Ha; subst a; apply Hseed; assumption.
Qed.

Arguments prepare_c {N E U} P : simpl never.
Arguments prepare {N E U} P : simpl never.
Arguments may_analysis_c {N E U} P : simpl never.
Arguments must_analysis_c {N E U} P : simpl never.
Arguments may_analysis {N E U} P : simpl never.
Arguments must_analysis {N E U} P : simpl never.

End Bitvector.
