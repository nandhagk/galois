(** * Numeric discovery on finite metadata domains

    Discovery visits a bipartite graph whose incidence retains repeated metadata and row entries.
    For example, repeated side targets pay for probes while each vertex expands once.
    Builds on: FixpointLocalCredit, FixpointLocalDiscover and public index laws. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseMapCost BaseSet
  BaseTrieCost.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointAnalysis
  FixpointIndexCost FixpointLocalDiscover FixpointLocalCredit FixpointLocal FixpointLocalProof.
Import List.ListNotations Cost.Notations.
Local Open Scope N_scope.

Module LocalCost.

(** A row's finite metadata includes its primary target, side declarations and reads. *)
Definition metadata {X C A} (a : Analysis.t X C A) c :=
  System.target (Analysis.system a) c ::
    side_targets (Analysis.static a) c ++ deps (Analysis.static a) c.

(** Raw support retains roots and source metadata occurrences before key-domain deduplication. *)
Definition raw_support {X C A} (a : Analysis.t X C A) roots :=
  map (@inl X C) roots ++ map (@inr X C) (System.constraints (Analysis.system a)) ++
  flat_map (fun c => map (@inl X C) (metadata a c))
    (System.constraints (Analysis.system a)).

(** The proof-only support is a finite unique key domain, while adjacency retains multiplicity. *)
Definition support {X C A} (a : Analysis.t X C A) roots :=
  distinct (sum_encoding (Analysis.key_enc a) (Analysis.row_enc a)) (raw_support a roots).

(** Canonical proof support contains each vertex key once independently of adjacency multiplicity. *)
Theorem support_nodup {X C A} (a : Analysis.t X C A) roots : NoDup (support a roots).
Proof.
  apply distinct_nodup.
Qed.

Local Lemma support_member {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) roots v :
  In v (support a roots) <-> In v (raw_support a roots).
Proof.
  unfold support; apply distinct_spec, sum_encoding_laws;
    [exact (Analysis.key_laws HL)|exact (Analysis.row_laws HL)].
Qed.

Local Lemma projection_traversals {X C} (vs : list (X + C)) :
  Cost.ticks (Local.lefts_c vs) = N.of_nat (length vs) /\
  Cost.ticks (Local.rights_c vs) = N.of_nat (length vs) /\
  (length (Cost.value (Local.lefts_c vs)) <= length vs)%nat /\
  (length (Cost.value (Local.rights_c vs)) <= length vs)%nat.
Proof.
  induction vs as [|[x|c] vs [Hl [Hr [Hxl Hcl]]]];
    cbn [Local.lefts_c Local.rights_c length]; autorewrite with galois_cost.
  - cbn [length]; repeat split; lia.
  - rewrite Hl, Hr, Nat2N.inj_succ; cbn [length]; repeat split; lia.
  - rewrite Hl, Hr, Nat2N.inj_succ; cbn [length]; repeat split; lia.
Qed.

Local Lemma row_support {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) roots c :
  In (inr c) (support a roots) <-> In c (System.constraints (Analysis.system a)).
Proof.
  rewrite (support_member a HL); unfold raw_support; rewrite !in_app_iff; split.
  - intros [Hroot|[Hrow|Hmeta]].
    + apply in_map_iff in Hroot as [x [Heq _]]; discriminate.
    + apply in_map_iff in Hrow as [d [Heq Hd]]; injection Heq as <-; exact Hd.
    + apply in_flat_map in Hmeta as [d [_ Hmeta]].
      apply in_map_iff in Hmeta as [x [Heq _]]; discriminate.
  - intro Hc; right; left; apply in_map, Hc.
Qed.

(** Every original root belongs to the finite mathematical discovery support. *)
Theorem roots_support {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) roots :
  incl (map (@inl X C) roots) (support a roots).
Proof.
  intros v Hv; apply (support_member a HL); unfold raw_support; apply in_or_app; now left.
Qed.

(** Contributor laws and finite metadata establish support closure independently of runs. *)
Theorem support_closed {X C A} (a : Analysis.t X C A) (HL : Analysis.laws a) roots :
  forall v, In v (support a roots) ->
    incl (LocalDiscover.adjacent a
      (index_system (Analysis.key_enc a) (Analysis.system a) (Analysis.static a)) v)
      (support a roots).
Proof.
  intros [x|c] Hv v Hedge; rewrite LocalDiscover.adjacent_equation in Hedge.
  - apply in_map_iff in Hedge as [c [<- Hc]]; apply (row_support a HL).
    exact (proj1 (proj1 (contributors_agree
      (index_system_laws _ (Analysis.key_laws HL) _ _) x c) Hc)).
  - apply (row_support a HL) in Hv; apply in_map_iff in Hedge as [x [<- Hx]].
    apply (support_member a HL); unfold raw_support.
    apply in_or_app; right; apply in_or_app; right.
    apply in_flat_map; exists c; split; [exact Hv|apply in_map, Hx].
Qed.

Module Budget.

(** Budgets describe original encoders, tagged encoders and primitive metadata callbacks. *)
Record t := Make {
  vertex_encoder : N;
  vertex_digits : N;
  key_encoder : N;
  key_digits : N;
  row_encoder : N;
  row_digits : N;
  target : N;
  sides : N;
  reads : N
}.

Definition w b := 6 + vertex_encoder b + vertex_digits b +
  key_encoder b + key_digits b + target b + sides b + reads b.

(** Projection retains trie enumeration and the construction of both destination sets. *)
Definition projection b count :=
  TrieCost.trie_k * (1 + N.of_nat count * vertex_digits b) +
  N.of_nat count * (9 + key_encoder b + key_digits b + row_encoder b + row_digits b).

End Budget.
Import Budget.

(** Domains for primitive duties are the actual finite roots and declared metadata support. *)
Record model {X C A} (a : Analysis.t X C A) roots (b : Budget.t) : Prop := {
  vertices : forall v, In v (support a roots) ->
    Cost.ticks (encode_c (sum_encoding (Analysis.key_enc a) (Analysis.row_enc a)) v) <=
      Budget.vertex_encoder b /\
    key_bits (sum_encoding (Analysis.key_enc a) (Analysis.row_enc a)) v <=
      Budget.vertex_digits b;
  unknown_keys : forall x, In (inl x) (support a roots) ->
    Cost.ticks (encode_c (Analysis.key_enc a) x) <= Budget.key_encoder b /\
    key_bits (Analysis.key_enc a) x <= Budget.key_digits b;
  row_keys : forall c, In c (System.constraints (Analysis.system a)) ->
    Cost.ticks (encode_c (Analysis.row_enc a) c) <= Budget.row_encoder b /\
    key_bits (Analysis.row_enc a) c <= Budget.row_digits b;
  row_metadata : forall c, In c (System.constraints (Analysis.system a)) ->
    Cost.ticks (System.target_c (Analysis.system a) c) <= Budget.target b /\
    Cost.ticks (System.side_targets_c (Analysis.static a) c) <= Budget.sides b /\
    Cost.ticks (System.deps_c (Analysis.static a) c) <= Budget.reads b
}.

Arguments vertices {X C A a roots b}.
Arguments unknown_keys {X C A a roots b}.
Arguments row_keys {X C A a roots b}.
Arguments row_metadata {X C A a roots b}.

Section Numeric.
Context {X C A : Type} (a : Analysis.t X C A) (HL : Analysis.laws a)
  roots (b : Budget.t) (HB : model a roots b).
Let EX := Analysis.key_enc a.
Let EC := Analysis.row_enc a.
Let EV := sum_encoding EX EC.
Let HE := sum_encoding_laws EX EC (Analysis.key_laws HL) (Analysis.row_laws HL).
Let ix := index_system EX (Analysis.system a) (Analysis.static a).
Let next := LocalDiscover.adjacent_c a ix.
Let U := support a roots.
Let entries := map (@inl X C) roots.

(** Tagged membership and marking budgets follow their complete encoding and trie-width charges. *)
Theorem vertex_cost v :
  In v U -> forall marked, Cost.ticks (FinSet.mem_c EV v marked) <= Budget.w b /\
    Cost.ticks (FinSet.add_c EV v marked) <= Budget.w b.
Proof.
  intros Hv marked; destruct (vertices HB v Hv) as [He Hw].
  change (Cost.ticks (encode_c EV v) <= Budget.vertex_encoder b) in He.
  change (key_bits EV v <= Budget.vertex_digits b) in Hw.
  rewrite FinSet.mem_cost, FinSet.add_cost; fold (key_bits EV v).
  unfold Budget.w; split; lia.
Qed.

(** The actual adjacency callback's numeric cost follows primitive index and metadata charges. *)
Theorem adjacent_cost v :
  In v U -> Cost.ticks (next v) <=
    Budget.w b * (1 + N.of_nat (length (Cost.value (next v)))).
Proof.
  intro Hv; unfold next at 1; rewrite LocalDiscover.adjacent_cost_equation.
  unfold next; fold (LocalDiscover.adjacent a ix v).
  rewrite LocalDiscover.adjacent_equation.
  destruct v as [x|c]; rewrite length_map.
  - destruct (unknown_keys HB x Hv) as [He Hw].
    change (Cost.ticks (encode_c EX x) <= Budget.key_encoder b) in He.
    change (key_bits EX x <= Budget.key_digits b) in Hw.
    rewrite contributors_cost, Map.get_cost; fold EX; fold (key_bits EX x).
    unfold Budget.w; nia.
  - apply (row_support a HL) in Hv.
    destruct (row_metadata HB c Hv) as [Ht [Hs Hd]].
    cbn [length]; rewrite !length_app, Nat2N.inj_succ, Nat2N.inj_add.
    unfold Budget.w; nia.
Qed.

(** Visited work counts one vertex cell and all of that vertex's retained adjacency occurrences. *)
Definition visited_incidence vertices :=
  LocalCredit.visited_work EV next U vertices.

(** Indexed discovery cost depends on visited incidence and retains binary fuel descent. *)
Theorem local_discover_cost fuel vertices :
  LocalDiscover.run a ix roots fuel = inr vertices ->
  Cost.ticks (LocalDiscover.run_c a ix roots fuel) <=
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * visited_incidence vertices + N.pos (Pos.size fuel).
Proof.
  intro Hrun; unfold LocalDiscover.run, LocalDiscover.run_c in Hrun.
  rewrite Cost.value_bind, value_map_c in Hrun.
  pose proof (LocalCredit.local_discover_cost EV next U entries (roots_support a HL roots)
    (support_closed a HL roots) (Budget.w b) vertex_cost adjacent_cost fuel vertices Hrun)
    as Hcost.
  assert (Hmap : Cost.ticks (map_c (fun x => Cost.ret (@inl X C x)) roots) <=
    N.of_nat (length roots)).
  { pose proof (ticks_map_c_le (fun x => Cost.ret (@inl X C x)) 0 roots
      (fun _ => N.le_refl 0)); nia. }
  unfold LocalDiscover.run_c; rewrite Cost.ticks_bind, value_map_c.
  change (Cost.ticks (map_c (fun x => Cost.ret (@inl X C x)) roots) +
    Cost.ticks (iterate (LocalDiscover.step_c EV next) fuel
      (LocalDiscover.State FinSet.empty entries)) <=
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * visited_incidence vertices + N.pos (Pos.size fuel)).
  replace (length entries) with (length roots) in Hcost by
    (unfold entries; rewrite length_map; reflexivity).
  unfold visited_incidence; nia.
Qed.

(** Finite support and declared index closure give an actual discovery adequacy threshold. *)
Theorem local_discover_adequate fuel :
  N.of_nat (length roots) + LocalCredit.sum (LocalCredit.weight next) U < N.pos fuel ->
  exists vertices, LocalDiscover.run a ix roots fuel = inr vertices.
Proof.
  intro Hfuel.
  destruct (LocalCredit.adequate EV next U entries (roots_support a HL roots)
    (support_closed a HL roots) fuel) as [vertices Hloop].
  - unfold entries; rewrite length_map; exact Hfuel.
  - exists vertices; unfold LocalDiscover.run, LocalDiscover.run_c.
    rewrite Cost.value_bind, value_map_c; exact Hloop.
Qed.

(** All discovery outcomes have a numeric finite-domain bound without an assumed run result. *)
Theorem local_discover_full_cost fuel :
  Cost.ticks (LocalDiscover.run_c a ix roots fuel) <=
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * LocalCredit.sum (LocalCredit.weight next) U +
    N.pos (Pos.size fuel).
Proof.
  pose proof (LocalCredit.discover_full_cost EV next U entries (roots_support a HL roots)
    (support_closed a HL roots) (Budget.w b) vertex_cost adjacent_cost fuel) as Hcost.
  assert (Hmap : Cost.ticks (map_c (fun x => Cost.ret (@inl X C x)) roots) <=
    N.of_nat (length roots)).
  { pose proof (ticks_map_c_le (fun x => Cost.ret (@inl X C x)) 0 roots
      (fun _ => N.le_refl 0)); nia. }
  unfold LocalDiscover.run_c; rewrite Cost.ticks_bind, value_map_c.
  change (Cost.ticks (map_c (fun x => Cost.ret (@inl X C x)) roots) +
    Cost.ticks (iterate (LocalDiscover.step_c EV next) fuel
      (LocalDiscover.State FinSet.empty entries)) <=
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * LocalCredit.sum (LocalCredit.weight next) U +
    N.pos (Pos.size fuel)).
  replace (length entries) with (length roots) in Hcost by
    (unfold entries; rewrite length_map; reflexivity).
  nia.
Qed.

(** Canonical projection is numerically bounded by finite support and primitive key duties. *)
Theorem project_cost marked :
  FinSet.wf EV marked ->
  (forall v, FinSet.mem EV v marked = true -> In v U) ->
  Cost.ticks (Local.project_c EX EC marked) <= Budget.projection b (length U).
Proof.
  intros Hwf Hsupport.
  set (vs := FinSet.elements marked).
  assert (Hvs : forall v, In v vs -> In v U).
  { intros v Hv; apply Hsupport, (FinSet.elements_spec EV HE v marked Hwf), Hv. }
  assert (Hlength : (length vs <= length U)%nat).
  { apply NoDup_incl_length; [apply (FinSet.elements_nodup EV), Hwf|exact Hvs]. }
  assert (Hget : forall v value, Map.get EV v marked = Some value -> In v U).
  { intros v value Hvalue; apply Hsupport; rewrite FinSet.mem_equation, Hvalue; reflexivity. }
  assert (Hmap_size : (Map.size marked <= length U)%nat).
  { apply (Map.size_support_bound EV HE U marked Hwf Hget). }
  assert (Hbits : forall v value, Map.get EV v marked = Some value ->
    key_bits EV v <= Budget.vertex_digits b).
  { intros v value Hv; exact (proj2 (vertices HB v (Hget v value Hv))). }
  pose proof (MapCost.elements_numeric_cost EV marked (Budget.vertex_digits b) Hwf Hbits)
    as Hmap.
  assert (Henum : Cost.ticks (FinSet.elements_c marked) <=
    TrieCost.trie_k * (1 + N.of_nat (length U) * Budget.vertex_digits b) +
      N.of_nat (length U)).
  { rewrite FinSet.elements_cost_equation.
    assert (Hsize : Map.size marked = FinSet.size marked).
    { rewrite FinSet.size_elements, FinSet.elements_equation, length_map, Map.size_elements.
      reflexivity. }
    rewrite <- Hsize; apply N.add_le_mono; [|lia].
    eapply N.le_trans; [exact Hmap|].
    apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r; lia. }
  destruct (projection_traversals vs) as [Hl [Hr [Hxl Hcl]]].
  assert (Hleft : forall x, In x (Cost.value (Local.lefts_c vs)) ->
    Cost.ticks (encode_c EX x) <= Budget.key_encoder b /\ key_bits EX x <= Budget.key_digits b).
  { intros x Hx; exact (unknown_keys HB x
      (Hvs (inl x) (proj1 (LocalProof.lefts_member vs x) Hx))). }
  assert (Hright : forall c, In c (Cost.value (Local.rights_c vs)) ->
    Cost.ticks (encode_c EC c) <= Budget.row_encoder b /\ key_bits EC c <= Budget.row_digits b).
  { intros c Hc; exact (row_keys HB c (proj1 (row_support a HL roots c)
      (Hvs (inr c) (proj1 (LocalProof.rights_member vs c) Hc)))). }
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold EX
    (Cost.value (Local.lefts_c vs)) _ _ Hleft) as Hkeys.
  pose proof (FinSet.of_list_numeric_cost Map.cost_laws_hold EC
    (Cost.value (Local.rights_c vs)) _ _ Hright) as Hrows.
  unfold Local.project_c; rewrite !Cost.ticks_bind, Cost.ticks_ret.
  change (Cost.ticks (FinSet.elements_c marked) +
    (Cost.ticks (Local.lefts_c vs) + (Cost.ticks (Local.rights_c vs) +
      (Cost.ticks (FinSet.of_list_c EX (Cost.value (Local.lefts_c vs))) +
        (Cost.ticks (FinSet.of_list_c EC (Cost.value (Local.rights_c vs))) + 0)))) <=
    Budget.projection b (length U)).
  unfold Budget.projection.
  nia.
Qed.

(** Public discovery retains original index preparation and projection of completed sets. *)
Theorem public_discover_cost fuel preparation :
  SystemIndexCost.cost_model EX (Analysis.system a) (Analysis.static a)
    (System.constraints (Analysis.system a)) preparation ->
  Cost.ticks (Local.discover_c a roots fuel) <=
    SystemIndexCost.Budget.preparation preparation
      (length (System.constraints (Analysis.system a))) +
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * LocalCredit.sum (LocalCredit.weight next) U +
    N.pos (Pos.size fuel) + Budget.projection b (length U).
Proof.
  intro HP.
  pose proof (SystemIndexCost.index_system_cost EX (Analysis.key_laws HL)
    (Analysis.system a) (Analysis.static a) preparation HP) as Hindex.
  pose proof (local_discover_full_cost fuel) as Hraw.
  assert (Hprojection : forall marked, LocalDiscover.run a ix roots fuel = inr marked ->
    Cost.ticks (Local.project_c EX EC marked) <= Budget.projection b (length U)).
  { intros marked Hrun; unfold LocalDiscover.run, LocalDiscover.run_c in Hrun.
    rewrite Cost.value_bind, value_map_c in Hrun.
    destruct (LocalDiscover.completed_closed EV HE next entries fuel marked Hrun)
      as [Hwf _].
    apply (project_cost marked Hwf).
    apply (LocalDiscover.completed_least EV HE next entries fuel marked
      (fun v => In v U)).
    - split; [exact (roots_support a HL roots)|].
      intros v w Hv Hw; exact (support_closed a HL roots v Hv w Hw).
    - exact Hrun. }
  rewrite Local.discover_cost, Local.discover_indexed_cost.
  change (Cost.ticks (index_system_c EX (Analysis.system a) (Analysis.static a)) +
    (Cost.ticks (LocalDiscover.run_c a ix roots fuel) +
      match LocalDiscover.run a ix roots fuel with
      | inl _ => 0
      | inr marked => Cost.ticks (Local.project_c EX EC marked)
      end) <=
    SystemIndexCost.Budget.preparation preparation
      (length (System.constraints (Analysis.system a))) +
    (Budget.w b + 4) * N.of_nat (length roots) +
    (4 * Budget.w b + 10) * LocalCredit.sum (LocalCredit.weight next) U +
    N.pos (Pos.size fuel) + Budget.projection b (length U)).
  destruct (LocalDiscover.run a ix roots fuel) as [state|marked] eqn:Hrun.
  - nia.
  - specialize (Hprojection marked eq_refl); nia.
Qed.

End Numeric.

(** Discovery families have numeric big-O bounds without conditional complete-run premises. *)
Theorem local_bigO {T X C A} (a : T -> Analysis.t X C A)
    (HL : forall t, Analysis.laws (a t)) (roots : T -> list X)
    (b : T -> Budget.t) (HB : forall t, model (a t) (roots t) (b t)) (fuel : T -> positive) :
  bigO (fun t =>
    let ix := index_system (Analysis.key_enc (a t)) (Analysis.system (a t))
      (Analysis.static (a t)) in
    (Budget.w (b t) + 4) * N.of_nat (length (roots t)) +
    (4 * Budget.w (b t) + 10) *
      LocalCredit.sum (LocalCredit.weight (LocalDiscover.adjacent_c (a t) ix))
        (support (a t) (roots t)) + N.pos (Pos.size (fuel t)))
    (fun t => Cost.ticks (LocalDiscover.run_c (a t)
      (index_system (Analysis.key_enc (a t)) (Analysis.system (a t)) (Analysis.static (a t)))
      (roots t) (fuel t))).
Proof.
  exists 1; intro t; pose proof (local_discover_full_cost (a t) (HL t) (roots t)
    (b t) (HB t) (fuel t)) as Hcost; cbn zeta; nia.
Qed.

End LocalCost.
Import LocalCost.
