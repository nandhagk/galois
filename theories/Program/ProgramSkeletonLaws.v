(** * Skeleton control-flow laws

    Indexed slots describe the reachable steps of the continuation machine.
    For example, a conditional branch selects one of two distinct slots.
    Builds on: ProgramSkeletonCfg and ProgramSkeletonMachine. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCfg ProgramLink
  ProgramSkeleton ProgramSkeletonMachine ProgramSkeletonCfg.
Import List.ListNotations Skeleton.

Local Lemma fold_lookup_agrees {K V} (enc : encoding K) (HE : encoding_laws enc)
    (rows : list (K * V)) k (f : K -> option V) :
  (forall a v, In (a, v) rows -> f a = Some v) ->
  forall old, old = f k \/ old = None ->
  (forall v, f k = Some v -> old = Some v \/ In (k, v) rows) ->
  fold_left (fun old kv => if eqb enc k (fst kv) then Some (snd kv) else old)
    rows old = f k.
Proof.
  induction rows as [|[a v] rows IH]; intros Hrows old Hold Hcomplete.
  - cbn; destruct Hold as [-> | ->]; [reflexivity|].
    destruct (f k) as [v|] eqn:Hvalue; [|reflexivity].
    destruct (Hcomplete v eq_refl) as [Hbad|Hbad]; [discriminate|contradiction].
  - cbn [fold_left fst snd]; destruct (eqb enc k a) eqn:Heq.
    + apply (eqb_true_iff enc HE) in Heq; subst a.
      apply IH.
      * intros b w Hin; apply Hrows; right; exact Hin.
      * left; symmetry; apply Hrows; left; reflexivity.
      * intros w Hw; left; pose proof (Hrows k v (or_introl eq_refl)); congruence.
    + apply (eqb_false_iff enc HE) in Heq; apply IH.
      * intros b w Hin; apply Hrows; right; exact Hin.
      * exact Hold.
      * intros w Hw; destruct (Hcomplete w Hw) as [Hold'|[Hhead|Hin]].
        -- left; exact Hold'.
        -- exfalso; apply Heq; congruence.
        -- right; exact Hin.
Qed.

Local Lemma map_bindings_agree {K V} (enc : encoding K) (HE : encoding_laws enc)
    (rows : list (K * V)) (f : K -> option V) :
  (forall k v, In (k, v) rows <-> f k = Some v) ->
  forall k, Map.get enc k (Map.of_list enc rows) = f k.
Proof.
  intros Hrows k; rewrite Map.of_list_get.
  eapply (fold_lookup_agrees enc HE rows k f).
  - intros a v Hin; apply Hrows; exact Hin.
  - right; reflexivity.
  - intros v Hv; right; apply Hrows; exact Hv.
Qed.

Local Lemma numbered_out_spec {A G} v i xs (e : skel_edge A G) x :
  In (e, x) (numbered_out v i xs) <->
  from e = v /\ exists j, slot e = i + j /\ nth_error xs j = Some x.
Proof.
  revert i; induction xs as [|y xs IH]; intro i; rewrite numbered_out_equation.
  - cbn; split; [contradiction|intros [_ [j [_ Hnth]]]; destruct j; discriminate].
  - cbn [In]; rewrite IH; split.
    + intros [Heq|[Hfrom [j [Hslot Hnth]]]].
      * inversion Heq; subst; split; [reflexivity|exists 0; cbn; auto with arith].
      * split; [exact Hfrom|exists (S j); split; [cbn; lia|exact Hnth]].
    + intros [Hfrom [[|j] [Hslot Hnth]]].
      * cbn in Hnth; inversion Hnth; subst x; left; destruct e; cbn in *;
          subst; f_equal; f_equal; lia.
      * right; split; [exact Hfrom|exists j; split; [lia|exact Hnth]].
Qed.

Local Lemma nodes_spec {A G} (prog : stmt A G) v :
  In v (Graph.nodes (Cfg.graph (skeleton_cfg prog))) <->
  match v with PEntry p | PExit p => exists k, context prog p k end.
Proof.
  rewrite skeleton_cfg_nodes, in_flat_map; destruct v as [p|p]; split.
  all: try solve [intros [q [Hin [Heq|[Heq|Hfalse]]]]; try contradiction;
    inversion Heq; subst q; apply (proj2 (positions_exact prog)) in Hin;
    destruct Hin as [s Hsub]; eapply sub_context; exact Hsub].
  all: intros [k Hctx]; exists p; split;
    [apply (proj2 (positions_exact prog)); eapply context_sub; exact Hctx|cbn; tauto].
Qed.

Local Lemma outgoing_source_node {A G} (prog : stmt A G) v i x :
  nth_error (skel_out prog v) i = Some x ->
  In v (Graph.nodes (Cfg.graph (skeleton_cfg prog))).
Proof.
  destruct v as [p|p]; intro Hnth; apply nodes_spec.
  - cbn [skel_out] in Hnth; destruct (sub prog p) as [s|] eqn:Hsub.
    + eapply sub_context; exact Hsub.
    + destruct i; discriminate.
  - cbn [skel_out] in Hnth; destruct (locate prog p) as [[s k]|] eqn:Hloc.
    + exists k; exact (proj1 (locate_context prog p s k Hloc)).
    + destruct i; discriminate.
Qed.

Local Lemma indexed_rows {A G} (prog : stmt A G) :
  flat_map (fun r => Cost.value (row_out_c r))
    (fst (syntax_rows prog [] [] 0)) =
  map (fun v => (v, numbered_out v 0 (skel_out prog v)))
    (Graph.nodes (Cfg.graph (skeleton_cfg prog))).
Proof.
  rewrite prepared_rows_agree, skeleton_cfg_nodes.
  induction (positions prog) as [|p ps IH]; cbn [flat_map map].
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

(** Payload lookups retain the reference selector's target, actions and absent-slot behaviour. *)
Theorem prepared_payload_agrees {A G} (prog : stmt A G) (e : skel_edge A G) :
  Map.get skel_edge_encoding e (indexed_payload (skeleton_index prog)) =
    nth_error (skel_out prog (from e)) (slot e).
Proof.
  rewrite skeleton_index_equation; cbn [indexed_payload].
  rewrite indexed_rows.
  apply (map_bindings_agree _ skel_edge_encoding_laws _
    (fun edge => nth_error (skel_out prog (from edge)) (slot edge))).
  intros edge x; rewrite in_flat_map; split.
  - intros [row [Hrow Hedge]]; apply in_map_iff in Hrow.
    destruct Hrow as [v [<- Hnode]]; cbn in Hedge.
    apply numbered_out_spec in Hedge; destruct Hedge as [Hfrom [j [Hslot Hnth]]].
    cbn in Hslot; rewrite Hfrom, Hslot; exact Hnth.
  - intro Hnth; exists (from edge, numbered_out (from edge) 0 (skel_out prog (from edge))).
    split.
    + apply in_map_iff; exists (from edge); split; [reflexivity|].
      eapply outgoing_source_node; exact Hnth.
    + apply numbered_out_spec; split; [reflexivity|exists (slot edge); split;
        [reflexivity|exact Hnth]].
Qed.

Local Lemma point_eq_dec (u v : skel_point) : {u = v} + {u <> v}.
Proof.
  decide equality; apply list_eq_dec; decide equality.
Defined.

(** Outgoing indexed slots retain reference order at every point, including invalid positions. *)
Theorem prepared_keys_agree {A G} (prog : stmt A G) v :
  indexed_keys (skeleton_index prog) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v))).
Proof.
  assert (Hget : Map.get skel_point_encoding v (indexed_out (skeleton_index prog)) =
    if in_dec point_eq_dec v (Graph.nodes (Cfg.graph (skeleton_cfg prog)))
    then Some (map fst (numbered_out v 0 (skel_out prog v))) else None).
  { rewrite skeleton_index_equation; cbn [indexed_out]; rewrite indexed_rows.
    apply (map_bindings_agree _ skel_point_encoding_laws _ (fun u =>
      if in_dec point_eq_dec u (Graph.nodes (Cfg.graph (skeleton_cfg prog)))
      then Some (map fst (numbered_out u 0 (skel_out prog u))) else None)).
    intros u es; rewrite map_map, in_map_iff.
    destruct (in_dec point_eq_dec u (Graph.nodes (Cfg.graph (skeleton_cfg prog))))
      as [Hin|Hnot].
    - split.
      + intros [w [Heq Hnode]]; inversion Heq; reflexivity.
      + intro Heq; inversion Heq; exists u; split; [reflexivity|exact Hin].
    - split.
      + intros [w [Heq Hnode]]; inversion Heq; subst; contradiction.
      + discriminate. }
  rewrite indexed_keys_equation, Hget.
  destruct (in_dec _ _ _) as [Hin|Hnot].
  - apply numbered_out_keys.
  - destruct (skel_out prog v) as [|x xs] eqn:Hout; [reflexivity|].
    exfalso; apply Hnot; eapply outgoing_source_node with (i := 0) (x := x).
    rewrite Hout; reflexivity.
Qed.

(** Targets are the reference slot target and fall back to the source for absent slots. *)
Theorem skel_to_agrees {A G} (prog : stmt A G) e :
  skel_to prog e =
    match nth_error (skel_out prog (from e)) (slot e) with
    | Some (t, _) => t
    | None => from e
    end.
Proof.
  unfold skel_to; rewrite indexed_to_equation, prepared_payload_agrees; reflexivity.
Qed.

(** Actions are the reference slot actions and are empty for absent slots. *)
Theorem skel_acts_agrees {A G} (prog : stmt A G) e :
  skel_acts prog e =
    match nth_error (skel_out prog (from e)) (slot e) with
    | Some (_, xs) => xs
    | None => []
    end.
Proof.
  unfold skel_acts; rewrite indexed_acts_equation, prepared_payload_agrees; reflexivity.
Qed.

(** The graph's public outgoing callback observes its retained slot index. *)
Theorem skeleton_cfg_out {A G} (prog : stmt A G) v :
  Graph.out (Cfg.graph (skeleton_cfg prog)) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v))).
Proof.
  change (indexed_keys (skeleton_index prog) v =
    map (SkelEdge v) (seq 0 (length (skel_out prog v)))).
  apply prepared_keys_agree.
Qed.

Local Lemma resume_target_map {St} n k (st : St) :
  option_map machine_point (resume n k st) = resume_target n k.
Proof.
  revert n; induction k as [|f k IH]; intro n; rewrite resume_target_equation.
  - reflexivity.
  - destruct f; cbn [resume]; try apply IH.
    all: destruct n; [reflexivity|apply IH].
Qed.

Local Lemma enclosing_locate {A G} (s : stmt A G) base p k t k' :
  locate_from s base p k = Some (t, k') -> enclosing_from s base p k = k'.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hloc.
  - cbn in Hloc; inversion Hloc; reflexivity.
  - cbn [locate_from] in Hloc; cbn [enclosing_from].
    destruct (child s d); [eapply IH; exact Hloc|discriminate].
Qed.

Local Lemma context_enclosing {A G} (prog : stmt A G) p k :
  context prog p k -> enclosing_from prog [] p [] = k.
Proof.
  intro Hctx; destruct (context_locate prog p k Hctx) as [s [Hloc _]].
  eapply enclosing_locate; exact Hloc.
Qed.

Local Lemma label_point_resume {A G St} (prog : stmt A G) p k n (st : St) m :
  context prog p k -> resume n k st = Some m ->
  label_point prog p n = Some (machine_point m).
Proof.
  intros Hctx Hresume; unfold label_point; rewrite (context_enclosing prog p k Hctx).
  rewrite <- (resume_target_map n k st), Hresume; reflexivity.
Qed.

Local Lemma holds_single {A G St O} (C : skeleton_client A G St O) x st l st' :
  act_hold C x st l st' -> acts_hold C [x] st l st'.
Proof.
  intro Hact; rewrite <- (app_nil_r l); econstructor; [exact Hact|constructor].
Qed.

Local Lemma holds_guard {A G St O} (C : skeleton_client A G St O) g b st :
  guard_bool C g st = Some b -> acts_hold C [AGuard g b] st [] st.
Proof.
  intro Hguard; apply holds_single; repeat split; assumption || reflexivity.
Qed.

Local Lemma jump_out_in {A G} k p n (xs : list (skel_action A G)) v :
  resume_target n k = Some v -> In (v, xs) (Cost.value (jump_out_c k p n xs)).
Proof.
  intro Hlabel; unfold jump_out_c; rewrite Cost.value_map.
  change (In (v, xs) (match resume_target n k with Some q => [(q, xs)] | None => [] end)).
  rewrite Hlabel; left; reflexivity.
Qed.

Local Definition jump_out {A G} k p n (xs : list (skel_action A G)) :=
  Cost.value (jump_out_c k p n xs).

Local Definition table_out {A G} k p g ns i :=
  Cost.value (@table_out_c A G k p g ns i).

Local Lemma jump_out_equation {A G} k p n (xs : list (skel_action A G)) :
  jump_out k p n xs =
  match resume_target n k with Some v => [(v, xs)] | None => [] end.
Proof.
  unfold jump_out, jump_out_c; rewrite Cost.value_map; reflexivity.
Qed.

Local Lemma table_out_equation {A G} k p g ns i :
  @table_out A G k p g ns i =
  match ns with
  | [] => []
  | n :: ns => jump_out k p n [AIndexIs g i; AJump p n] ++ table_out k p g ns (S i)
  end.
Proof.
  destruct ns; [reflexivity|].
  unfold table_out at 1; cbn [table_out_c].
  rewrite !Cost.value_bind, value_app_c; reflexivity.
Qed.

Local Lemma entry_out_equation {A G} (s : stmt A G) p k :
  entry_out s p k =
  match s with
  | Atom a => [(PExit p, [AAtom a])]
  | Seq _ _ => [(PEntry (p ++ [DFirst]), [])]
  | If g _ _ =>
    [(PEntry (p ++ [DFirst]), [AGuard g true]);
     (PEntry (p ++ [DSecond]), [AGuard g false])]
  | Block _ | Loop _ => [(PEntry (p ++ [DBody]), [])]
  | Jump n => jump_out k p n [AJump p n]
  | JumpIf g n => jump_out k p n [AGuard g true; AJump p n] ++
    [(PExit p, [AGuard g false])]
  | JumpTable g ns n => table_out k p g ns 0 ++
    jump_out k p n [AIndexAtLeast g (length ns); AJump p n]
  end.
Proof.
  destruct s; unfold entry_out, entry_out_c;
    autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma return_point_equation f :
  return_point f =
  match f with
  | FSeq p => PEntry (p ++ [DSecond])
  | FJoin p | FBlock p => PExit p
  | FLoop p => PEntry (p ++ [DBody])
  end.
Proof.
  destruct f; unfold return_point, return_point_c;
    autorewrite with galois_cost; reflexivity.
Qed.

Local Definition point_valid {A G} (prog : stmt A G) v :=
  In v (Graph.nodes (Cfg.graph (skeleton_cfg prog))).

Local Lemma resume_target_valid {A G} (prog : stmt A G) k n v :
  stack_valid prog k -> resume_target n k = Some v -> point_valid prog v.
Proof.
  intros Hvalid Htarget; pose proof (resume_target_map n k tt) as Hmap.
  rewrite Htarget in Hmap; destruct (resume n k tt) as [m|] eqn:Hresume;
    cbn in Hmap; [|discriminate].
  inversion Hmap; subst v.
  pose proof (resume_context prog n k tt m Hvalid Hresume) as Hctx.
  destruct m; apply nodes_spec; eexists; exact Hctx.
Qed.

Local Lemma return_point_valid {A G} (prog : stmt A G) f k :
  stack_valid prog (f :: k) -> point_valid prog (return_point f).
Proof.
  intros [_ Hframe]; rewrite return_point_equation.
  destruct f as [p|p|p|p]; destruct Hframe as [Hctx Howner]; apply nodes_spec.
  - destruct Howner as [s1 [s2 Hsub]]; exists (FJoin p :: k).
    eapply (context_child (s := Seq s1 s2) (d := DSecond)); eassumption || reflexivity.
  - exists k; exact Hctx.
  - exists k; exact Hctx.
  - destruct Howner as [s Hsub]; exists (FLoop p :: k).
    eapply (context_child (s := Loop s) (d := DBody)); eassumption || reflexivity.
Qed.

Local Lemma jump_out_valid {A G} (prog : stmt A G) k p n
    (xs : list (skel_action A G)) v ys :
  stack_valid prog k -> In (v, ys) (jump_out k p n xs) -> point_valid prog v.
Proof.
  intros Hvalid; rewrite jump_out_equation.
  destruct (resume_target n k) as [t|] eqn:Htarget; [|cbn; tauto].
  intros [Heq|Hfalse]; [inversion Heq; subst; eapply resume_target_valid; eassumption|
    contradiction].
Qed.

Local Lemma table_out_valid {A G} (prog : stmt A G) k p g ns i v
    (xs : list (skel_action A G)) :
  stack_valid prog k -> In (v, xs) (table_out k p g ns i) -> point_valid prog v.
Proof.
  intro Hvalid; revert i; induction ns as [|n ns IH]; intros i Hin;
    rewrite table_out_equation in Hin; [contradiction|].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - eapply jump_out_valid; eassumption.
  - eapply IH; exact Hin.
Qed.

Local Lemma skel_out_valid {A G} (prog : stmt A G) u v xs :
  point_valid prog u -> In (v, xs) (skel_out prog u) -> point_valid prog v.
Proof.
  destruct u as [p|p]; intro Hvalid; apply nodes_spec in Hvalid; destruct Hvalid as [k Hctx].
  - cbn [skel_out]; destruct (context_sub prog p k Hctx) as [s Hsub]; rewrite Hsub.
    rewrite entry_out_equation, (context_enclosing prog p k Hctx).
    pose proof (context_stack_valid prog p k Hctx) as Hstack.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n]; cbn.
    + intros [Heq|Hfalse]; [inversion Heq; subst; apply nodes_spec; eauto|contradiction].
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst; apply nodes_spec.
      exists (FSeq p :: k); eapply (context_child (s := Seq s1 s2) (d := DFirst));
        eassumption || reflexivity.
    + intros [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; subst; apply nodes_spec.
      * exists (FJoin p :: k); eapply (context_child (s := If g s1 s2) (d := DFirst));
          eassumption || reflexivity.
      * exists (FJoin p :: k); eapply (context_child (s := If g s1 s2) (d := DSecond));
          eassumption || reflexivity.
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst; apply nodes_spec.
      exists (FBlock p :: k); eapply (context_child (s := Block s) (d := DBody));
        eassumption || reflexivity.
    + intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst; apply nodes_spec.
      exists (FLoop p :: k); eapply (context_child (s := Loop s) (d := DBody));
        eassumption || reflexivity.
    + eapply (jump_out_valid prog k p n); exact Hstack.
    + intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
      * eapply (jump_out_valid prog k p n); eassumption.
      * inversion Heq; subst; apply nodes_spec; eauto.
      * contradiction.
    + intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * eapply (table_out_valid prog k p g ns 0); eassumption.
      * eapply (jump_out_valid prog k p n); eassumption.
  - cbn [skel_out]; destruct (context_locate prog p k Hctx) as [s [Hloc _]]; rewrite Hloc.
    destruct k as [|f k]; [cbn; tauto|].
    intros [Heq|Hfalse]; [|contradiction]; inversion Heq; subst.
    apply (return_point_valid prog f k); eapply context_stack_valid; exact Hctx.
Qed.

Local Lemma phase_nodes_nodup (ps : list position) :
  NoDup ps -> NoDup (flat_map (fun p => [PEntry p; PExit p]) ps).
Proof.
  intro Hnodup; induction Hnodup as [|p ps Hnot Hnodup IH]; cbn; [constructor|].
  constructor.
  - intros [Hbad|Hin]; [discriminate|].
    apply in_flat_map in Hin; destruct Hin as [q [Hin [Heq|[Heq|Hfalse]]]];
      try contradiction; inversion Heq; subst; contradiction.
  - constructor; [|exact IH].
    intro Hin; apply in_flat_map in Hin; destruct Hin as [q [Hin [Heq|[Heq|Hfalse]]]];
      try contradiction; inversion Heq; subst; contradiction.
Qed.

(** Outgoing keys identify exactly valid source slots. *)
Theorem skeleton_out_slot {A G} (prog : stmt A G) v (e : skel_edge A G) :
  In e (Graph.out (Cfg.graph (skeleton_cfg prog)) v) <->
  from e = v /\ slot e < length (skel_out prog v).
Proof.
  rewrite skeleton_cfg_out; destruct e as [u i]; cbn [from slot].
  rewrite in_map_iff; split.
  - intros [j [Heq Hin]]; inversion Heq; subst; split; [reflexivity|].
    apply in_seq in Hin; lia.
  - intros [-> Hbound]; exists i; split; [reflexivity|apply in_seq; lia].
Qed.

(** Skeleton preparation constructs a closed graph with distinct nodes. *)
Theorem skeleton_graph_wf {A G} (prog : stmt A G) :
  graph_wf (Cfg.graph (skeleton_cfg prog)).
Proof.
  constructor.
  - rewrite skeleton_cfg_nodes; apply phase_nodes_nodup; exact (proj1 (positions_exact prog)).
  - intros v [<-|Hfalse]; [apply nodes_spec; exists []; constructor|contradiction].
  - intros v e Hin; exact (proj1 (proj1 (skeleton_out_slot prog v e) Hin)).
  - intros v e Hnode Hedge; apply skeleton_out_slot in Hedge; destruct Hedge as [Hfrom Hbound].
    change (point_valid prog (skel_to prog e)).
    rewrite skel_to_agrees, Hfrom.
    destruct (nth_error (skel_out prog v) (slot e)) as [[t xs]|] eqn:Hnth.
    + eapply skel_out_valid; [exact Hnode|apply nth_error_In in Hnth; exact Hnth].
    + apply nth_error_None in Hnth; lia.
Qed.

Local Lemma table_out_nth {A G} k p g ns i j n v :
  nth_error ns j = Some n -> resume_target n k = Some v ->
  In (v, [AIndexIs g (i + j); AJump p n]) (@table_out A G k p g ns i).
Proof.
  revert i j; induction ns as [|a ns IH]; intros i [|j] Hnth Hlabel;
    cbn in Hnth; try discriminate; rewrite table_out_equation.
  - inversion Hnth; subst; apply in_or_app; left; rewrite Nat.add_0_r.
    apply jump_out_in; exact Hlabel.
  - apply in_or_app; right; replace (i + S j) with (S i + j) by lia.
    eapply IH; eassumption.
Qed.

Local Lemma resume_store {St} n k (st : St) m :
  resume n k st = Some m -> store_of m = st.
Proof.
  revert n; induction k as [|f k IH]; intros n Hresume; [discriminate|].
  destruct f; cbn in Hresume; try (eapply IH; exact Hresume).
  all: destruct n; [inversion Hresume; reflexivity|eapply IH; exact Hresume].
Qed.

Local Lemma holds_guard_jump {A G St O} (C : skeleton_client A G St O) g b p n st st' :
  guard_bool C g st = Some b -> jump_effect C p n st st' ->
  acts_hold C [AGuard g b; AJump p n] st [] st'.
Proof.
  intros Hguard Heffect; change (acts_hold C [AGuard g b; AJump p n] st ([] ++ []) st').
  econstructor; [repeat split; assumption || reflexivity|].
  apply holds_single; split; [exact Heffect|reflexivity].
Qed.

Local Lemma table_out_selected {A G St O} (C : skeleton_client A G St O)
    p k st g ns n i st' m :
  guard_index C g st = Some i -> jump_effect C p (nth i ns n) st st' ->
  resume (nth i ns n) k st' = Some m ->
  exists xs, In (machine_point m, xs)
    (table_out k p g ns 0 ++ jump_out k p n [AIndexAtLeast g (length ns); AJump p n]) /\
    acts_hold C xs st [] (store_of m).
Proof.
  intros Hguard Heffect Hresume.
  assert (Hstore : store_of m = st') by (eapply resume_store; exact Hresume).
  assert (Hlabel : resume_target (nth i ns n) k = Some (machine_point m)).
  { rewrite <- (resume_target_map _ _ st'), Hresume; reflexivity. }
  destruct (lt_dec i (length ns)) as [Hin|Hout].
  - exists [AIndexIs g i; AJump p (nth i ns n)]; split.
    + apply in_or_app; left; replace i with (0 + i) at 1 by lia.
      eapply table_out_nth; [apply nth_error_nth'; exact Hin|exact Hlabel].
    + rewrite Hstore; change (acts_hold C [AIndexIs g i; AJump p (nth i ns n)]
        st ([] ++ []) st').
      econstructor; [repeat split; assumption || reflexivity|].
      apply holds_single; split; [exact Heffect|reflexivity].
  - rewrite nth_overflow in Heffect, Hlabel by lia.
    exists [AIndexAtLeast g (length ns); AJump p n]; split.
    + apply in_or_app; right; apply jump_out_in; exact Hlabel.
    + rewrite Hstore; change (acts_hold C [AIndexAtLeast g (length ns); AJump p n]
        st ([] ++ []) st').
      econstructor.
      * split; [exists i; split; [exact Hguard|lia]|split; reflexivity].
      * apply holds_single; split; [exact Heffect|reflexivity].
Qed.

Local Lemma return_out {A G} (prog : stmt A G) c f k :
  context prog c (f :: k) ->
  In ((match f with
    | FSeq p => PEntry (p ++ [DSecond])
    | FJoin p | FBlock p => PExit p
    | FLoop p => PEntry (p ++ [DBody])
    end), []) (skel_out prog (PExit c)).
Proof.
  intro Hctx; destruct (context_locate prog c (f :: k) Hctx) as [s [Hloc _]].
  cbn [skel_out]; rewrite Hloc, return_point_equation; left; reflexivity.
Qed.

Local Lemma machine_step_out {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : machine_valid prog m -> skel_step prog C m l m' ->
  exists xs, In (machine_point m', xs) (skel_out prog (machine_point m)) /\
    acts_hold C xs (store_of m) l (store_of m').
Proof.
  intros Hvalid Hstep; destruct Hstep as
    [p k st a l st' Hsub Hatom
    |p k st s1 s2 Hsub
    |p k st g s1 s2 b Hsub Hguard
    |p k st s Hsub
    |p k st s Hsub
    |p k st n st' m Hsub Heffect Hresume
    |p k st g n st' m Hsub Hguard Heffect Hresume
    |p k st g n Hsub Hguard
    |p k st g ns n i st' m Hsub Hguard Heffect Hresume
    |c p k st|c p k st|c p k st|c p k st];
    cbn [machine_valid machine_point store_of] in *.
  all: try match goal with
  | Hsub : sub _ _ = Some _ |- _ =>
    cbn [skel_out]; rewrite Hsub, entry_out_equation;
    try rewrite (context_enclosing _ _ _ Hvalid)
  end.
  - exists [AAtom a]; split; [left; reflexivity|apply holds_single; assumption].
  - exists []; split; [left; reflexivity|constructor].
  - exists [AGuard g b]; split; [destruct b; cbn; tauto|apply holds_guard; exact Hguard].
  - exists []; split; [left; reflexivity|constructor].
  - exists []; split; [left; reflexivity|constructor].
  - exists [AJump p n]; split.
    + apply jump_out_in; rewrite <- (resume_target_map n k st'), Hresume; reflexivity.
    + rewrite (resume_store _ _ _ _ ltac:(eassumption)); apply holds_single; split;
        assumption || reflexivity.
  - exists [AGuard g true; AJump p n]; split.
    + apply in_or_app; left; apply jump_out_in.
      rewrite <- (resume_target_map n k st'), Hresume; reflexivity.
    + rewrite (resume_store _ _ _ _ ltac:(eassumption)); apply holds_guard_jump; assumption.
  - exists [AGuard g false]; split.
    + apply in_or_app; right; left; reflexivity.
    + apply holds_single; repeat split; assumption || reflexivity.
  - eapply table_out_selected; eassumption.
  - exists []; split; [exact (return_out prog c (FSeq p) k Hvalid)|constructor].
  - exists []; split; [exact (return_out prog c (FJoin p) k Hvalid)|constructor].
  - exists []; split; [exact (return_out prog c (FBlock p) k Hvalid)|constructor].
  - exists []; split; [exact (return_out prog c (FLoop p) k Hvalid)|constructor].
Qed.

Local Lemma machine_step_taken {A G St O} (prog : stmt A G) (C : skeleton_client A G St O)
    m l m' : machine_valid prog m -> skel_step prog C m l m' ->
  exists e, Link.taken (skeleton_link prog C) m l m' e.
Proof.
  intros Hvalid Hstep; destruct (machine_step_out prog C m l m' Hvalid Hstep)
    as [xs [Hin Hacts]].
  apply In_nth_error in Hin; destruct Hin as [i Hnth].
  exists (SkelEdge (machine_point m) i); split.
  - change (In (SkelEdge (machine_point m) i)
      (Graph.out (Cfg.graph (skeleton_cfg prog)) (machine_point m))).
    apply skeleton_out_slot; split; [reflexivity|].
    cbn [slot]; apply nth_error_Some; rewrite Hnth; discriminate.
  - change (machine_point m' = skel_to prog (SkelEdge (machine_point m) i) /\
      acts_hold C (skel_acts prog (SkelEdge (machine_point m) i))
        (store_of m) l (store_of m')).
    rewrite skel_to_agrees, skel_acts_agrees; cbn [from slot].
    rewrite Hnth; split; [reflexivity|exact Hacts].
Qed.

(** Every reachable skeleton machine step follows a listed slot with its actual actions. *)
Theorem skeleton_link_laws {A G St O} (prog : stmt A G)
    (C : skeleton_client A G St O) :
  link_laws (skeleton_machine C prog) (Cfg.graph (skeleton_cfg prog)) (skeleton_link prog C).
Proof.
  constructor.
  - apply skeleton_graph_wf.
  - intros m [st [-> Hinit]]; left; reflexivity.
  - intros m l m' Hreachable Hstep; right; apply machine_step_taken.
    + eapply reachable_machine_valid; exact Hreachable.
    + exact Hstep.
  - intros e m l m' _ _ [Hout [Htarget Hacts]].
    split; [exact Hout|symmetry; exact Htarget].
  - intros m l m' _ _ Hfalse; contradiction.
Qed.

Local Lemma split_last_snoc p d : split_last (p ++ [d]) = Some (p, d).
Proof.
  induction p as [|x p IH]; [reflexivity|].
  destruct p as [|y p]; cbn in *; [reflexivity|rewrite IH; reflexivity].
Qed.

Local Lemma split_last_spec p q d : split_last p = Some (q, d) -> p = q ++ [d].
Proof.
  revert q; induction p as [|x p IH]; intros q Hsplit; [discriminate|].
  destruct p as [|y p].
  - cbn in Hsplit; inversion Hsplit; reflexivity.
  - change (match split_last (y :: p) with
      | Some (base, last) => Some (x :: base, last)
      | None => None
      end = Some (q, d)) in Hsplit.
    destruct (split_last (y :: p)) as [[r e]|] eqn:Htail; [|discriminate].
    inversion Hsplit; subst; cbn; f_equal; apply IH; reflexivity.
Qed.

(** Loop-head recognition agrees exactly with the public loop-head enumeration. *)
Theorem is_loop_head_iff {A G} (prog : stmt A G) (n : skel_point) :
  is_loop_head prog n = true <-> In n (loop_heads prog).
Proof.
  unfold loop_heads; rewrite in_flat_map; destruct n as [p|p]; split.
  - cbn [is_loop_head]; destruct (split_last p) as [[q d]|] eqn:Hsplit;
      [destruct d|]; try discriminate.
    destruct (sub prog q) as [s|] eqn:Hsub; [destruct s|]; try discriminate.
    intros _; exists q; split.
    + apply (proj2 (positions_exact prog)); eexists; exact Hsub.
    + rewrite Hsub; cbn; left; f_equal; symmetry; apply split_last_spec; exact Hsplit.
  - intros [q [Hin Hnode]]; destruct (sub prog q) as [s|] eqn:Hsub;
      [destruct s|]; try contradiction.
    destruct Hnode as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
    cbn [is_loop_head]; rewrite split_last_snoc, Hsub; reflexivity.
  - discriminate.
  - intros [q [_ Hnode]]; destruct (sub prog q) as [s|]; [destruct s|];
      cbn in Hnode; try contradiction; destruct Hnode as [Hbad|Hfalse];
      [discriminate|contradiction].
Qed.

Local Lemma loop_body_head {A G} (prog : stmt A G) p s :
  sub prog p = Some (Loop s) -> is_loop_head prog (PEntry (p ++ [DBody])) = true.
Proof.
  intro Hsub; cbn [is_loop_head]; rewrite split_last_snoc, Hsub; reflexivity.
Qed.

(** * Mathematical interpretation of the retained ranks *)

Local Definition child_offset {A G} (s : stmt A G) d :=
  match s, d with
  | Seq a _, DSecond | If _ a _, DSecond => 1 + statement_span a
  | _, _ => 1
  end.

Local Fixpoint entry_rank {A G} (s : stmt A G) (p : position) : nat :=
  match p with
  | [] => 0
  | d :: p =>
    match child s d with
    | Some t => child_offset s d + entry_rank t p
    | None => 0
    end
  end.

Local Definition exit_rank {A G} (prog : stmt A G) p :=
  entry_rank prog p +
    match sub prog p with Some s => statement_span s - 1 | None => 0 end.

Local Definition point_rank {A G} (prog : stmt A G) v :=
  match v with
  | PEntry p => entry_rank prog p
  | PExit p => exit_rank prog p
  end.

Local Lemma statement_span_positive {A G} (s : stmt A G) : 2 <= statement_span s.
Proof.
  destruct s; cbn; lia.
Qed.

Local Lemma entry_rank_app {A G} (prog : stmt A G) p s q :
  sub prog p = Some s -> entry_rank prog (p ++ q) = entry_rank prog p + entry_rank s q.
Proof.
  revert prog s; induction p as [|d p IH]; intros prog s Hsub; cbn in *.
  - inversion Hsub; reflexivity.
  - destruct (child prog d) as [t|] eqn:Hchild; [|discriminate].
    rewrite (IH t s Hsub); lia.
Qed.

Local Lemma syntax_row_ranks {A G} (prog s : stmt A G) p k start :
  sub prog p = Some s -> start = entry_rank prog p ->
  forall r, In r (fst (syntax_rows s p k start)) ->
    row_entry_rank r = entry_rank prog (row_position r) /\
      row_exit_rank r = exit_rank prog (row_position r).
Proof.
  revert p k start; induction s; intros p k start Hsub Hstart r Hin;
    rewrite syntax_rows_equation in Hin; cbn [fst] in Hin;
    destruct Hin as [<-|Hin].
  all: try solve [
    cbn [row_entry_rank row_exit_rank row_position];
    rewrite ?syntax_rows_span; unfold exit_rank; rewrite Hsub;
    cbn [statement_span]; split; lia].
  all: try contradiction.
  all: try (apply in_app_or in Hin; destruct Hin as [Hin|Hin]).
  all: first [eapply IHs1 in Hin|eapply IHs2 in Hin|eapply IHs in Hin].
  all: try exact Hin.
  all: try solve [rewrite (sub_child prog p _ _ Hsub); reflexivity].
  all: rewrite (entry_rank_app prog p _ _ Hsub);
    cbn [entry_rank child child_offset]; rewrite ?syntax_rows_span; lia.
Qed.

Local Lemma rank_map_agrees {A G} (prog : stmt A G) (rows : list (syntax_row A G)) v :
  (forall r, In r rows ->
    row_entry_rank r = entry_rank prog (row_position r) /\
      row_exit_rank r = exit_rank prog (row_position r)) ->
  map row_position rows = positions prog ->
  Map.get skel_point_encoding v
    (Map.of_list skel_point_encoding
      (flat_map (fun r =>
        [(PEntry (row_position r), row_entry_rank r);
         (PExit (row_position r), row_exit_rank r)]) rows)) =
  if in_dec point_eq_dec v (Graph.nodes (Cfg.graph (skeleton_cfg prog)))
  then Some (point_rank prog v) else None.
Proof.
  intros Hranks Hpositions; apply (map_bindings_agree _ skel_point_encoding_laws _
    (fun w => if in_dec point_eq_dec w (Graph.nodes (Cfg.graph (skeleton_cfg prog)))
      then Some (point_rank prog w) else None)).
  intros w rank; rewrite in_flat_map.
  destruct (in_dec point_eq_dec w (Graph.nodes (Cfg.graph (skeleton_cfg prog))))
    as [Hw|Hw].
  - split.
    + intros [r [Hin [Heq|[Heq|Hbad]]]]; [| |contradiction].
      * inversion Heq; subst; cbn [point_rank]; rewrite (proj1 (Hranks r Hin)); reflexivity.
      * inversion Heq; subst; cbn [point_rank]; rewrite (proj2 (Hranks r Hin)); reflexivity.
    + intro Heq; injection Heq as <-.
      rewrite skeleton_cfg_nodes, in_flat_map in Hw.
      destruct Hw as [p [Hp [Heq|[Heq|Hbad]]]]; [| |contradiction].
      all: rewrite <- Hpositions in Hp; apply in_map_iff in Hp;
        destruct Hp as [r [Hrp Hin]]; exists r; split; [exact Hin|].
      * left; subst w; rewrite <- Hrp; cbn [point_rank]; rewrite (proj1 (Hranks r Hin));
          reflexivity.
      * right; left; subst w; rewrite <- Hrp; cbn [point_rank];
          rewrite (proj2 (Hranks r Hin)); reflexivity.
  - split; [|discriminate].
    intros [r [Hin [Heq|[Heq|Hbad]]]]; [| |contradiction].
    all: exfalso; apply Hw; rewrite skeleton_cfg_nodes; apply in_flat_map;
      exists (row_position r); split.
    all: try solve [rewrite <- Hpositions; apply in_map; exact Hin].
    all: inversion Heq; subst; cbn; tauto.
Qed.

Local Lemma cached_rank_agrees {A G} (prog : stmt A G) v :
  point_valid prog v ->
  indexed_point_rank (skeleton_index prog) v = Some (point_rank prog v).
Proof.
  intro Hvalid; unfold indexed_point_rank, indexed_point_rank_c.
  change (Map.get skel_point_encoding v (indexed_rank (skeleton_index prog)) =
    Some (point_rank prog v)).
  rewrite skeleton_index_equation; cbn [indexed_rank].
  rewrite (rank_map_agrees prog _ v).
  - destruct (in_dec _ _ _) as [Hin|Hnot]; [reflexivity|contradiction].
  - intros r Hin; exact (syntax_row_ranks prog prog [] [] 0 eq_refl eq_refl r Hin).
  - rewrite syntax_rows_positions; apply map_id.
Qed.

(** Every listed point has a rank retained by the syntax traversal. *)
Theorem skeleton_rank_present {A G} (prog : stmt A G) v :
  In v (Graph.nodes (Cfg.graph (skeleton_cfg prog))) ->
  exists rank, indexed_point_rank (skeleton_index prog) v = Some rank.
Proof.
  intro Hvalid; exists (point_rank prog v); apply cached_rank_agrees; exact Hvalid.
Qed.

(** Points outside the listed syntax domain have no retained rank. *)
Theorem skeleton_rank_absent {A G} (prog : stmt A G) v :
  ~ In v (Graph.nodes (Cfg.graph (skeleton_cfg prog))) ->
  indexed_point_rank (skeleton_index prog) v = None.
Proof.
  intro Habsent; unfold indexed_point_rank, indexed_point_rank_c.
  change (Map.get skel_point_encoding v (indexed_rank (skeleton_index prog)) = None).
  rewrite skeleton_index_equation; cbn [indexed_rank]; rewrite (rank_map_agrees prog _ v).
  - destruct (in_dec _ _ _) as [Hin|Hnot]; [contradiction|reflexivity].
  - intros r Hin; exact (syntax_row_ranks prog prog [] [] 0 eq_refl eq_refl r Hin).
  - rewrite syntax_rows_positions; apply map_id.
Qed.

Local Lemma child_span_bounds {A G} (s t : stmt A G) d :
  child s d = Some t -> 0 < child_offset s d /\
    child_offset s d + statement_span t < statement_span s.
Proof.
  destruct s; destruct d; cbn; intro Hchild; try discriminate;
    inversion Hchild; subst; cbn; lia.
Qed.

Local Lemma child_rank_bounds {A G} (prog : stmt A G) p s d t :
  sub prog p = Some s -> child s d = Some t ->
  entry_rank prog p < entry_rank prog (p ++ [d]) /\
    exit_rank prog (p ++ [d]) < exit_rank prog p.
Proof.
  intros Hsub Hchild; unfold exit_rank.
  rewrite (sub_child prog p s d Hsub), Hchild, Hsub, (entry_rank_app prog p s [d] Hsub).
  cbn [entry_rank]; rewrite Hchild; cbn [entry_rank].
  pose proof (child_span_bounds s t d Hchild) as Hbounds.
  pose proof (statement_span_positive t); pose proof (statement_span_positive s); lia.
Qed.

Local Lemma entry_before_exit {A G} (prog : stmt A G) p :
  (exists s, sub prog p = Some s) -> entry_rank prog p < exit_rank prog p.
Proof.
  intros [s Hsub]; unfold exit_rank; rewrite Hsub.
  pose proof (statement_span_positive s); lia.
Qed.

Local Lemma seq_first_before_second {A G} (prog : stmt A G) p s1 s2 :
  sub prog p = Some (Seq s1 s2) ->
  exit_rank prog (p ++ [DFirst]) < entry_rank prog (p ++ [DSecond]).
Proof.
  intro Hsub; unfold exit_rank; rewrite (sub_child prog p _ DFirst Hsub).
  rewrite (entry_rank_app prog p _ [DFirst] Hsub),
    (entry_rank_app prog p _ [DSecond] Hsub); cbn.
  pose proof (statement_span_positive s1); lia.
Qed.

Local Definition continuation_after {A G} (prog : stmt A G) p f :=
  is_loop_head prog (return_point f) = true \/
    exit_rank prog p < point_rank prog (return_point f).

Local Lemma context_continuations {A G} (prog : stmt A G) p k :
  context prog p k -> Forall (continuation_after prog p) k.
Proof.
  intro Hctx; induction Hctx as [|p k s d t Hctx IH Hsub Hchild]; [constructor|].
  pose proof (child_rank_bounds prog p s d t Hsub Hchild) as [_ Hexit].
  constructor.
  - unfold continuation_after; rewrite return_point_equation.
    destruct s; destruct d; cbn in Hchild; try discriminate; cbn [child_frame point_rank].
    + right; exact (seq_first_before_second prog p s1 s2 Hsub).
    + right; exact Hexit.
    + right; exact Hexit.
    + right; exact Hexit.
    + right; exact Hexit.
    + left; eapply loop_body_head; exact Hsub.
  - eapply Forall_impl; [|exact IH].
    intros f [Hloop|Hrank]; [left; exact Hloop|right; lia].
Qed.

Local Lemma context_entry_continuations {A G} (prog : stmt A G) p k :
  context prog p k -> Forall (fun f => is_loop_head prog (return_point f) = true \/
    entry_rank prog p < point_rank prog (return_point f)) k.
Proof.
  intro Hctx; pose proof (context_continuations prog p k Hctx) as Hall.
  pose proof (entry_before_exit prog p (context_sub prog p k Hctx)) as Hentry.
  eapply Forall_impl; [|exact Hall].
  intros f [Hloop|Hrank]; [left; exact Hloop|right; lia].
Qed.

Local Lemma resume_target_rank {A G} (prog : stmt A G) low k n v :
  Forall (fun f => is_loop_head prog (return_point f) = true \/
    low < point_rank prog (return_point f)) k -> resume_target n k = Some v ->
  is_loop_head prog v = true \/ low < point_rank prog v.
Proof.
  revert n; induction k as [|f k IH]; intros n Hall Htarget;
    rewrite resume_target_equation in Htarget; [discriminate|].
  inversion Hall as [|? ? Hhead Htail]; subst.
  rewrite return_point_equation in Hhead; destruct f; cbn [return_point] in Hhead;
    try (eapply IH; eassumption).
  all: destruct n; [inversion Htarget; subst; exact Hhead|eapply IH; eassumption].
Qed.

Local Lemma jump_out_after {A G} (prog : stmt A G) p k n
    (xs : list (skel_action A G)) v ys :
  context prog p k -> In (v, ys) (jump_out k p n xs) ->
  is_loop_head prog v = true \/ entry_rank prog p < point_rank prog v.
Proof.
  intro Hctx; rewrite jump_out_equation.
  destruct (resume_target n k) as [q|] eqn:Htarget; [|cbn; tauto].
  intros [Heq|Hbad]; [inversion Heq; subst|contradiction].
  eapply resume_target_rank; [eapply context_entry_continuations; exact Hctx|exact Htarget].
Qed.

Local Lemma table_out_after {A G} (prog : stmt A G) p k g ns i v
    (xs : list (skel_action A G)) :
  context prog p k -> In (v, xs) (table_out k p g ns i) ->
  is_loop_head prog v = true \/ entry_rank prog p < point_rank prog v.
Proof.
  intro Hctx; revert i; induction ns as [|n ns IH]; intros i Hin;
    rewrite table_out_equation in Hin; [contradiction|].
  apply in_app_or in Hin; destruct Hin as [Hin|Hin].
  - eapply jump_out_after; eassumption.
  - eapply IH; exact Hin.
Qed.

Local Lemma skel_out_after {A G} (prog : stmt A G) u v xs :
  point_valid prog u -> In (v, xs) (skel_out prog u) ->
  is_loop_head prog v = true \/ point_rank prog u < point_rank prog v.
Proof.
  intros Hvalid Hin; apply nodes_spec in Hvalid.
  destruct u as [p|p]; destruct Hvalid as [k Hctx]; cbn [skel_out] in Hin.
  - destruct (context_sub prog p k Hctx) as [s Hsub]; rewrite Hsub in Hin.
    rewrite entry_out_equation, (context_enclosing prog p k Hctx) in Hin.
    destruct s as [a|s1 s2|g s1 s2|s|s|n|g n|g ns n].
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; apply entry_before_exit; eexists; exact Hsub.
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; exact (proj1 (child_rank_bounds prog p _ DFirst s1 Hsub eq_refl)).
    + destruct Hin as [Heq|[Heq|Hfalse]]; try contradiction; inversion Heq; subst; right.
      * exact (proj1 (child_rank_bounds prog p _ DFirst s1 Hsub eq_refl)).
      * exact (proj1 (child_rank_bounds prog p _ DSecond s2 Hsub eq_refl)).
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      right; exact (proj1 (child_rank_bounds prog p _ DBody s Hsub eq_refl)).
    + destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
      left; eapply loop_body_head; exact Hsub.
    + eapply jump_out_after; eassumption.
    + apply in_app_or in Hin; destruct Hin as [Hin|[Heq|Hfalse]].
      * eapply jump_out_after; eassumption.
      * inversion Heq; subst; right; apply entry_before_exit; eexists; exact Hsub.
      * contradiction.
    + apply in_app_or in Hin; destruct Hin as [Hin|Hin].
      * eapply table_out_after; eassumption.
      * eapply jump_out_after; eassumption.
  - destruct (context_locate prog p k Hctx) as [s [Hloc _]]; rewrite Hloc in Hin.
    destruct k as [|f k]; [contradiction|].
    destruct Hin as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
    pose proof (context_continuations prog p (f :: k) Hctx) as Hall.
    inversion Hall; assumption.
Qed.

Local Lemma skeleton_edge_after {A G} (prog : stmt A G) e :
  point_valid prog (from e) ->
  In e (Graph.out (Cfg.graph (skeleton_cfg prog)) (from e)) ->
  is_loop_head prog (skel_to prog e) = true \/
    point_rank prog (from e) < point_rank prog (skel_to prog e).
Proof.
  intros Hvalid Hedge; apply skeleton_out_slot in Hedge; destruct Hedge as [_ Hbound].
  rewrite skel_to_agrees; destruct (nth_error (skel_out prog (from e)) (slot e))
    as [[v xs]|] eqn:Hnth.
  - eapply skel_out_after; [exact Hvalid|apply nth_error_In in Hnth; exact Hnth].
  - apply nth_error_None in Hnth; lia.
Qed.

Local Lemma skeleton_path_rank {A G} (prog : stmt A G) u es v :
  path (Cfg.graph (skeleton_cfg prog)) u es v -> point_valid prog u ->
  (forall e, In e es -> is_loop_head prog (skel_to prog e) = false) ->
  point_rank prog u <= point_rank prog v /\
    (es <> [] -> point_rank prog u < point_rank prog v).
Proof.
  intro Hpath; induction Hpath as [u|e es v Hedge Hpath IH]; intros Hvalid Htargets.
  - split; [lia|tauto].
  - assert (Hnext : point_valid prog (skel_to prog e)).
    { change (In (Graph.target (Cfg.graph (skeleton_cfg prog)) e)
        (Graph.nodes (Cfg.graph (skeleton_cfg prog)))).
      eapply out_target_in; [apply skeleton_graph_wf|exact Hvalid|exact Hedge]. }
    destruct (IH Hnext ltac:(intros a Ha; apply Htargets; right; exact Ha)) as [Hle _].
    destruct (skeleton_edge_after prog e Hvalid Hedge) as [Hloop|Hrank].
    + pose proof (Htargets e (or_introl eq_refl)); congruence.
    + change (point_rank prog (skel_to prog e) <= point_rank prog v) in Hle.
      change (point_rank prog (from e) <= point_rank prog v /\
        (e :: es <> [] -> point_rank prog (from e) < point_rank prog v)).
      split; [lia|intros _; lia].
Qed.

Local Lemma cached_path_rank {A G} (prog : stmt A G) u es v ru rv :
  path (Cfg.graph (skeleton_cfg prog)) u es v ->
  point_valid prog u -> point_valid prog v ->
  indexed_point_rank (skeleton_index prog) u = Some ru ->
  indexed_point_rank (skeleton_index prog) v = Some rv ->
  (forall e, In e es -> is_loop_head prog (skel_to prog e) = false) ->
  ru <= rv /\ (es <> [] -> ru < rv).
Proof.
  intros Hpath Hu Hv Hru Hrv Hheads.
  rewrite (cached_rank_agrees prog u Hu) in Hru; injection Hru as <-.
  rewrite (cached_rank_agrees prog v Hv) in Hrv; injection Hrv as <-.
  eapply skeleton_path_rank; eassumption.
Qed.

(** Every nonempty listed cycle of the indexed skeleton graph meets a loop head. *)
Theorem skeleton_cuts {A G} (prog : stmt A G) :
  cycles_cut (Cfg.graph (skeleton_cfg prog)) (fun v => is_loop_head prog v = true).
Proof.
  intros v es Hnode Hpath Hnonempty.
  destruct (is_loop_head prog v) eqn:Hstart; [left; reflexivity|].
  destruct (existsb (fun e => is_loop_head prog (skel_to prog e)) es) eqn:Hheads.
  - right; apply existsb_exists in Hheads; destruct Hheads as [e [Hin Hhead]].
    exists e; split; assumption.
  - assert (Htargets : forall e, In e es -> is_loop_head prog (skel_to prog e) = false).
    { intros e Hin; destruct (is_loop_head prog (skel_to prog e)) eqn:Hhead;
        [|reflexivity].
      assert (Hsome : existsb (fun e => is_loop_head prog (skel_to prog e)) es = true).
      { apply existsb_exists; exists e; split; assumption. }
      congruence. }
    destruct (skeleton_rank_present prog v Hnode) as [rank Hrank].
    destruct (cached_path_rank prog v es v rank rank Hpath Hnode Hnode Hrank Hrank Htargets)
      as [_ Hstrict].
    specialize (Hstrict Hnonempty); lia.
Qed.
