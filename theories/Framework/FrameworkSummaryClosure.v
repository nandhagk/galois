(** * Prepared call-graph closure

    The reference Floyd preparation computes exactly graph reachability on listed callers.
    For example, a recursive caller belongs to its own reachable set.
    Builds on: FrameworkSummarySound and GraphModel. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCalls.
From Galois.Framework Require Import FrameworkSummary FrameworkSummarySound.
Import List.ListNotations Cost.Notations.

Module SummaryClosure.

(** Routes admit exactly the supplied intermediate vertices. *)
Inductive route {V E} (G : Graph.t V E) (via : list V) : V -> V -> Prop :=
  | route_refl f : route G via f f
  | route_edge e : In e (Graph.out G (Graph.source G e)) ->
      route G via (Graph.source G e) (Graph.target G e)
  | route_join f p g : In p via ->
      route G via f p -> route G via p g -> route G via f g.

Local Lemma route_mono {V E} (G : Graph.t V E) xs ys :
  incl xs ys -> forall f g, route G xs f g -> route G ys f g.
Proof.
  intros Hin f g Hroute; induction Hroute; econstructor; eauto.
Qed.

Local Lemma route_nil {V E} (G : Graph.t V E) f g :
  route G [] f g <->
    f = g \/ exists e, Graph.source G e = f /\ Graph.target G e = g /\
      In e (Graph.out G f).
Proof.
  split.
  - intro Hroute; inversion Hroute; subst; [now left|right; eexists; eauto|contradiction].
  - intros [->|[e [<- [<- He]]]]; constructor; assumption.
Qed.

Local Lemma route_cons {V E} (G : Graph.t V E) p via f g :
  route G (p :: via) f g <->
    route G via f g \/ (route G via f p /\ route G via p g).
Proof.
  split.
  - intro Hroute; induction Hroute as
      [f|e He|f q g Hq Hleft IHleft Hright IHright].
    + left; constructor.
    + left; now constructor.
    + destruct Hq as [<-|Hq].
      * right; split.
        -- destruct IHleft as [Hfp|[Hfp _]]; exact Hfp.
        -- destruct IHright as [Hpg|[_ Hpg]]; exact Hpg.
      * destruct IHleft as [Hfq|[Hfp Hpq]];
          destruct IHright as [Hqg|[Hqp Hpg]].
        -- left; eapply route_join; eassumption.
        -- right; split; [eapply route_join; eassumption|exact Hpg].
        -- right; split; [exact Hfp|eapply route_join; eassumption].
        -- right; auto.
  - intros [Hroute|[Hfp Hpg]].
    + eapply route_mono; [|exact Hroute]; intros x Hx; now right.
    + eapply route_join with (p := p).
      * left; reflexivity.
      * eapply route_mono; [|exact Hfp]; intros x Hx; now right.
      * eapply route_mono; [|exact Hpg]; intros x Hx; now right.
Qed.

Local Lemma path_app {V E} (G : Graph.t V E) f es p gs g :
  path G f es p -> path G p gs g -> path G f (es ++ gs) g.
Proof.
  intros Hpath; induction Hpath as [f|e es p He Hpath IH]; intro Htail; cbn.
  - exact Htail.
  - constructor; [exact He|apply IH; exact Htail].
Qed.

Local Lemma route_sound {V E} (G : Graph.t V E) via f g :
  route G via f g -> reaches G f g.
Proof.
  intro Hroute; induction Hroute as [f|e He|f p g Hp Hfp [es Hleft] Hpg [gs Hright]].
  - exists []; constructor.
  - exists [e]; constructor; [exact He|constructor].
  - exists (es ++ gs); eapply path_app; eassumption.
Qed.

Local Lemma route_complete {V E} (G : Graph.t V E) f es g :
  graph_wf G -> path G f es g -> In f (Graph.nodes G) ->
  route G (Graph.nodes G) f g.
Proof.
  intros Hwf Hpath; induction Hpath as [f|e es g He Hpath IH]; intro Hf.
  - constructor.
  - pose proof (out_target_in Hwf _ _ Hf He) as Htarget.
    eapply route_join; [exact Htarget|now constructor|apply IH; exact Htarget].
Qed.

(** A matrix row is the prepared reachable set or the empty set for an absent caller. *)
Definition row {F P} (C : Calls.t F P) (m : Map.t F (FinSet.t F)) f :=
  Map.find_or (Calls.fn_enc C) FinSet.empty f m.

Local Definition seed {F P} (C : Calls.t F P) f :=
  FinSet.of_list (Calls.fn_enc C)
    (f :: map edge_callee (Graph.out (Calls.graph C) f)).

Local Definition advance {F P} (C : Calls.t F P) m p :=
  Map.of_list (Calls.fn_enc C) (map (fun f =>
    (f, if FinSet.mem (Calls.fn_enc C) p (row C m f)
        then FinSet.union (row C m f) (row C m p)
        else row C m f)) (Calls.functions C)).

Local Lemma fold_agrees {X Y} (f g : Y -> X -> Y) xs acc :
  (forall acc x, f acc x = g acc x) ->
  fold_left f xs acc = fold_left g xs acc.
Proof.
  intro Hagree; revert acc; induction xs as [|x xs IH]; intro acc; cbn.
  - reflexivity.
  - rewrite Hagree; apply IH.
Qed.

(** The charged implementation agrees with Floyd's row-update recurrence. *)
Theorem closure_equation {F P} (C : Calls.t F P) :
  Cost.value (Summary.closure_c C) =
    fold_left (advance C) (Calls.functions C)
      (Map.of_list (Calls.fn_enc C) (map (fun f => (f, seed C f)) (Calls.functions C))).
Proof.
  unfold Summary.closure_c; autorewrite with galois_cost.
  etransitivity.
  - apply (fold_agrees _ (advance C)).
    intros m p; autorewrite with galois_cost.
    unfold advance, Summary.reach_get_c, row; autorewrite with galois_cost.
    apply (f_equal (Map.of_list (Calls.fn_enc C))); apply map_ext; intro f.
    autorewrite with galois_cost.
    change ((f, Cost.value (if FinSet.mem (Calls.fn_enc C) p (row C m f)
      then FinSet.union_c (row C m f) (row C m p) else Cost.ret (row C m f))) =
      (f, if FinSet.mem (Calls.fn_enc C) p (row C m f)
        then FinSet.union (row C m f) (row C m p) else row C m f)).
    destruct (FinSet.mem (Calls.fn_enc C) p (row C m f)); reflexivity.
  - apply (f_equal (fold_left (advance C) (Calls.functions C))).
    apply (f_equal (Map.of_list (Calls.fn_enc C))); apply map_ext; intro f.
    autorewrite with galois_cost.
    reflexivity.
Qed.

Local Lemma row_table {F P} (C : Calls.t F P) (HE : encoding_laws (Calls.fn_enc C))
    (f : F -> FinSet.t F) x :
  In x (Calls.functions C) ->
  row C (Map.of_list (Calls.fn_enc C)
    (map (fun y => (y, f y)) (Calls.functions C))) x = f x.
Proof.
  intro Hx; unfold row; rewrite Map.find_or_equation, (SummarySound.table_lookup _ HE);
    [reflexivity|exact Hx].
Qed.

Local Lemma seed_spec {F P} (C : Calls.t F P) (HE : encoding_laws (Calls.fn_enc C)) f g :
  graph_wf (Calls.graph C) ->
  FinSet.mem (Calls.fn_enc C) g (seed C f) = true <->
    route (Calls.graph C) [] f g.
Proof.
  intro Hwf; unfold seed; rewrite FinSet.mem_of_list, existsb_exists, route_nil.
  split.
  - intros [h [Hh Heq]]; apply (eqb_true_iff _ HE) in Heq; subst h.
    destruct Hh as [<-|Hh]; [now left|].
    apply in_map_iff in Hh; destruct Hh as [e [Heq He]].
    right; exists e; split; [exact (out_source Hwf f e He)|].
    split; [rewrite Calls.graph_target; exact Heq|exact He].
  - intros [<-|[e [Hs [Ht He]]]].
    + exists f; split; [now left|apply eqb_refl].
    + exists g; split; [right|apply eqb_refl].
      apply in_map_iff; exists e; split; [rewrite <- Ht, Calls.graph_target; reflexivity|exact He].
Qed.

(** A matrix stores well-formed sets for exactly the permitted intermediate routes. *)
Definition matrix {F P} (C : Calls.t F P) via m :=
  forall f, In f (Calls.functions C) ->
    FinSet.wf (Calls.fn_enc C) (row C m f) /\
    forall g, FinSet.mem (Calls.fn_enc C) g (row C m f) = true <->
      route (Calls.graph C) via f g.

Local Lemma seed_matrix {F P} (C : Calls.t F P) (HE : encoding_laws (Calls.fn_enc C)) :
  graph_wf (Calls.graph C) ->
  matrix C [] (Map.of_list (Calls.fn_enc C)
    (map (fun f => (f, seed C f)) (Calls.functions C))).
Proof.
  intros Hwf f Hf; rewrite (row_table C HE _ f Hf); split.
  - apply FinSet.wf_of_list.
  - intro g; apply seed_spec; assumption.
Qed.

Local Lemma advance_matrix {F P} (C : Calls.t F P)
    (HE : encoding_laws (Calls.fn_enc C)) via m p :
  In p (Calls.functions C) -> matrix C via m -> matrix C (p :: via) (advance C m p).
Proof.
  intros Hp Hmatrix f Hf; unfold advance; rewrite (row_table C HE _ f Hf).
  destruct (Hmatrix f Hf) as [Hfw Hfs].
  destruct (Hmatrix p Hp) as [Hpw Hps].
  destruct (FinSet.mem (Calls.fn_enc C) p (row C m f)) eqn:Hfp; split.
  - apply FinSet.wf_union; assumption.
  - intro g; rewrite FinSet.mem_union by assumption.
    rewrite orb_true_iff, route_cons, <- Hfs, <- Hps, <- Hfs, Hfp; tauto.
  - exact Hfw.
  - intro g; rewrite route_cons, <- Hfs, <- Hps, <- Hfs, Hfp; intuition discriminate.
Qed.

Local Lemma fold_matrix {F P} (C : Calls.t F P) (HE : encoding_laws (Calls.fn_enc C))
    todo via m :
  incl todo (Calls.functions C) -> matrix C via m ->
  matrix C (rev todo ++ via) (fold_left (advance C) todo m).
Proof.
  revert via m; induction todo as [|p todo IH]; intros via m Htodo Hmatrix.
  - exact Hmatrix.
  - cbn [rev fold_left]; rewrite <- app_assoc; cbn [app].
    apply IH.
    + intros f Hf; apply Htodo; now right.
    + apply advance_matrix; [exact HE|apply Htodo; now left|exact Hmatrix].
Qed.

(** The actual prepared closure is well formed and equals graph reachability at listed callers. *)
Theorem closure_exact {F P} (C : Calls.t F P) f :
  encoding_laws (Calls.fn_enc C) -> graph_wf (Calls.graph C) ->
  In f (Calls.functions C) ->
  FinSet.wf (Calls.fn_enc C) (row C (Cost.value (Summary.closure_c C)) f) /\
  forall g, FinSet.mem (Calls.fn_enc C) g
    (row C (Cost.value (Summary.closure_c C)) f) = true <-> reaches (Calls.graph C) f g.
Proof.
  intros HE Hwf Hf; rewrite closure_equation.
  pose proof (fold_matrix C HE (Calls.functions C) [] _
    (incl_refl _) (seed_matrix C HE Hwf)) as Hmatrix.
  rewrite app_nil_r in Hmatrix.
  destruct (Hmatrix f Hf) as [Hfw Hroute]; split; [exact Hfw|intro g; rewrite Hroute; split].
  - apply route_sound.
  - intros [es Hpath]; eapply route_mono with (xs := Calls.functions C).
    + intros p Hp; apply (proj1 (in_rev (Calls.functions C) p)); exact Hp.
    + exact (route_complete (Calls.graph C) f es g Hwf Hpath Hf).
Qed.

Local Lemma reaches_trans {V E} (G : Graph.t V E) f p g :
  reaches G f p -> reaches G p g -> reaches G f g.
Proof.
  intros [es Hleft] [gs Hright]; exists (es ++ gs); eapply path_app; eassumption.
Qed.

Local Lemma size_strict {X} (EX : encoding X) (HE : encoding_laws EX) (s t : FinSet.t X) x :
  FinSet.wf EX s -> FinSet.wf EX t ->
  (forall y, FinSet.mem EX y s = true -> FinSet.mem EX y t = true) ->
  FinSet.mem EX x t = true -> FinSet.mem EX x s = false ->
  FinSet.size s < FinSet.size t.
Proof.
  intros Hs Ht Hsub Hxt Hxs; rewrite !FinSet.size_elements.
  assert (Hnot : ~ In x (FinSet.elements s)).
  { intro Hin; apply (FinSet.elements_spec EX HE _ _ Hs) in Hin; congruence. }
  assert (Hincl : incl (x :: FinSet.elements s) (FinSet.elements t)).
  { intros y [<-|Hy]; apply (FinSet.elements_spec EX HE _ _ Ht); [exact Hxt|].
    apply Hsub; apply (FinSet.elements_spec EX HE _ _ Hs); exact Hy. }
  pose proof (NoDup_incl_length
    ltac:(constructor; [exact Hnot|exact (FinSet.elements_nodup EX s Hs)]) Hincl) as Hlen.
  cbn in Hlen; lia.
Qed.

(** A strict call-reachability edge strictly decreases the prepared reachable-set size. *)
Theorem closure_size_order {F P} (C : Calls.t F P) f g :
  encoding_laws (Calls.fn_enc C) -> graph_wf (Calls.graph C) ->
  In f (Calls.functions C) -> In g (Calls.functions C) ->
  reaches (Calls.graph C) f g -> ~ reaches (Calls.graph C) g f ->
  FinSet.size (row C (Cost.value (Summary.closure_c C)) g) <
    FinSet.size (row C (Cost.value (Summary.closure_c C)) f).
Proof.
  intros HE Hwf Hf Hg Hfg Hnot.
  destruct (closure_exact C f HE Hwf Hf) as [Hfw Hfs].
  destruct (closure_exact C g HE Hwf Hg) as [Hgw Hgs].
  apply (size_strict (Calls.fn_enc C) HE _ _ f Hgw Hfw).
  - intros y Hy; apply Hfs; eapply reaches_trans; [exact Hfg|apply Hgs; exact Hy].
  - apply Hfs; exists []; constructor.
  - destruct (FinSet.mem (Calls.fn_enc C) f
      (row C (Cost.value (Summary.closure_c C)) g)) eqn:Hmem; [|reflexivity].
    exfalso; apply Hnot, Hgs, Hmem.
Qed.

End SummaryClosure.
