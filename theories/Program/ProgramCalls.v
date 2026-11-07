(** * Calls and resolver graphs

    Function inventories and resolvers compute without concrete call stacks.
    For example, recursion contributes a self-edge tagged by its call site.
    Builds on: ProgramSteps, BaseCode and GraphModel. *)

From Stdlib Require Import List NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps.
Import List.ListNotations Cost.Notations.

Module CallsLink.

(** Suspended callers are listed innermost first. *)
Record t (S F P : Type) := Make {
  here : S -> F;
  frames : S -> list (F * P)
}.
Arguments Make {S F P}.
Arguments here {S F P}.
Arguments frames {S F P}.

End CallsLink.

(** A call edge retains its call-site identity and resolved target. *)
Record call_edge (F P : Type) := CallEdge {
  edge_site : P;
  edge_callee : F
}.
Arguments CallEdge {F P}.
Arguments edge_site {F P}.
Arguments edge_callee {F P}.

Module Calls.

(** The inventory covers functions, roots, sites and every possible resolver target. *)
Record t (F P : Type) := Make {
  functions : list F;
  roots : list F;
  sites_of_c : F -> Cost.t (list P);
  caller_of_c : P -> Cost.t F;
  resolve_c : P -> Cost.t (list F);
  fn_enc : encoding F;
  site_enc : encoding P
}.
Arguments Make {F P}.
Arguments functions {F P}.
Arguments roots {F P}.
Arguments sites_of_c {F P}.
Arguments caller_of_c {F P}.
Arguments resolve_c {F P}.
Arguments fn_enc {F P}.
Arguments site_enc {F P}.

Definition sites_of {F P} (c : t F P) f := Cost.value (sites_of_c c f).
Definition caller_of {F P} (c : t F P) p := Cost.value (caller_of_c c p).
Definition resolve {F P} (c : t F P) p := Cost.value (resolve_c c p).

(** Pure inventory callbacks charge one primitive tick. *)
Definition of_pure {F P} functions roots sites caller resolve fe pe : t F P :=
  Make functions roots (Cost.lift (fun _ => 1%N) sites) (Cost.lift (fun _ => 1%N) caller)
    (Cost.lift (fun _ => 1%N) resolve) fe pe.

(** Active functions run from the current function to the outermost caller. *)
Definition active {S F P} (cl : CallsLink.t S F P) s :=
  CallsLink.here cl s :: map fst (CallsLink.frames cl s).

Definition out_c {F P} (c : t F P) f : Cost.t (list (call_edge F P)) :=
  Cost.step ;;
  let* ps := sites_of_c c f in
  fold_right_c (fun p rest =>
    Cost.step ;;
    let* targets := resolve_c c p in
    let* es := map_c (fun g => Cost.ret (CallEdge p g)) targets in
    app_c es rest) [] ps.

(** The graph retains resolver callback charges and endpoint primitives. *)
Definition graph {F P} (c : t F P) : Graph.t F (call_edge F P) :=
  Graph.Make (roots c) (functions c) (out_c c)
    (fun e => Cost.step ;; caller_of_c c (edge_site e))
    (fun e => Cost.ret (edge_callee e)).

(** Outgoing call edges preserve site order, target order and duplicate occurrences. *)
Theorem graph_out {F P} (c : t F P) f :
  Graph.out (graph c) f =
    flat_map (fun p => map (CallEdge p) (resolve c p)) (sites_of c f).
Proof.
  change (Cost.value (out_c c f) =
    flat_map (fun p => map (CallEdge p) (resolve c p)) (sites_of c f)).
  unfold out_c; autorewrite with galois_cost.
  fold (sites_of c f).
  induction (sites_of c f) as [|p ps IH]; cbn [fold_right flat_map].
  - reflexivity.
  - autorewrite with galois_cost; rewrite IH; reflexivity.
Qed.

(** The source of a call edge is the site's declared caller. *)
Theorem graph_source {F P} (c : t F P) e :
  Graph.source (graph c) e = caller_of c (edge_site e).
Proof.
  reflexivity.
Qed.

(** The target of a call edge is its tagged callee. *)
Theorem graph_target {F P} (c : t F P) e :
  Graph.target (graph c) e = edge_callee e.
Proof.
  reflexivity.
Qed.

Definition edge_key_c {F P} (c : t F P) (e : call_edge F P) :=
  Cost.step ;;
  let* p := encode_c (site_enc c) (edge_site e) in
  Cost.step ;;
  let* f := encode_c (fn_enc c) (edge_callee e) in
  Cost.ret (p, f).

(** Edge dictionaries reuse the costed component encodings through a pair pullback. *)
Definition edge_enc {F P} (c : t F P) : encoding (call_edge F P) :=
  encoding_comap (edge_key_c c) (codec_enc (pair_codec positive_codec positive_codec)).

(** Injective site and function dictionaries distinguish every call edge. *)
Theorem edge_enc_laws {F P} (c : t F P) :
  encoding_laws (site_enc c) -> encoding_laws (fn_enc c) -> encoding_laws (edge_enc c).
Proof.
  intros HP HF; apply encoding_comap_laws.
  - intros [p f] [q g] Heq.
    change ((encode (site_enc c) p, encode (fn_enc c) f) =
      (encode (site_enc c) q, encode (fn_enc c) g)) in Heq.
    inversion Heq as [[Hp Hf]].
    apply (encode_injective HP) in Hp; apply (encode_injective HF) in Hf.
    subst; reflexivity.
  - apply codec_laws_injective, pair_codec_laws; apply positive_codec_laws.
Qed.

Arguments graph {F P} c : simpl never.

End Calls.

(** Actual pushes, including callbacks, must be listed and resolved.
    Inventory and reachable-state clauses keep their legacy domains. *)
Record calls_laws {S O F P} (m : semantics S O) (c : Calls.t F P)
    (cl : CallsLink.t S F P) : Prop := {
  sites_caller : forall f p, In p (Calls.sites_of c f) -> Calls.caller_of c p = f;
  initial_roots : forall s, initial m s ->
    In (CallsLink.here cl s) (Calls.roots c) /\ CallsLink.frames cl s = [];
  frames_listed : forall s, reachable_state m s -> forall f, In f (Calls.active cl s) ->
    In f (Calls.functions c);
  step_shape : on_steps m (fun s _ s' =>
    (CallsLink.here cl s' = CallsLink.here cl s /\ CallsLink.frames cl s' = CallsLink.frames cl s)
    \/ (exists p, In p (Calls.sites_of c (CallsLink.here cl s)) /\
      In (CallsLink.here cl s') (Calls.resolve c p) /\
      CallsLink.frames cl s' = (CallsLink.here cl s, p) :: CallsLink.frames cl s)
    \/ (exists f p, CallsLink.frames cl s = (f, p) :: CallsLink.frames cl s' /\
      CallsLink.here cl s' = f))
}.
Arguments sites_caller {S O F P m c cl}.
Arguments initial_roots {S O F P m c cl}.
Arguments frames_listed {S O F P m c cl}.
Arguments step_shape {S O F P m c cl}.

(** A resolved site contributes its tagged target edge to the caller's outgoing list. *)
Theorem call_graph_edge {F P} (c : Calls.t F P) f p g :
  In p (Calls.sites_of c f) -> In g (Calls.resolve c p) ->
  In (CallEdge p g) (Graph.out (Calls.graph c) f).
Proof.
  intros Hsite Htarget; rewrite Calls.graph_out; apply in_flat_map.
  exists p; split; [exact Hsite|apply in_map; exact Htarget].
Qed.

(** A closed call inventory yields a well-formed call graph. *)
Theorem call_graph_wf {F P} (c : Calls.t F P) :
  NoDup (Calls.functions c) -> incl (Calls.roots c) (Calls.functions c) ->
  (forall f p, In p (Calls.sites_of c f) ->
    Calls.caller_of c p = f /\ In f (Calls.functions c)) ->
  (forall p g, In g (Calls.resolve c p) -> In g (Calls.functions c)) ->
  graph_wf (Calls.graph c).
Proof.
  intros Hnodes Hroots Hsites Hresolve; constructor.
  - exact Hnodes.
  - exact Hroots.
  - intros f e Hedge; rewrite Calls.graph_out in Hedge.
    apply in_flat_map in Hedge; destruct Hedge as [p [Hsite Hedge]].
    apply in_map_iff in Hedge; destruct Hedge as [g [<- Htarget]].
    rewrite Calls.graph_source; exact (proj1 (Hsites f p Hsite)).
  - intros f e Hf Hedge; rewrite Calls.graph_out in Hedge.
    apply in_flat_map in Hedge; destruct Hedge as [p [Hsite Hedge]].
    apply in_map_iff in Hedge; destruct Hedge as [g [<- Htarget]].
    rewrite Calls.graph_target; exact (Hresolve p g Htarget).
Qed.

(** Each suspended caller is linked to the callee directly above it by the resolver. *)
Fixpoint frames_linked {F P} (c : Calls.t F P) (callee : F) (stack : list (F * P)) : Prop :=
  match stack with
  | [] => True
  | (f, p) :: rest => Calls.caller_of c p = f /\ In p (Calls.sites_of c f) /\
      In callee (Calls.resolve c p) /\ frames_linked c f rest
  end.

(** Every reachable step preserves the resolver links of its suspended frames. *)
Theorem frames_linked_step {S O F P} (m : semantics S O) (c : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m c cl ->
  on_steps m (fun s _ s' =>
    frames_linked c (CallsLink.here cl s) (CallsLink.frames cl s) ->
    frames_linked c (CallsLink.here cl s') (CallsLink.frames cl s')).
Proof.
  intros Hlaws s l s' Hreachable Hstep Hlinked.
  destruct (step_shape Hlaws s l s' Hreachable Hstep) as
    [[Hhere Hframes]|[[p [Hsite [Htarget Hframes]]]|[f [p [Hframes Hhere]]]]].
  - rewrite Hhere, Hframes; exact Hlinked.
  - rewrite Hframes; cbn; split; [eapply sites_caller; eassumption|].
    split; [exact Hsite|split; assumption].
  - rewrite Hframes in Hlinked; cbn in Hlinked; rewrite Hhere.
    exact (proj2 (proj2 (proj2 Hlinked))).
Qed.

(** Reachable stacks retain the resolver links established by their pushes. *)
Theorem reachable_frames_linked {S O F P} (m : semantics S O) (c : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m c cl -> forall s, reachable_state m s ->
    frames_linked c (CallsLink.here cl s) (CallsLink.frames cl s).
Proof.
  intro Hlaws; apply reachable_ind.
  - intros s Hinitial; rewrite (proj2 (initial_roots Hlaws s Hinitial)); exact I.
  - intros s l s' Hreach HI Hstep.
    exact (frames_linked_step m c cl Hlaws s l s' Hreach Hstep HI).
Qed.

Local Lemma active_reachable_step {S O F P} (m : semantics S O) (c : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m c cl -> forall s l s', reachable_state m s -> step m s l s' ->
  (forall f, In f (Calls.active cl s) -> reachable (Calls.graph c) f) ->
  forall f, In f (Calls.active cl s') -> reachable (Calls.graph c) f.
Proof.
  intros Hlaws s l s' Hreachable Hstep Hactive f Hin.
  unfold Calls.active in Hin.
  destruct (step_shape Hlaws s l s' Hreachable Hstep) as
    [[Hhere Hframes]|[[p [Hsite [Htarget Hframes]]]|[g [p [Hframes Hhere]]]]].
  - rewrite Hhere, Hframes in Hin; apply Hactive; exact Hin.
  - rewrite Hframes in Hin; cbn in Hin; destruct Hin as [<-|Hin].
    + pose proof (sites_caller Hlaws _ _ Hsite) as Hcaller.
      change (reachable (Calls.graph c)
        (Graph.target (Calls.graph c) (CallEdge p (CallsLink.here cl s')))).
      apply GraphModel.reachable_step.
      * rewrite Calls.graph_source; cbn [edge_site]; rewrite Hcaller.
        apply Hactive; left; reflexivity.
      * rewrite Calls.graph_source; cbn [edge_site]; rewrite Hcaller.
        apply call_graph_edge; assumption.
    + apply Hactive; exact Hin.
  - rewrite Hhere in Hin; apply Hactive; unfold Calls.active; rewrite Hframes; cbn.
    right; exact Hin.
Qed.

(** Every function active in a reachable state is reachable from a call-graph root. *)
Theorem active_reachable_in_call_graph {S O F P} (m : semantics S O) (c : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m c cl ->
  forall s, reachable_state m s -> forall f, In f (Calls.active cl s) ->
    reachable (Calls.graph c) f.
Proof.
  intro Hlaws; apply (reachable_ind m (fun s =>
    forall f, In f (Calls.active cl s) -> reachable (Calls.graph c) f)).
  - intros s Hinitial f Hin; unfold Calls.active in Hin.
    destruct (initial_roots Hlaws s Hinitial) as [Hroot Hframes].
    rewrite Hframes in Hin; cbn in Hin; destruct Hin as [<-|[]].
    apply reachable_entry; exact Hroot.
  - intros s l s' Hreachable Hactive Hstep.
    eapply active_reachable_step; eassumption.
Qed.
