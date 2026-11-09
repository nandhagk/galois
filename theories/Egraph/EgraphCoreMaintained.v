(** * Maintained constructors and insertion

    Structural operation laws compose with concrete kernel coverage without changing computation.
    For example, term insertion carries both duties through every child graph it creates.
    Builds on: EgraphCoreStructural, EgraphCoreInvariant and EgraphCoreRepresentation. *)

From Stdlib Require Import List PArith Lia.
From Galois.Base Require Import BaseMap.
From Galois.Egraph Require Import
  EgraphSyntax EgraphGraph EgraphCoreRepresentation EgraphCoreStructural
  EgraphCoreInvariant EgraphCoreTransition EgraphCoreView.
Import List.ListNotations.

Module EggMaintained.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** Structural validity supplies the forest, Map and allocated-root premises of repair. *)
Theorem layout g :
  EggRepresentation.structural_wf a g -> EggTransition.layout a g.
Proof.
  intro Hwf; constructor.
  - exact (EggRepresentation.forest_wf a g Hwf).
  - exact (EggRepresentation.nodes_wf a g Hwf).
  - exact (EggRepresentation.memo_wf a g Hwf).
  - intros c n Hnode.
    apply (EggStructural.find_wf a g c (Egraph.node_sort n) Hwf).
    change (option_map Egraph.node_sort (Map.get Egraph.id_encoding c (Egraph.nodes g)) =
      Some (Egraph.node_sort n)); rewrite Hnode; reflexivity.
Qed.

(** The allocation pointer is absent from the node Map under structural validity. *)
Theorem fresh g :
  EggRepresentation.structural_wf a g ->
  Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g) = None.
Proof.
  intro Hwf.
  destruct (Map.get Egraph.id_encoding (Egraph.next g) (Egraph.nodes g))
    as [n|] eqn:Hnode; [|reflexivity].
  pose proof (proj1 (EggRepresentation.allocation a g Hwf (Egraph.next g))
    (ex_intro _ n Hnode)) as Hbound; lia.
Qed.

(** Empty construction satisfies both the original structural predicate and maintained coverage. *)
Theorem empty_wf : EggRepresentation.wf a (@Egraph.empty K Sort V).
Proof.
  constructor; [exact (EggStructural.empty_wf a)|exact (EggKernelInv.empty_kernel_inv a)].
Qed.

(** Public node insertion maintains coverage from actual forest and freshness duties. *)
Theorem add_node_kernel g n c h :
  EggRepresentation.structural_wf a g -> Egraph.kernel_inv a g ->
  Egraph.add_node a g n = Some (c, h) -> Egraph.kernel_inv a h.
Proof.
  intros Hwf Hkernel Hadded.
  exact (EggKernelInv.add_node_kernel_inv a g n c h Hkernel
    (EggRepresentation.forest_wf a g Hwf) (EggRepresentation.nodes_wf a g Hwf)
    (EggRepresentation.memo_wf a g Hwf) (fresh g Hwf) Hadded).
Qed.

(** Successful public insertion composes structural validity and maintained indexing. *)
Theorem add_node_wf g n c h :
  EggRepresentation.encoding_laws a -> EggRepresentation.wf a g ->
  Egraph.add_node a g n = Some (c, h) -> EggRepresentation.wf a h.
Proof.
  intros Hl Hwf Hadded; constructor.
  - exact (EggStructural.add_node_wf a g n c h Hl
      (EggRepresentation.wf_structural a g Hwf) Hadded).
  - exact (add_node_kernel g n c h (EggRepresentation.wf_structural a g Hwf)
      (EggRepresentation.wf_kernel a g Hwf) Hadded).
Qed.

(** Successful ordinary union maintains both predicates through its actual justified merge. *)
Theorem union_wf g c d h :
  EggRepresentation.encoding_laws a -> EggRepresentation.wf a g ->
  Egraph.union a g c d = Some h -> EggRepresentation.wf a h.
Proof.
  intros Hl Hwf Hunion.
  pose proof (EggRepresentation.wf_structural a g Hwf) as Hstruct.
  destruct (EggStructural.union_inv a g c d h Hl Hunion) as [s [Hc [Hd Hresult]]].
  constructor.
  - exact (EggStructural.union_wf a g c d h Hl Hstruct Hunion).
  - exact (EggKernelInv.union_j_kernel_inv a g c d Egraph.JGiven h
      (EggRepresentation.wf_kernel a g Hwf) (EggRepresentation.forest_wf a g Hstruct)
      (EggStructural.find_wf a g c s Hstruct Hc)
      (EggStructural.find_wf a g d s Hstruct Hd) Hunion).
Qed.

(** Successful annotated union maintains WF without adding semantics or proof inputs to runtime. *)
Theorem union_j_wf g c d reason h :
  EggRepresentation.encoding_laws a -> EggRepresentation.wf a g ->
  Egraph.union_j a g c d reason = Some h -> EggRepresentation.wf a h.
Proof.
  intros Hl Hwf Hunion.
  pose proof (EggRepresentation.wf_structural a g Hwf) as Hstruct.
  destruct (EggView.union_annotation a g c d reason h Hunion)
    as [given [Hgiven [Huf [Hnodes [Hmemo Hnext]]]]].
  pose proof (EggStructural.union_wf a g c d given Hl Hstruct Hgiven) as Hraw.
  destruct (EggStructural.union_inv a g c d given Hl Hgiven) as [s [Hc [Hd Hresult]]].
  assert (Hmemo_wf : Map.wf Egraph.id_encoding (Egraph.memo h)).
  { rewrite <- Hmemo; exact (EggRepresentation.memo_wf a given Hraw). }
  constructor.
  - exact (EggView.structural_transport a given h Hraw Huf Hnodes Hnext
      Hmemo_wf
      (EggView.memo_observation a given h Huf Hnodes Hmemo
        (EggRepresentation.memo_correct a given Hraw))).
  - exact (EggKernelInv.union_j_kernel_inv a g c d reason h
      (EggRepresentation.wf_kernel a g Hwf) (EggRepresentation.forest_wf a g Hstruct)
      (EggStructural.find_wf a g c s Hstruct Hc)
      (EggStructural.find_wf a g d s Hstruct Hd) Hunion).
Qed.

Section Terms.
Context (Hl : EggRepresentation.encoding_laws a).

Local Lemma terms_structural es :
  forall g cs h, EggRepresentation.structural_wf a g ->
  Egraph.add_terms a g es = Some (cs, h) -> EggRepresentation.structural_wf a h.
Proof.
  induction es as [|e es IH]; intros g cs h Hwf;
    rewrite EggStructural.add_terms_equation.
  - intro Heq; injection Heq as <- <-; exact Hwf.
  - destruct (Egraph.add_term a g e) as [[c j]|] eqn:Hchild; [|discriminate].
    destruct (proj1 (EggStructural.add_term_represents a g e Hl Hwf) c j Hchild)
      as [_ [Hj Hext]].
    destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Htail; [|discriminate].
    intro Heq; injection Heq as <- <-; exact (IH j ds k Hj Htail).
Qed.

Local Lemma terms_kernel es :
  Forall (fun e => forall g c h, EggRepresentation.structural_wf a g ->
    Egraph.kernel_inv a g -> Egraph.add_term a g e = Some (c, h) ->
    Egraph.kernel_inv a h) es ->
  forall g cs h, EggRepresentation.structural_wf a g -> Egraph.kernel_inv a g ->
    Egraph.add_terms a g es = Some (cs, h) -> Egraph.kernel_inv a h.
Proof.
  intro Hchildren; induction Hchildren as [|e es He Hrest IH]; intros g cs h Hwf Hkernel;
    rewrite EggStructural.add_terms_equation.
  - intro Heq; injection Heq as <- <-; exact Hkernel.
  - destruct (Egraph.add_term a g e) as [[c j]|] eqn:Hchild; [|discriminate].
    pose proof (He g c j Hwf Hkernel Hchild) as Hj_kernel.
    destruct (proj1 (EggStructural.add_term_represents a g e Hl Hwf) c j Hchild)
      as [_ [Hj Hext]].
    destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Htail; [|discriminate].
    intro Heq; injection Heq as <- <-; exact (IH j ds k Hj Hj_kernel Htail).
Qed.

(** Term insertion carries maintained coverage through the complete nested child traversal. *)
Theorem add_term_kernel :
  forall e g c h, EggRepresentation.structural_wf a g -> Egraph.kernel_inv a g ->
    Egraph.add_term a g e = Some (c, h) -> Egraph.kernel_inv a h.
Proof.
  apply (EggStructural.term_ind_all (fun e => forall g c h,
    EggRepresentation.structural_wf a g -> Egraph.kernel_inv a g ->
    Egraph.add_term a g e = Some (c, h) -> Egraph.kernel_inv a h)).
  - intros s v g c h Hwf Hkernel; rewrite EggStructural.add_term_equation.
    exact (add_node_kernel g (Egraph.NVar s v) c h Hwf Hkernel).
  - intros s op es IH g c h Hwf Hkernel; rewrite EggStructural.add_term_equation.
    destruct (Egraph.add_terms a g es) as [[cs j]|] eqn:Hchildren; [|discriminate].
    intro Hadded.
    exact (add_node_kernel j (Egraph.NApp s op cs) c h
      (terms_structural es g cs j Hwf Hchildren)
      (terms_kernel es IH g cs j Hwf Hkernel Hchildren) Hadded).
Qed.

End Terms.

(** Successful public term insertion maintains the complete WF domain. *)
Theorem add_term_wf g e c h :
  EggRepresentation.encoding_laws a -> EggRepresentation.wf a g ->
  Egraph.add_term a g e = Some (c, h) -> EggRepresentation.wf a h.
Proof.
  intros Hl Hwf Hadded.
  pose proof (EggRepresentation.wf_structural a g Hwf) as Hstruct.
  destruct (proj1 (EggStructural.add_term_represents a g e Hl Hstruct) c h Hadded)
    as [_ [Hnew Hext]].
  constructor; [exact Hnew|].
  exact (add_term_kernel Hl e g c h Hstruct (EggRepresentation.wf_kernel a g Hwf) Hadded).
Qed.

End Graph.

End EggMaintained.
