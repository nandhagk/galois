(** * Public e-graph predicates and operation laws

    Predicate views retain one grammar owner and keep maintained WF separate from raw validity.
    For example, public term insertion returns maintained coverage as well as a finite witness.
    Builds on: EgraphCoreRepresentation, EgraphCoreStructural and EgraphCoreMaintained. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphCoreRepresentation
  EgraphCoreStructural EgraphCoreMaintained EgraphCoreView EgraphCoreRebuildSemantic.

Module EggSpec.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** The public encoding-law record is the single representation owner's original contract. *)
Definition encoding_laws := EggRepresentation.encoding_laws a.
Definition Encoding_laws := @EggRepresentation.Encoding_laws K Sort V a.
Definition op_encoding := @EggRepresentation.op_encoding K Sort V a.
Definition sort_encoding := @EggRepresentation.sort_encoding K Sort V a.
Definition var_encoding := @EggRepresentation.var_encoding K Sort V a.

Definition nodes_get := @EggRepresentation.nodes_get K Sort V.

(** Public representation is the same finite inductive grammar used by all semantic proofs. *)
Definition represents := EggRepresentation.represents a.
Definition rep_var := @EggRepresentation.rep_var K Sort V a.
Definition rep_app := @EggRepresentation.rep_app K Sort V a.
Definition represents_ind := @EggRepresentation.represents_ind K Sort V a.

(** Class, typing and historical memo predicates retain their original semantic clauses. *)
Definition same_class := EggRepresentation.same_class a.
Definition node_typed := EggRepresentation.node_typed a.
Definition memo_sound := EggRepresentation.memo_sound a.

(** Raw validity remains available independently of maintained indexing. *)
Definition structural_wf := EggRepresentation.structural_wf a.
Definition Structural_wf := @EggRepresentation.Structural_wf K Sort V a.

(** Public WF requires both raw structural validity and maintained local kernel coverage. *)
Definition wf := EggRepresentation.wf a.
Definition Wf := @EggRepresentation.Wf K Sort V a.
Definition wf_structural := @EggRepresentation.wf_structural K Sort V a.
Definition wf_kernel := @EggRepresentation.wf_kernel K Sort V a.

Definition forest_wf g (Hwf : wf g) :=
  EggRepresentation.forest_wf a g (wf_structural g Hwf).
Definition nodes_wf g (Hwf : wf g) :=
  EggRepresentation.nodes_wf a g (wf_structural g Hwf).
Definition memo_wf g (Hwf : wf g) :=
  EggRepresentation.memo_wf a g (wf_structural g Hwf).
Definition allocation g (Hwf : wf g) :=
  EggRepresentation.allocation a g (wf_structural g Hwf).
Definition forest_domain g (Hwf : wf g) :=
  EggRepresentation.forest_domain a g (wf_structural g Hwf).
Definition class_sorts g (Hwf : wf g) :=
  EggRepresentation.class_sorts a g (wf_structural g Hwf).
Definition nodes_typed g (Hwf : wf g) :=
  EggRepresentation.nodes_typed a g (wf_structural g Hwf).
Definition finite_witness g (Hwf : wf g) :=
  EggRepresentation.finite_witness a g (wf_structural g Hwf).
Definition memo_correct g (Hwf : wf g) :=
  EggRepresentation.memo_correct a g (wf_structural g Hwf).

(** Cleanliness still requires congruence closure and current sound complete memo indexing. *)
Definition clean := EggRepresentation.clean a.
Definition Clean := @EggRepresentation.Clean K Sort V a.
Definition clean_wf := @EggRepresentation.clean_wf K Sort V a.
Definition congruence_closed := @EggRepresentation.congruence_closed K Sort V a.
Definition memo_current := @EggRepresentation.memo_current K Sort V a.
Definition memo_complete := @EggRepresentation.memo_complete K Sort V a.

(** Soundness retains the original models, facts, rules and finite represented-term pairs. *)
Definition sound {H F C} (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) g := EggRepresentation.sound a adm facts rules g.

Definition same_class_equal := EggRepresentation.same_class_equal a.
Definition node_represents := EggRepresentation.node_represents a.
Definition node_rep_var := @EggRepresentation.node_rep_var K Sort V a.
Definition node_rep_app := @EggRepresentation.node_rep_app K Sort V a.
Definition node_represents_ind := @EggRepresentation.node_represents_ind K Sort V a.
Definition extends := EggRepresentation.extends a.

(** Memo serialization remains injective under the original algebra encoding laws. *)
Theorem node_code_injective :
  encoding_laws -> forall n m, Egraph.node_code a n = Egraph.node_code a m -> n = m.
Proof.
  exact (EggStructural.node_code_injective a).
Qed.

(** Representation is unchanged by querying another identifier in the same class. *)
Theorem represents_same g c d e :
  same_class g c d -> represents g c e -> represents g d e.
Proof.
  exact (EggStructural.represents_same a g c d e).
Qed.

(** Find remains idempotent under public maintained WF. *)
Theorem find_idem g c :
  wf g -> Egraph.find a g (Egraph.find a g c) = Egraph.find a g c.
Proof.
  intro Hwf; exact (EggStructural.find_idem a g c (wf_structural g Hwf)).
Qed.

(** Find's allocation bound still requires a successful sort lookup. *)
Theorem find_wf g c s :
  wf g -> Egraph.sort_of a g c = Some s ->
  (Egraph.find a g c < Egraph.next g)%positive.
Proof.
  intro Hwf; exact (EggStructural.find_wf a g c s (wf_structural g Hwf)).
Qed.

(** Finite representations remain restricted to allocated classes. *)
Theorem represents_allocated g c e :
  wf g -> represents g c e -> (c < Egraph.next g)%positive.
Proof.
  intro Hwf; exact (EggStructural.represents_allocated a g c e (wf_structural g Hwf)).
Qed.

(** A represented term retains the sort of its allocated class identifier. *)
Theorem represents_sort g c e :
  wf g -> represents g c e -> Egraph.sort_of a g c = Some (EggTerm.sort_of e).
Proof.
  intro Hwf; exact (EggStructural.represents_sort a g c e (wf_structural g Hwf)).
Qed.

(** Every finite represented term is well typed under maintained WF. *)
Theorem represents_typed g :
  wf g -> forall c e, represents g c e -> EggTerm.typed a e.
Proof.
  intro Hwf; exact (EggStructural.represents_typed a g (wf_structural g Hwf)).
Qed.

(** Empty construction establishes all structural and maintained duties without client key laws. *)
Theorem empty_wf : wf (@Egraph.empty K Sort V).
Proof.
  exact (EggMaintained.empty_wf a).
Qed.

(** The empty graph has no congruence obligations and a current complete empty memo. *)
Theorem empty_clean : clean (@Egraph.empty K Sort V).
Proof.
  exact (EggStructural.empty_clean a).
Qed.

(** Successful union preserves every old finite term and every old class equality. *)
Theorem union_preserves g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h ->
  (forall x e, represents g x e -> represents h x e) /\
  (forall x y, same_class g x y -> same_class h x y).
Proof.
  intros Hl Hwf; exact (EggStructural.union_preserves a g c d h Hl (wf_structural g Hwf)).
Qed.

(** Successful union identifies its two allocated inputs. *)
Theorem union_same g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h -> same_class h c d.
Proof.
  intros Hl Hwf; exact (EggStructural.union_same a g c d h Hl (wf_structural g Hwf)).
Qed.

(** Successful union preserves the complete public maintained WF domain. *)
Theorem union_wf g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h -> wf h.
Proof.
  exact (EggMaintained.union_wf a g c d h).
Qed.

(** Annotated union preserves the same maintained domain as ordinary union. *)
Theorem union_j_wf g c d reason h :
  encoding_laws -> wf g -> Egraph.union_j a g c d reason = Some h -> wf h.
Proof.
  exact (EggMaintained.union_j_wf a g c d reason h).
Qed.

(** Every successful annotated union retains an explanation forest. *)
Theorem edges_forest g c d reason h :
  encoding_laws -> wf g -> Egraph.union_j a g c d reason = Some h ->
  Egraph.explanation_forest (Egraph.edges h).
Proof.
  intros Hl Hwf Hunion.
  exact (Egraph.reasons_forest a h (wf_kernel h (union_j_wf g c d reason h Hl Hwf Hunion))).
Qed.

(** Genuine old cross-class equality and old soundness still justify union soundness. *)
Theorem union_sound {H F C} (adm : EggSem.t K V C -> Prop)
    (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)) g c d h :
  encoding_laws -> wf g -> sound adm facts rules g ->
  (forall t u, represents g c t -> represents g d u -> EggEqual.rel a adm facts rules t u) ->
  Egraph.union a g c d = Some h -> sound adm facts rules h.
Proof.
  intros Hl Hwf.
  exact (EggStructural.union_sound a adm facts rules g c d h Hl (wf_structural g Hwf)).
Qed.

(** Annotated union soundness still requires a genuine cross-class equality justification. *)
Theorem union_j_sound {H F C} (adm : EggSem.t K V C -> Prop)
    (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F))
    g c d reason h :
  encoding_laws -> wf g -> sound adm facts rules g ->
  (forall t u, represents g c t -> represents g d u -> EggEqual.rel a adm facts rules t u) ->
  Egraph.union_j a g c d reason = Some h -> sound adm facts rules h.
Proof.
  intros Hl Hwf Hsound Hjoin Hunion.
  destruct (EggView.union_annotation a g c d reason h Hunion)
    as [given [Hgiven [Huf [Hnodes Hrest]]]].
  exact (EggView.sound_observation a adm facts rules given h Huf Hnodes
    (EggStructural.union_sound a adm facts rules g c d given Hl
      (wf_structural g Hwf) Hsound Hjoin Hgiven)).
Qed.

(** Successful node insertion preserves structural validity and maintained kernel indexing. *)
Theorem add_node_wf g n c h :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) -> wf h.
Proof.
  exact (EggMaintained.add_node_wf a g n c h).
Qed.

(** Successful node insertion preserves every old finite representation and class equality. *)
Theorem add_node_preserves g n c h :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) ->
  (forall d e, represents g d e -> represents h d e) /\
  (forall d e, same_class g d e -> same_class h d e).
Proof.
  intros Hl Hwf; exact (EggStructural.add_node_preserves a g n c h Hl (wf_structural g Hwf)).
Qed.

(** Successful insertion represents every finite term supplied by the input node's child classes. *)
Theorem add_node_represents g n c h e :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) ->
  node_represents g n e -> represents h c e.
Proof.
  intros Hl Hwf; exact (EggStructural.add_node_represents a g n c h e Hl (wf_structural g Hwf)).
Qed.

(** Clean insertion still reuses the existing class without changing the graph value. *)
Theorem add_node_hashcons g n i m c h :
  encoding_laws -> clean g -> node_typed g n -> nodes_get g i = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.add_node a g n = Some (c, h) -> h = g /\ same_class g c i.
Proof.
  exact (EggStructural.add_node_hashcons a g n i m c h).
Qed.

(** Successful term insertion represents its input and preserves maintained WF and old meanings. *)
Theorem add_term_represents g e :
  encoding_laws -> wf g ->
  (forall c h, Egraph.add_term a g e = Some (c, h) ->
    represents h c e /\ wf h /\ extends g h) /\
  (EggTerm.typed a e -> exists c h, Egraph.add_term a g e = Some (c, h)).
Proof.
  intros Hl Hwf.
  destruct (EggStructural.add_term_represents a g e Hl (wf_structural g Hwf))
    as [Hsuccess Htotal].
  split; [|exact Htotal]; intros c h Hadded.
  destruct (Hsuccess c h Hadded) as [Hrep [Hstruct Hext]].
  split; [exact Hrep|]; split; [|exact Hext].
  exact (EggMaintained.add_term_wf a g e c h Hl Hwf Hadded).
Qed.

(** Rebuilding restores the original clean condition under the maintained WF boundary. *)
Theorem rebuild_clean g :
  encoding_laws -> wf g -> clean (Egraph.rebuild a g).
Proof.
  intro Hl; exact (EggRebuildSem.rebuild_clean a Hl g).
Qed.

(** Rebuilding preserves every old finite term and class equality. *)
Theorem rebuild_preserves g :
  encoding_laws -> wf g -> extends g (Egraph.rebuild a g).
Proof.
  intro Hl; exact (EggRebuildSem.rebuild_preserves a Hl g).
Qed.

(** Rebuilding preserves old generated-equality soundness without a new rule-soundness premise. *)
Theorem rebuild_sound {H F C} (adm : EggSem.t K V C -> Prop)
    (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)) g :
  encoding_laws -> wf g -> sound adm facts rules g ->
  sound adm facts rules (Egraph.rebuild a g).
Proof.
  intro Hl; exact (EggRebuildSem.rebuild_sound a Hl adm facts rules g).
Qed.

(** Maintained rebuilding leaves no dirty class scheduled. *)
Theorem rebuild_dirty_empty g :
  encoding_laws -> wf g -> Egraph.dirty (Egraph.rebuild a g) = nil.
Proof.
  intro Hl; exact (EggRebuildSem.rebuild_dirty_empty a Hl g).
Qed.

(** Rebuilding a clean graph retains every class equality, including unknown singleton keys. *)
Theorem rebuild_idle g :
  encoding_laws -> clean g -> same_class_equal g (Egraph.rebuild a g).
Proof.
  intro Hl; exact (EggRebuildSem.rebuild_idle a Hl g).
Qed.

End Graph.

End EggSpec.
