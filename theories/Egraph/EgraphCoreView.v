(** * Semantic transport across metadata-only updates

    Finite representations depend on the forest and stored productions.
    For example, replacing a memo entry or queue flag does not change the represented terms.
    Builds on: EgraphCoreRepresentation, EgraphCoreStructural and EgraphGraph. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphCoreRepresentation
  EgraphCoreStructural EgraphCoreTransition.

Module EggView.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** Equal backing forests yield equal public representative observations. *)
Theorem find_observation g h :
  Egraph.uf g = Egraph.uf h -> forall c, Egraph.find a g c = Egraph.find a h c.
Proof.
  intros Huf c; unfold Egraph.find, Egraph.find_c; rewrite Huf; reflexivity.
Qed.

(** Equal backing node Maps yield equal public sort observations. *)
Theorem sort_observation g h :
  Egraph.nodes g = Egraph.nodes h -> forall c, Egraph.sort_of a g c = Egraph.sort_of a h c.
Proof.
  intros Hnodes c; unfold Egraph.sort_of, Egraph.sort_of_c; rewrite Hnodes; reflexivity.
Qed.

(** Equal forests retain every canonical node observation. *)
Theorem canonical_observation g h :
  Egraph.uf g = Egraph.uf h ->
  forall n, Egraph.canonical a g n = Egraph.canonical a h n.
Proof.
  intros Huf [s v|s op cs]; rewrite !Egraph.canonical_equation; [reflexivity|].
  f_equal; apply map_ext; exact (find_observation g h Huf).
Qed.

(** Equal representative observations retain canonical syntax across different forest data. *)
Theorem canonical_representatives g h :
  (forall c, Egraph.find a g c = Egraph.find a h c) ->
  forall n, Egraph.canonical a g n = Egraph.canonical a h n.
Proof.
  intros Hfind [s v|s op cs]; rewrite !Egraph.canonical_equation; [reflexivity|].
  f_equal; apply map_ext; exact Hfind.
Qed.

(** Equal forests and stored productions give the same finite grammar at every identifier. *)
Theorem represents_observation g h c e :
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  (EggRepresentation.represents a g c e <-> EggRepresentation.represents a h c e).
Proof.
  intros Huf Hnodes; split.
  - apply (EggStructural.represents_mono a g h).
    + intros i n Hnode; unfold EggRepresentation.nodes_get in *; rewrite <- Hnodes; exact Hnode.
    + intros x y Hsame; unfold EggRepresentation.same_class in *.
      rewrite <- (find_observation g h Huf x), <- (find_observation g h Huf y); exact Hsame.
  - apply (EggStructural.represents_mono a h g).
    + intros i n Hnode; unfold EggRepresentation.nodes_get in *; rewrite Hnodes; exact Hnode.
    + intros x y Hsame; unfold EggRepresentation.same_class in *.
      rewrite (find_observation g h Huf x), (find_observation g h Huf y); exact Hsame.
Qed.

(** Local typing is independent of memo and queue metadata. *)
Theorem node_typed_observation g h n :
  Egraph.nodes g = Egraph.nodes h ->
  EggRepresentation.node_typed a g n -> EggRepresentation.node_typed a h n.
Proof.
  intros Hnodes Htyped; destruct n as [s v|s op cs]; [exact Htyped|].
  destruct Htyped as [sorts [Hsorts Hshape]]; exists sorts; split; [|exact Hshape].
  clear Hshape.
  induction Hsorts as [|c sort cs sorts Hsort Hrest IH].
  - constructor.
  - constructor; [|exact IH].
    rewrite <- (sort_observation g h Hnodes c); exact Hsort.
Qed.

(** Concrete memo ownership and snapshot agreement imply the original class-valued memo contract. *)
Theorem kernel_memo_sound {work} g :
  Egraph.kernel_inv_on a g work -> EggRepresentation.memo_sound a g.
Proof.
  intros Hinv key owner Hget.
  destruct (Egraph.memo_owner a g Hinv key owner Hget) as [historical [Hsnapshot Hcode]].
  destruct (Egraph.snapshot_correct a g Hinv owner historical Hsnapshot)
    as [n [Hnode Hcanonical]].
  exists owner, n, historical; split; [exact Hnode|].
  split; [reflexivity|]; split; assumption.
Qed.

(** Equal semantic data transports the historical class-valued memo contract entry by entry. *)
Theorem memo_observation g h :
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  Egraph.memo g = Egraph.memo h ->
  EggRepresentation.memo_sound a g -> EggRepresentation.memo_sound a h.
Proof.
  intros Huf Hnodes Hmemo Hsound key owner Hget; rewrite <- Hmemo in Hget.
  destruct (Hsound key owner Hget) as [i [n [historical [Hnode [Hclass [Hcode Hsame]]]]]].
  exists i, n, historical; split.
  - unfold EggRepresentation.nodes_get in *; rewrite <- Hnodes; exact Hnode.
  - split.
    + unfold EggRepresentation.same_class in *.
      rewrite <- (find_observation g h Huf i), <- (find_observation g h Huf owner); exact Hclass.
    + split; [exact Hcode|].
      rewrite <- (canonical_observation g h Huf historical),
        <- (canonical_observation g h Huf n); exact Hsame.
Qed.

(** Justification annotations change no semantic backing data of a successful union. *)
Theorem union_annotation g c d reason h :
  Egraph.union_j a g c d reason = Some h ->
  exists given, Egraph.union a g c d = Some given /\
    Egraph.uf given = Egraph.uf h /\ Egraph.nodes given = Egraph.nodes h /\
    Egraph.memo given = Egraph.memo h /\ Egraph.next given = Egraph.next h.
Proof.
  rewrite Egraph.union_j_equation.
  destruct (Egraph.sort_of a g c) as [sc|] eqn:Hc,
    (Egraph.sort_of a g d) as [sd|] eqn:Hd; [|discriminate..].
  destruct (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) sc)
    (encode (EggAlg.sort_enc K Sort V a) sd)) eqn:Hcompare; [|discriminate..].
  intro Hresult; injection Hresult as <-.
  exists (Egraph.merge a g c d Egraph.JGiven); split.
  - rewrite EggStructural.union_equation, Hc, Hd, Hcompare; reflexivity.
  - split; [reflexivity|]; split; [reflexivity|]; split; reflexivity.
Qed.

(** Equal semantic data and independently verified memo duties transport structural validity. *)
Theorem structural_transport g h :
  EggRepresentation.structural_wf a g ->
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  Egraph.next g = Egraph.next h ->
  Map.wf Egraph.id_encoding (Egraph.memo h) ->
  EggRepresentation.memo_sound a h ->
  EggRepresentation.structural_wf a h.
Proof.
  intros Hwf Huf Hnodes Hnext Hmemo Hsound; constructor.
  - rewrite <- Huf; exact (EggRepresentation.forest_wf a g Hwf).
  - rewrite <- Hnodes; exact (EggRepresentation.nodes_wf a g Hwf).
  - exact Hmemo.
  - intro c; unfold EggRepresentation.nodes_get; rewrite <- Hnodes, <- Hnext.
    exact (EggRepresentation.allocation a g Hwf c).
  - intros c Hin; rewrite <- Huf in Hin; rewrite <- Hnext.
    exact (EggRepresentation.forest_domain a g Hwf c Hin).
  - intros c d sc sd Hsame Hc Hd.
    apply (EggRepresentation.class_sorts a g Hwf c d sc sd).
    + unfold EggRepresentation.same_class in *.
      rewrite (find_observation g h Huf c), (find_observation g h Huf d); exact Hsame.
    + rewrite (sort_observation g h Hnodes c); exact Hc.
    + rewrite (sort_observation g h Hnodes d); exact Hd.
  - intros c n Hnode.
    apply node_typed_observation with (g := g); [exact Hnodes|].
    apply (EggRepresentation.nodes_typed a g Hwf c n).
    unfold EggRepresentation.nodes_get in *; rewrite Hnodes; exact Hnode.
  - intros c n Hnode.
    assert (Hold : EggRepresentation.nodes_get g c = Some n).
    { unfold EggRepresentation.nodes_get in *; rewrite Hnodes; exact Hnode. }
    destruct (EggRepresentation.finite_witness a g Hwf c n Hold) as [e He].
    exists e; exact (proj1 (represents_observation g h c e Huf Hnodes) He).
  - exact Hsound.
Qed.

(** Equal semantic data and maintained memo coverage retain raw WF across metadata changes. *)
Theorem maintained_transport {work} g h :
  EggRepresentation.structural_wf a g ->
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  Egraph.next g = Egraph.next h ->
  Egraph.kernel_inv_on a h work -> EggTransition.layout a h ->
  EggRepresentation.structural_wf a h.
Proof.
  intros Hwf Huf Hnodes Hnext Hkernel Hlayout.
  exact (structural_transport g h Hwf Huf Hnodes Hnext
    (EggTransition.memo_wf a h Hlayout) (kernel_memo_sound h Hkernel)).
Qed.

(** Replacing queue data preserves the complete raw structural predicate. *)
Theorem queue_structural g queue :
  EggRepresentation.structural_wf a g ->
  EggRepresentation.structural_wf a (Egraph.with_queue g queue).
Proof.
  intro Hwf.
  apply (structural_transport g (Egraph.with_queue g queue) Hwf eq_refl eq_refl eq_refl).
  - exact (EggRepresentation.memo_wf a g Hwf).
  - exact (memo_observation g (Egraph.with_queue g queue) eq_refl eq_refl eq_refl
      (EggRepresentation.memo_correct a g Hwf)).
Qed.

(** Metadata-only updates preserve both represented terms and every class equality. *)
Theorem extends_observation g h :
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  EggRepresentation.extends a g h.
Proof.
  intros Huf Hnodes; split.
  - intros c e He; exact (proj1 (represents_observation g h c e Huf Hnodes) He).
  - intros c d Hsame; unfold EggRepresentation.same_class in *.
    rewrite <- (find_observation g h Huf c), <- (find_observation g h Huf d); exact Hsame.
Qed.

(** Metadata updates preserve genuine generated-equality soundness for the complete grammar. *)
Theorem sound_observation {H F C} (adm : EggSem.t K V C -> Prop)
    (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)) g h :
  Egraph.uf g = Egraph.uf h -> Egraph.nodes g = Egraph.nodes h ->
  EggRepresentation.sound a adm facts rules g -> EggRepresentation.sound a adm facts rules h.
Proof.
  intros Huf Hnodes Hsound c t u Ht Hu; apply (Hsound c t u).
  - exact (proj2 (represents_observation g h c t Huf Hnodes) Ht).
  - exact (proj2 (represents_observation g h c u Huf Hnodes) Hu).
Qed.

End Graph.

End EggView.
