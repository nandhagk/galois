(** * E-graph representation and operation laws

    Finite representation derivations give meaning to possibly cyclic classes.
    For example, a class containing a leaf and its own unary application has finite witnesses.
    Builds on: EgraphGraph, EgraphEquality and the public Base forest laws. *)

From Stdlib Require Import List Bool PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphIndex.
Import List.ListNotations Cost.Notations.

Module EggSpec.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

(** The algebra's three key dictionaries must distinguish different client values. *)
Record encoding_laws : Prop := Encoding_laws {
  op_encoding : BaseEncoding.encoding_laws (EggAlg.op_enc K Sort V a);
  sort_encoding : BaseEncoding.encoding_laws (EggAlg.sort_enc K Sort V a);
  var_encoding : BaseEncoding.encoding_laws (EggAlg.var_enc K Sort V a)
}.

Definition nodes_get (g : Egraph.t K Sort V) c :=
  Map.get Egraph.id_encoding c (Egraph.nodes g).

(** Representation unfolds a finite tree through nodes in the queried class. *)
Inductive represents (g : Egraph.t K Sort V) : Egraph.id -> EggTerm.t K Sort V -> Prop :=
  | rep_var : forall c i s v,
      Egraph.find a g i = Egraph.find a g c ->
      nodes_get g i = Some (Egraph.NVar s v) ->
      represents g c (EggTerm.Var s v)
  | rep_app : forall c i s op cs args,
      Egraph.find a g i = Egraph.find a g c ->
      nodes_get g i = Some (Egraph.NApp s op cs) ->
      Forall2 (represents g) cs args ->
      represents g c (EggTerm.App s op args).

(** Class equality compares the representatives returned by the implementation. *)
Definition same_class (g : Egraph.t K Sort V) c d : Prop :=
  Egraph.find a g c = Egraph.find a g d.

(** A valid local node has declared variables or allocated children of an accepted shape. *)
Definition node_typed (g : Egraph.t K Sort V) (n : Egraph.enode K Sort V) : Prop :=
  match n with
  | Egraph.NVar s v => EggAlg.var_sort a v = Some s
  | Egraph.NApp s op cs =>
    exists ss, Forall2 (fun c s => Egraph.sort_of a g c = Some s) cs ss /\
      EggAlg.op_shape a op ss s = true
  end.

(** Dirty memo keys retain historical syntax whose children still denote the same classes. *)
Definition memo_sound (g : Egraph.t K Sort V) : Prop :=
  forall key c, Map.get Egraph.id_encoding key (Egraph.memo g) = Some c ->
    exists i n historical,
      nodes_get g i = Some n /\
      same_class g i c /\
      Egraph.node_code a historical = key /\
      Egraph.canonical a g historical = Egraph.canonical a g n.

(** Raw structural validity carries forest and map duties and finite witnesses for allocations. *)
Record structural_wf (g : Egraph.t K Sort V) : Prop := Wf {
  forest_wf : UnionFind.wf Egraph.id_encoding (Egraph.uf g);
  nodes_wf : Map.wf Egraph.id_encoding (Egraph.nodes g);
  memo_wf : Map.wf Egraph.id_encoding (Egraph.memo g);
  allocation : forall c, (exists n, nodes_get g c = Some n) <-> (c < Egraph.next g)%positive;
  forest_domain : forall c, In c (UnionFind.keys Egraph.id_encoding (Egraph.uf g)) ->
    (c < Egraph.next g)%positive;
  class_sorts : forall c d sc sd, same_class g c d ->
    Egraph.sort_of a g c = Some sc -> Egraph.sort_of a g d = Some sd -> sc = sd;
  nodes_typed : forall c n, nodes_get g c = Some n -> node_typed g n;
  finite_witness : forall c n, nodes_get g c = Some n -> exists e, represents g c e;
  memo_correct : memo_sound g
}.

(** Structural operation laws retain the raw-state domain while maintained proofs are composed. *)
Definition wf (g : Egraph.t K Sort V) : Prop := structural_wf g.

(** Clean graphs have a current memo index and merge all equal canonical signatures. *)
Record clean (g : Egraph.t K Sort V) : Prop := Clean {
  clean_wf : wf g;
  congruence_closed : forall i j n m, nodes_get g i = Some n -> nodes_get g j = Some m ->
    Egraph.canonical a g n = Egraph.canonical a g m -> same_class g i j;
  memo_current : forall key c, Map.get Egraph.id_encoding key (Egraph.memo g) = Some c ->
    exists i n, nodes_get g i = Some n /\ same_class g i c /\
      Egraph.node_code a (Egraph.canonical a g n) = key;
  memo_complete : forall i n, nodes_get g i = Some n ->
    exists c, Map.get Egraph.id_encoding
      (Egraph.node_code a (Egraph.canonical a g n)) (Egraph.memo g) = Some c /\
      same_class g i c
}.

(** A sound class relates all its represented finite terms by the client's generated equality. *)
Definition sound {H F C} (adm : EggSem.t K V C -> Prop) (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) (g : Egraph.t K Sort V) : Prop :=
  forall c t u, represents g c t -> represents g c u -> EggEqual.rel a adm facts rules t u.

(** Two states have the same classes when every pair of identifiers has the same equality test. *)
Definition same_class_equal (g h : Egraph.t K Sort V) : Prop :=
  forall c d, same_class g c d <-> same_class h c d.

Local Lemma id_laws : BaseEncoding.encoding_laws Egraph.id_encoding.
Proof.
  exact positive_encoding_laws.
Qed.

Local Lemma find_equation g c :
  Egraph.find a g c = fst (UnionFind.find Egraph.id_encoding c (Egraph.uf g)).
Proof.
  reflexivity.
Qed.

Local Lemma sort_of_equation g c :
  Egraph.sort_of a g c = option_map Egraph.node_sort (nodes_get g c).
Proof.
  reflexivity.
Qed.

Local Lemma canonical_equation g n :
  Egraph.canonical a g n =
    match n with
    | Egraph.NVar s v => Egraph.NVar s v
    | Egraph.NApp s op cs => Egraph.NApp s op (map (Egraph.find a g) cs)
    end.
Proof.
  destruct n; [reflexivity|].
  unfold Egraph.canonical, Egraph.canonical_c.
  rewrite Cost.value_map, value_map_c; reflexivity.
Qed.

Local Lemma signature_equation n :
  Egraph.signature a n =
    match n with
    | Egraph.NVar s v =>
      [1%positive; encode (EggAlg.sort_enc K Sort V a) s;
        encode (EggAlg.var_enc K Sort V a) v]
    | Egraph.NApp s op cs =>
      2%positive :: encode (EggAlg.sort_enc K Sort V a) s ::
        encode (EggAlg.op_enc K Sort V a) op :: cs
    end.
Proof.
  destruct n; reflexivity.
Qed.

Local Lemma node_code_equation n :
  Egraph.node_code a n =
    encode (codec_enc (list_codec positive_codec)) (Egraph.signature a n).
Proof.
  reflexivity.
Qed.

(** Memo serialization is injective when the client encodings are injective. *)
Theorem node_code_injective :
  encoding_laws -> forall n m, Egraph.node_code a n = Egraph.node_code a m -> n = m.
Proof.
  intros [Hop Hsort Hvar] n m Heq.
  rewrite !node_code_equation in Heq.
  apply (encode_injective (codec_laws_injective _
    (list_codec_laws positive_codec positive_codec_laws))) in Heq.
  destruct n as [s v|s op cs], m as [s' v'|s' op' ds];
    rewrite !signature_equation in Heq; try discriminate.
  - injection Heq as Hs Hv.
    apply (encode_injective Hsort) in Hs.
    apply (encode_injective Hvar) in Hv; now subst.
  - injection Heq as Hs Hop' Hcs.
    apply (encode_injective Hsort) in Hs.
    apply (encode_injective Hop) in Hop'; now subst.
Qed.

Local Lemma represents_ind_all g (P : Egraph.id -> EggTerm.t K Sort V -> Prop)
    (Hvar : forall c i s v, same_class g i c -> nodes_get g i = Some (Egraph.NVar s v) ->
      P c (EggTerm.Var s v))
    (Happ : forall c i s op cs args, same_class g i c ->
      nodes_get g i = Some (Egraph.NApp s op cs) ->
      Forall2 (represents g) cs args -> Forall2 P cs args ->
      P c (EggTerm.App s op args)) :
  forall c e, represents g c e -> P c e.
Proof.
  fix IH 3.
  intros c e Hrep; destruct Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs].
  - exact (Hvar c i s v Hclass Hnode).
  - apply (Happ c i s op cs args Hclass Hnode Hargs).
    clear Hclass Hnode.
    induction Hargs as [|d e ds es Hrep Hrest IHrest].
    + constructor.
    + constructor; [exact (IH d e Hrep)|exact IHrest].
Qed.

(** Finite representation is invariant under changing the queried identifier within a class. *)
Theorem represents_same g c d e :
  same_class g c d -> represents g c e -> represents g d e.
Proof.
  intros Hsame Hrep; destruct Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs].
  - apply (rep_var g d i s v); [unfold same_class in Hsame; congruence|exact Hnode].
  - apply (rep_app g d i s op cs args);
      [unfold same_class in Hsame; congruence|exact Hnode|exact Hargs].
Qed.

(** Find is idempotent under the Base forest invariant carried by WF. *)
Theorem find_idem g c :
  wf g -> Egraph.find a g (Egraph.find a g c) = Egraph.find a g c.
Proof.
  intro Hwf; rewrite !find_equation.
  apply UnionFind.find_rep_canonical; [exact id_laws|exact (forest_wf g Hwf)].
Qed.

Local Lemma allocated_root g c :
  wf g -> (c < Egraph.next g)%positive ->
  (Egraph.find a g c < Egraph.next g)%positive.
Proof.
  intros Hwf Hc.
  destruct (Pos.ltb (Egraph.find a g c) (Egraph.next g)) eqn:Htest.
  { now apply Pos.ltb_lt. }
  assert (Hnot : ~ (Egraph.find a g c < Egraph.next g)%positive).
  { apply Pos.ltb_ge in Htest; lia. }
  assert (Houtside : ~ In (Egraph.find a g c)
    (UnionFind.keys Egraph.id_encoding (Egraph.uf g))).
  { intro Hin; apply Hnot; exact (forest_domain g Hwf _ Hin). }
  pose proof (UnionFind.keys_support Egraph.id_encoding id_laws (Egraph.uf g)
    (Egraph.find a g c) c (forest_wf g Hwf) Houtside) as Hsingleton.
  assert (Hsame : UnionFind.equiv Egraph.id_encoding (Egraph.uf g) (Egraph.find a g c) c).
  { change (Egraph.find a g (Egraph.find a g c) = Egraph.find a g c).
    exact (find_idem g c Hwf). }
  specialize (Hsingleton Hsame).
  exfalso; apply Hnot; rewrite <- Hsingleton; exact Hc.
Qed.

(** Find's allocation bound applies to identifiers with a successful sort lookup. *)
Theorem find_wf g c s :
  wf g -> Egraph.sort_of a g c = Some s ->
  (Egraph.find a g c < Egraph.next g)%positive.
Proof.
  intros Hwf Hsort; apply allocated_root; [exact Hwf|].
  apply (proj1 (allocation g Hwf c)).
  rewrite sort_of_equation in Hsort.
  destruct (nodes_get g c) as [n|] eqn:Hnode; [exists n; reflexivity|discriminate].
Qed.

Local Lemma sort_allocated g c :
  (exists s, Egraph.sort_of a g c = Some s) <-> exists n, nodes_get g c = Some n.
Proof.
  rewrite sort_of_equation; destruct (nodes_get g c) as [n|] eqn:Hnode; cbn.
  - split; intro H; eauto.
  - split; intros [x Hx]; discriminate.
Qed.

Local Lemma class_allocated g c d :
  wf g -> same_class g c d -> (c < Egraph.next g)%positive ->
  (d < Egraph.next g)%positive.
Proof.
  intros Hwf Hsame Hc.
  destruct (Pos.ltb d (Egraph.next g)) eqn:Htest.
  { now apply Pos.ltb_lt. }
  assert (Hnot : ~ (d < Egraph.next g)%positive).
  { apply Pos.ltb_ge in Htest; lia. }
  assert (Houtside : ~ In d (UnionFind.keys Egraph.id_encoding (Egraph.uf g))).
  { intro Hin; apply Hnot; exact (forest_domain g Hwf _ Hin). }
  assert (Hequiv : UnionFind.equiv Egraph.id_encoding (Egraph.uf g) d c).
  { change (same_class g d c); symmetry; exact Hsame. }
  pose proof (UnionFind.keys_support Egraph.id_encoding id_laws _ d c
    (forest_wf g Hwf) Houtside Hequiv) as Heq; subst; contradiction.
Qed.

(** Every finitely represented term belongs to an allocated class. *)
Theorem represents_allocated g c e :
  wf g -> represents g c e -> (c < Egraph.next g)%positive.
Proof.
  intros Hwf Hrep; destruct Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs].
  - eapply class_allocated; [exact Hwf|exact Hclass|].
    apply (proj1 (allocation g Hwf i)); eauto.
  - eapply class_allocated; [exact Hwf|exact Hclass|].
    apply (proj1 (allocation g Hwf i)); eauto.
Qed.

(** A represented term has the sort recorded at its class identifier. *)
Theorem represents_sort g c e :
  wf g -> represents g c e -> Egraph.sort_of a g c = Some (EggTerm.sort_of e).
Proof.
  intros Hwf Hrep.
  pose proof (represents_allocated g c e Hwf Hrep) as Halloc.
  destruct (proj2 (allocation g Hwf c) Halloc) as [n Hn].
  assert (Hsort : Egraph.sort_of a g c = Some (Egraph.node_sort n)).
  { rewrite sort_of_equation, Hn; reflexivity. }
  destruct Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs];
    cbn [EggTerm.sort_of];
    assert (Hi : Egraph.sort_of a g i = Some s) by
      (rewrite sort_of_equation, Hnode; reflexivity);
    pose proof (class_sorts g Hwf i c s _ Hclass Hi Hsort) as Heq;
    now rewrite <- Heq in Hsort.
Qed.

(** Every finitely represented term in a well-formed graph is well typed. *)
Theorem represents_typed g :
  wf g -> forall c e, represents g c e -> EggTerm.typed a e.
Proof.
  intro Hwf; apply (represents_ind_all g (fun _ e => EggTerm.typed a e)).
  - intros c i s v Hsame Hnode; apply EggTerm.typed_var.
    exact (nodes_typed g Hwf i _ Hnode).
  - intros c i s op cs args Hsame Hnode Hargs IHargs.
    destruct (nodes_typed g Hwf i _ Hnode) as [ss [Hsorts Hshape]].
    apply EggTerm.typed_app.
    + clear Hargs Hsorts Hnode Hsame Hshape.
      induction IHargs; constructor; assumption.
    + assert (Hss : ss = map EggTerm.sort_of args).
      { clear Hnode Hshape Hsame IHargs; revert ss Hsorts.
        induction Hargs as [|d e ds es Hrep Hrest IH]; intros ss Hsorts;
          inversion Hsorts as [|d' s' ds' ss' Hsort Htail]; subst.
        - reflexivity.
        - cbn; f_equal.
          + pose proof (represents_sort g d e Hwf Hrep); congruence.
          + exact (IH _ Htail). }
      now rewrite <- Hss.
Qed.

Local Lemma empty_equation :
  @Egraph.empty K Sort V =
    Egraph.Make K Sort V UnionFind.make Map.empty Map.empty 1%positive Egraph.empty_kernel.
Proof.
  reflexivity.
Qed.

Local Lemma empty_find c :
  Egraph.find a Egraph.empty c = c.
Proof.
  rewrite find_equation, empty_equation; cbn [Egraph.uf].
  rewrite UnionFind.find_equation, UnionFind.make_equation; cbn [UnionFind.max_rank].
  rewrite UnionFind.find_fuel_equation; cbn [UnionFind.parents].
  now rewrite Map.get_empty.
Qed.

(** The empty graph satisfies every structural invariant without client key laws. *)
Theorem empty_wf : wf Egraph.empty.
Proof.
  constructor.
  - apply UnionFind.wf_make.
  - apply Map.wf_empty.
  - apply Map.wf_empty.
  - intros c; unfold nodes_get; rewrite empty_equation; cbn [Egraph.nodes Egraph.next].
    rewrite Map.get_empty; split; [intros [n Hn]; discriminate|intros Hlt; lia].
  - intros c Hin; rewrite empty_equation in Hin; cbn [Egraph.uf] in Hin.
    rewrite UnionFind.keys_make in Hin; contradiction.
  - intros c d sc sd Hsame Hc Hd.
    rewrite sort_of_equation in Hc; unfold nodes_get in Hc.
    rewrite empty_equation in Hc; cbn [Egraph.nodes] in Hc.
    rewrite Map.get_empty in Hc; discriminate.
  - intros c n Hnode; unfold nodes_get in Hnode.
    rewrite empty_equation in Hnode; cbn [Egraph.nodes] in Hnode.
    rewrite Map.get_empty in Hnode; discriminate.
  - intros c n Hnode; unfold nodes_get in Hnode.
    rewrite empty_equation in Hnode; cbn [Egraph.nodes] in Hnode.
    rewrite Map.get_empty in Hnode; discriminate.
  - intros key c Hget; rewrite empty_equation in Hget; cbn [Egraph.memo] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
Qed.

(** The empty graph has a complete empty memo and no unmerged congruent nodes. *)
Theorem empty_clean : clean Egraph.empty.
Proof.
  constructor; [exact empty_wf| | |].
  - intros i j n m Hnode; unfold nodes_get in Hnode.
    rewrite empty_equation in Hnode; cbn [Egraph.nodes] in Hnode.
    rewrite Map.get_empty in Hnode; discriminate.
  - intros key c Hget; rewrite empty_equation in Hget; cbn [Egraph.memo] in Hget.
    rewrite Map.get_empty in Hget; discriminate.
  - intros i n Hnode; unfold nodes_get in Hnode.
    rewrite empty_equation in Hnode; cbn [Egraph.nodes] in Hnode.
    rewrite Map.get_empty in Hnode; discriminate.
Qed.

Local Lemma represents_mono g h :
  (forall i n, nodes_get g i = Some n -> nodes_get h i = Some n) ->
  (forall c d, same_class g c d -> same_class h c d) ->
  forall c e, represents g c e -> represents h c e.
Proof.
  intros Hnodes Hclasses; apply (represents_ind_all g (represents h)).
  - intros c i s v Hsame Hnode.
    eapply rep_var; [apply Hclasses; exact Hsame|apply Hnodes; exact Hnode].
  - intros c i s op cs args Hsame Hnode Hargs IHargs.
    eapply rep_app; [apply Hclasses; exact Hsame|apply Hnodes; exact Hnode|exact IHargs].
Qed.

Local Lemma map_classes (f f' : Egraph.id -> Egraph.id) cs ds :
  (forall c d, f c = f d -> f' c = f' d) ->
  map f cs = map f ds -> map f' cs = map f' ds.
Proof.
  intros Hmono; revert ds; induction cs as [|c cs IH]; intros [|d ds] Heq;
    cbn in *; try discriminate; [reflexivity|].
  injection Heq as Hcd Hrest; f_equal; [apply Hmono; exact Hcd|apply IH; exact Hrest].
Qed.

Local Lemma canonical_mono g h n m :
  (forall c d, same_class g c d -> same_class h c d) ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.canonical a h n = Egraph.canonical a h m.
Proof.
  intros Hmono Heq.
  destruct n as [s v|s op cs], m as [s' v'|s' op' ds];
    rewrite !canonical_equation in *; try discriminate.
  - exact Heq.
  - injection Heq as Hs Hop Hcs; subst; f_equal.
    exact (map_classes _ _ cs ds Hmono Hcs).
Qed.

Local Lemma union_equation g c d :
  Egraph.union a g c d =
    match Egraph.sort_of a g c, Egraph.sort_of a g d with
    | Some sc, Some sd =>
      match Map.code_compare
        (encode (EggAlg.sort_enc K Sort V a) sc)
        (encode (EggAlg.sort_enc K Sort V a) sd) with
      | Eq => Some (Egraph.merge a g c d Egraph.JGiven)
      | _ => None
      end
    | _, _ => None
    end.
Proof.
  unfold Egraph.union, Egraph.union_c, Egraph.union_j_c; rewrite !Cost.value_bind.
  fold (Egraph.sort_of a g c) (Egraph.sort_of a g d).
  destruct (Egraph.sort_of a g c), (Egraph.sort_of a g d); [|reflexivity..].
  rewrite !Cost.value_bind; fold (encode (EggAlg.sort_enc K Sort V a) s).
  fold (encode (EggAlg.sort_enc K Sort V a) s0).
  fold (Map.code_compare (encode (EggAlg.sort_enc K Sort V a) s)
    (encode (EggAlg.sort_enc K Sort V a) s0)).
  destruct (Map.code_compare _ _); reflexivity.
Qed.

Local Lemma union_inv g c d h :
  encoding_laws -> Egraph.union a g c d = Some h ->
  exists s, Egraph.sort_of a g c = Some s /\ Egraph.sort_of a g d = Some s /\
    h = Egraph.merge a g c d Egraph.JGiven.
Proof.
  intros Hl; rewrite union_equation.
  destruct (Egraph.sort_of a g c) as [sc|] eqn:Hc; [|discriminate].
  destruct (Egraph.sort_of a g d) as [sd|] eqn:Hd; [|discriminate].
  destruct (Map.code_compare _ _) eqn:Hcmp; try discriminate.
  apply Map.code_compare_eq in Hcmp.
  apply (encode_injective (sort_encoding Hl)) in Hcmp; subst sd.
  intro Hresult; injection Hresult as <-; exists sc; auto.
Qed.

Local Lemma merged_classes g c d :
  wf g -> forall x y,
    same_class (Egraph.merge a g c d Egraph.JGiven) x y <->
    same_class g x y \/ (same_class g x c /\ same_class g d y) \/
      (same_class g x d /\ same_class g c y).
Proof.
  intros Hwf x y; unfold same_class; rewrite !find_equation.
  apply UnionFind.union_equiv; [exact id_laws|exact (forest_wf g Hwf)].
Qed.

(** Successful union preserves every finite representation and every old class equality. *)
Theorem union_preserves g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h ->
  (forall x e, represents g x e -> represents h x e) /\
  (forall x y, same_class g x y -> same_class h x y).
Proof.
  intros Hl Hwf Hunion.
  destruct (union_inv g c d h Hl Hunion) as [s [Hc [Hd ->]]].
  assert (Hmono : forall x y, same_class g x y ->
    same_class (Egraph.merge a g c d Egraph.JGiven) x y).
  { intros x y Hsame; apply (proj2 (merged_classes g c d Hwf x y)); auto. }
  split; [apply represents_mono; [intros i n Hnode; exact Hnode|exact Hmono]|exact Hmono].
Qed.

(** Successful union places its two allocated arguments in one class. *)
Theorem union_same g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h -> same_class h c d.
Proof.
  intros Hl Hwf Hunion.
  destruct (union_inv g c d h Hl Hunion) as [s [Hc [Hd ->]]].
  apply (proj2 (merged_classes g c d Hwf c d)).
  right; left; split; reflexivity.
Qed.

(** Successful union preserves rank, map, typing, productivity and historical memo invariants. *)
Theorem union_wf g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h -> wf h.
Proof.
  intros Hl Hwf Hunion.
  destruct (union_preserves g c d h Hl Hwf Hunion) as [Hrep Hmono].
  destruct (union_inv g c d h Hl Hunion) as [s [Hc [Hd ->]]].
  constructor.
  - apply UnionFind.wf_union; [exact id_laws|exact (forest_wf g Hwf)].
  - exact (nodes_wf g Hwf).
  - exact (memo_wf g Hwf).
  - exact (allocation g Hwf).
  - intros x Hin.
    apply (UnionFind.keys_union Egraph.id_encoding id_laws _ c d x
      (forest_wf g Hwf)) in Hin.
    destruct Hin as [->|[->|Hin]].
    + apply (proj1 (allocation g Hwf c)); apply sort_allocated; eauto.
    + apply (proj1 (allocation g Hwf d)); apply sort_allocated; eauto.
    + exact (forest_domain g Hwf x Hin).
  - intros x y sx sy Hsame Hx Hy.
    apply (proj1 (merged_classes g c d Hwf x y)) in Hsame.
    destruct Hsame as [Hsame|[[Hxc Hdy]|[Hxd Hcy]]].
    + exact (class_sorts g Hwf x y sx sy Hsame Hx Hy).
    + pose proof (class_sorts g Hwf x c sx s Hxc Hx Hc).
      pose proof (class_sorts g Hwf d y s sy Hdy Hd Hy); congruence.
    + pose proof (class_sorts g Hwf x d sx s Hxd Hx Hd).
      pose proof (class_sorts g Hwf c y s sy Hcy Hc Hy); congruence.
  - exact (nodes_typed g Hwf).
  - intros x n Hnode.
    destruct (finite_witness g Hwf x n Hnode) as [e He].
    exists e; apply Hrep; exact He.
  - intros key x Hget.
    destruct (memo_correct g Hwf key x Hget) as [i [n [old [Hnode [Hsame [Hcode Hcanon]]]]]].
    exists i, n, old; split; [exact Hnode|].
    split; [apply Hmono; exact Hsame|].
    split; [exact Hcode|exact (canonical_mono g _ old n Hmono Hcanon)].
Qed.

Section SoundUnion.
Context {H F C : Type} (adm : EggSem.t K V C -> Prop)
  (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)).

Local Lemma union_old_related g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h ->
  sound adm facts rules g ->
  (forall t u, represents g c t -> represents g d u -> EggEqual.rel a adm facts rules t u) ->
  forall x y t u, represents g x t -> represents g y u -> same_class h x y ->
    EggEqual.rel a adm facts rules t u.
Proof.
  intros Hl Hwf Hunion Hsound Hjoin x y t u Ht Hu Hsame.
  destruct (union_inv g c d h Hl Hunion) as [s [Hc [Hd Heq]]]; subst h.
  apply (proj1 (merged_classes g c d Hwf x y)) in Hsame.
  destruct Hsame as [Hsame|[[Hxc Hdy]|[Hxd Hcy]]].
  - apply (Hsound y t u); [apply (represents_same g x y t Hsame Ht)|exact Hu].
  - apply Hjoin.
    + exact (represents_same g x c t Hxc Ht).
    + apply (represents_same g y d u); [symmetry; exact Hdy|exact Hu].
  - apply EggEqual.sym; apply Hjoin.
    + apply (represents_same g y c u); [symmetry; exact Hcy|exact Hu].
    + exact (represents_same g x d t Hxd Ht).
Qed.

Local Lemma union_old_witness g c d h :
  encoding_laws -> wf g -> Egraph.union a g c d = Some h ->
  sound adm facts rules g ->
  (forall t u, represents g c t -> represents g d u -> EggEqual.rel a adm facts rules t u) ->
  forall x t, represents h x t ->
    exists u, represents g x u /\ EggEqual.rel a adm facts rules t u.
Proof.
  intros Hl Hwf Hunion Hsound Hjoin.
  pose proof (union_wf g c d h Hl Hwf Hunion) as Hnew.
  assert (Hnodes : forall i, nodes_get h i = nodes_get g i).
  { destruct (union_inv g c d h Hl Hunion) as [s [Hc [Hd ->]]]; reflexivity. }
  assert (Hwitness : forall x t, represents h x t -> exists u, represents g x u).
  { intros x t Ht.
    pose proof (represents_allocated h x t Hnew Ht) as Hallocated.
    destruct (proj2 (allocation h Hnew x) Hallocated) as [n Hn].
    rewrite Hnodes in Hn; exact (finite_witness g Hwf x n Hn). }
  apply (represents_ind_all h
    (fun x t => exists u, represents g x u /\ EggEqual.rel a adm facts rules t u)).
  - intros x i s v Hsame Hnode.
    assert (Ht : represents h x (EggTerm.Var s v)) by
      (exact (rep_var h x i s v Hsame Hnode)).
    destruct (Hwitness x _ Ht) as [u Hu].
    exists u; split; [exact Hu|].
    apply (union_old_related g c d h Hl Hwf Hunion Hsound Hjoin
      i x (EggTerm.Var s v) u).
    + apply (rep_var g i i s v); [reflexivity|now rewrite <- Hnodes].
    + exact Hu.
    + exact Hsame.
  - intros x i s op cs ts Hsame Hnode Hargs IHargs.
    assert (Ht : represents h x (EggTerm.App s op ts)) by
      (exact (rep_app h x i s op cs ts Hsame Hnode Hargs)).
    destruct (Hwitness x _ Ht) as [u Hu].
    assert (Hchildren : exists us, Forall2 (represents g) cs us /\
      Forall2 (EggEqual.rel a adm facts rules) ts us).
    { clear Hnode Hargs Ht Hsame.
      induction IHargs as [|c' t cs' ts' [u' [Hu' Heq]] Hrest [us [Hus Heqs]]].
      - exists []; split; constructor.
      - exists (u' :: us); split; constructor; assumption. }
    destruct Hchildren as [us [Hus Heqs]].
    exists u; split; [exact Hu|].
    eapply EggEqual.trans; [apply EggEqual.app; exact Heqs|].
    apply (union_old_related g c d h Hl Hwf Hunion Hsound Hjoin
      i x (EggTerm.App s op us) u).
    + apply (rep_app g i i s op cs us); [reflexivity|now rewrite <- Hnodes|exact Hus].
    + exact Hu.
    + exact Hsame.
Qed.

(** Old soundness and a genuine cross-class equality justification make union sound. *)
Theorem union_sound g c d h :
  encoding_laws -> wf g -> sound adm facts rules g ->
  (forall t u, represents g c t -> represents g d u -> EggEqual.rel a adm facts rules t u) ->
  Egraph.union a g c d = Some h -> sound adm facts rules h.
Proof.
  intros Hl Hwf Hsound Hjoin Hunion x t u Ht Hu.
  destruct (union_old_witness g c d h Hl Hwf Hunion Hsound Hjoin x t Ht)
    as [t' [Ht' Htt']].
  destruct (union_old_witness g c d h Hl Hwf Hunion Hsound Hjoin x u Hu)
    as [u' [Hu' Huu']].
  eapply EggEqual.trans; [exact Htt'|].
  eapply EggEqual.trans; [exact (Hsound x t' u' Ht' Hu')|].
  apply EggEqual.sym; exact Huu'.
Qed.

End SoundUnion.

Local Lemma child_sorts_equation g cs :
  Egraph.child_sorts a g cs =
    match cs with
    | [] => Some []
    | c :: ds =>
      match Egraph.sort_of a g c, Egraph.child_sorts a g ds with
      | Some s, Some ss => Some (s :: ss)
      | _, _ => None
      end
    end.
Proof.
  destruct cs; [reflexivity|].
  unfold Egraph.child_sorts, Egraph.child_sorts_c at 1.
  cbn [fold_right_c]; rewrite !Cost.value_bind; reflexivity.
Qed.

Local Lemma child_sorts_spec g cs ss :
  Egraph.child_sorts a g cs = Some ss <->
    Forall2 (fun c s => Egraph.sort_of a g c = Some s) cs ss.
Proof.
  revert ss; induction cs as [|c cs IH]; intros ss; rewrite child_sorts_equation.
  - split; [intro Heq; injection Heq as <-; constructor|intro H; inversion H; reflexivity].
  - split.
    + destruct (Egraph.sort_of a g c) as [s|] eqn:Hsort; [|discriminate].
      destruct (Egraph.child_sorts a g cs) as [ds|] eqn:Hrest; [|discriminate].
      intros Heq; injection Heq as <-; constructor; [exact Hsort|now apply IH].
    + intros Hrel; inversion Hrel as [|c' s cs' ds Hsort Hrest]; subst.
      apply IH in Hrest; now rewrite Hsort, Hrest.
Qed.

Local Lemma node_valid_spec g n :
  encoding_laws -> (Egraph.node_valid a g n = true <-> node_typed g n).
Proof.
  intros Hl; destruct n as [s v|s op cs].
  - unfold Egraph.node_valid, Egraph.node_valid_c; rewrite !Cost.value_bind.
    fold (EggAlg.var_sort a v); cbn [node_typed].
    destruct (EggAlg.var_sort a v) as [d|] eqn:Hv.
    + change (eqb (EggAlg.sort_enc K Sort V a) s d = true <-> Some d = Some s).
      rewrite (eqb_true_iff _ (sort_encoding Hl)); split; congruence.
    + split; discriminate.
  - unfold Egraph.node_valid, Egraph.node_valid_c; rewrite Cost.value_bind.
    fold (Egraph.child_sorts a g cs); cbn [node_typed].
    destruct (Egraph.child_sorts a g cs) as [ss|] eqn:Hsorts.
    + split.
      * intro Hshape; exists ss; split; [now apply child_sorts_spec|exact Hshape].
      * intros [ds [Hds Hshape]]; apply child_sorts_spec in Hds.
        rewrite Hsorts in Hds; injection Hds as <-; exact Hshape.
    + split; [discriminate|].
      intros [ds [Hds Hshape]]; apply child_sorts_spec in Hds; congruence.
Qed.

Local Lemma root_sort g c s :
  wf g -> Egraph.sort_of a g c = Some s ->
  Egraph.sort_of a g (Egraph.find a g c) = Some s.
Proof.
  intros Hwf Hsort.
  destruct (proj2 (allocation g Hwf _) (find_wf g c s Hwf Hsort)) as [n Hnode].
  assert (Hroot : Egraph.sort_of a g (Egraph.find a g c) = Some (Egraph.node_sort n)).
  { rewrite sort_of_equation, Hnode; reflexivity. }
  assert (Hsame : same_class g c (Egraph.find a g c)).
  { unfold same_class; symmetry; exact (find_idem g c Hwf). }
  pose proof (class_sorts g Hwf _ _ _ _ Hsame Hsort Hroot) as Heq.
  now rewrite <- Heq in Hroot.
Qed.

Local Lemma canonical_typed g n :
  wf g -> node_typed g n -> node_typed g (Egraph.canonical a g n).
Proof.
  intros Hwf Htyped; destruct n as [s v|s op cs]; rewrite canonical_equation; [exact Htyped|].
  destruct Htyped as [ss [Hsorts Hshape]]; exists ss; split; [|exact Hshape].
  clear Hshape; induction Hsorts as [|c s' cs ss Hsort Hrest IH]; cbn [map].
  - constructor.
  - constructor; [apply root_sort; assumption|exact IH].
Qed.

Local Lemma canonical_idem g n :
  wf g -> Egraph.canonical a g (Egraph.canonical a g n) = Egraph.canonical a g n.
Proof.
  intro Hwf; destruct n; rewrite !canonical_equation; [reflexivity|].
  f_equal; rewrite map_map; apply map_ext; intro c; apply find_idem; exact Hwf.
Qed.

Local Lemma allocate_equation g n key :
  Egraph.allocate a g n key =
    (Egraph.next g, Egraph.Make K Sort V
      (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g))
      (Map.set Egraph.id_encoding (Egraph.next g) n (Egraph.nodes g))
      (Map.set Egraph.id_encoding key (Egraph.next g) (Egraph.memo g))
      (Pos.succ (Egraph.next g)) (Egraph.allocation_kernel g n)).
Proof.
  reflexivity.
Qed.

Local Lemma allocate_classes g n key :
  wf g -> forall c d, same_class (snd (Egraph.allocate a g n key)) c d <->
    same_class g c d.
Proof.
  intros Hwf c d; rewrite allocate_equation.
  change (UnionFind.equiv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g)) c d <->
    UnionFind.equiv Egraph.id_encoding (Egraph.uf g) c d).
  rewrite (UnionFind.union_equiv Egraph.id_encoding id_laws _ _ _ _ _
    (forest_wf g Hwf)).
  unfold UnionFind.equiv; intuition congruence.
Qed.

Local Lemma fresh_singleton g c :
  wf g -> same_class g (Egraph.next g) c -> c = Egraph.next g.
Proof.
  intros Hwf Hsame.
  apply (UnionFind.keys_support Egraph.id_encoding id_laws (Egraph.uf g) (Egraph.next g) c).
  - exact (forest_wf g Hwf).
  - intro Hin; pose proof (forest_domain g Hwf _ Hin); lia.
  - exact Hsame.
Qed.

Local Lemma allocate_lookup g n key c :
  wf g -> nodes_get (snd (Egraph.allocate a g n key)) c =
    if Pos.eq_dec c (Egraph.next g) then Some n else nodes_get g c.
Proof.
  intros Hwf; rewrite allocate_equation; unfold nodes_get; cbn [snd Egraph.nodes].
  destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
  - apply Map.get_set_same; exact (nodes_wf g Hwf).
  - apply Map.get_set_other; [exact id_laws|exact (nodes_wf g Hwf)|exact Hne].
Qed.

Local Lemma allocate_old_lookup g n key c m :
  wf g -> nodes_get g c = Some m ->
  nodes_get (snd (Egraph.allocate a g n key)) c = Some m.
Proof.
  intros Hwf Hnode; rewrite allocate_lookup by exact Hwf.
  pose proof (proj1 (allocation g Hwf c) (ex_intro _ m Hnode)) as Hlt.
  destruct (Pos.eq_dec c (Egraph.next g)); [subst; lia|exact Hnode].
Qed.

Local Lemma allocate_old_sort g n key c s :
  wf g -> Egraph.sort_of a g c = Some s ->
  Egraph.sort_of a (snd (Egraph.allocate a g n key)) c = Some s.
Proof.
  intros Hwf Hsort; rewrite !sort_of_equation in *.
  destruct (nodes_get g c) as [m|] eqn:Hnode; [|discriminate].
  rewrite (allocate_old_lookup g n key c m Hwf Hnode); exact Hsort.
Qed.

Local Lemma node_typed_mono g h n :
  (forall c s, Egraph.sort_of a g c = Some s -> Egraph.sort_of a h c = Some s) ->
  node_typed g n -> node_typed h n.
Proof.
  intros Hsort Htyped; destruct n as [s v|s op cs]; [exact Htyped|].
  destruct Htyped as [ss [Hss Hshape]]; exists ss; split; [|exact Hshape].
  clear Hshape; induction Hss as [|c s' cs ss Hc Hrest IH].
  - constructor.
  - constructor; [now apply Hsort|exact IH].
Qed.

Local Lemma allocate_preserves g n key :
  wf g ->
  (forall c e, represents g c e -> represents (snd (Egraph.allocate a g n key)) c e) /\
  (forall c d, same_class g c d -> same_class (snd (Egraph.allocate a g n key)) c d).
Proof.
  intro Hwf.
  assert (Hmono : forall c d, same_class g c d ->
    same_class (snd (Egraph.allocate a g n key)) c d).
  { intros c d Hsame; apply (proj2 (allocate_classes g n key Hwf c d)); exact Hsame. }
  split; [apply represents_mono; [intros; eapply allocate_old_lookup; eassumption|exact Hmono]|
    exact Hmono].
Qed.

(** A node represents a term when its child identifiers represent the term's arguments. *)
Inductive node_represents (g : Egraph.t K Sort V) :
    Egraph.enode K Sort V -> EggTerm.t K Sort V -> Prop :=
  | node_rep_var : forall s v, node_represents g (Egraph.NVar s v) (EggTerm.Var s v)
  | node_rep_app : forall s op cs args, Forall2 (represents g) cs args ->
      node_represents g (Egraph.NApp s op cs) (EggTerm.App s op args).

Local Lemma node_witness g n :
  wf g -> node_typed g n -> exists e, node_represents g n e.
Proof.
  intros Hwf Htyped; destruct n as [s v|s op cs].
  - exists (EggTerm.Var s v); constructor.
  - destruct Htyped as [ss [Hss Hshape]].
    assert (Hchildren : exists es, Forall2 (represents g) cs es).
    { clear Hshape; induction Hss as [|c s' cs ss Hsort Hrest [es Hes]].
      - exists []; constructor.
      - destruct (proj1 (sort_allocated g c) (ex_intro _ s' Hsort)) as [n Hnode].
        destruct (finite_witness g Hwf c n Hnode) as [e He].
        exists (e :: es); constructor; assumption. }
    destruct Hchildren as [es Hes]; exists (EggTerm.App s op es); constructor; exact Hes.
Qed.

Local Lemma allocate_represents g n key e :
  wf g -> node_represents g n e ->
  represents (snd (Egraph.allocate a g n key)) (Egraph.next g) e.
Proof.
  intros Hwf Hrep.
  assert (Hnode : nodes_get (snd (Egraph.allocate a g n key)) (Egraph.next g) = Some n).
  { rewrite allocate_lookup by exact Hwf; destruct (Pos.eq_dec _ _); congruence. }
  destruct Hrep as [s v|s op cs es Hargs].
  - apply (rep_var _ (Egraph.next g) (Egraph.next g) s v); [reflexivity|exact Hnode].
  - apply (rep_app _ (Egraph.next g) (Egraph.next g) s op cs es);
      [reflexivity|exact Hnode|].
    pose proof (proj1 (allocate_preserves g (Egraph.NApp s op cs) key Hwf)) as Hext.
    set (h := snd (Egraph.allocate a g (Egraph.NApp s op cs) key)) in *.
    clearbody h; clear Hnode; induction Hargs; constructor; auto.
Qed.

Local Lemma allocate_wf g n :
  wf g -> node_typed g n -> wf (snd (Egraph.allocate a g n (Egraph.node_code a n))).
Proof.
  intros Hwf Htyped; set (key := Egraph.node_code a n).
  set (h := snd (Egraph.allocate a g n key)).
  destruct (allocate_preserves g n key Hwf) as [Hrep Hmono].
  constructor.
  - unfold h; rewrite allocate_equation; cbn [snd Egraph.uf].
    apply UnionFind.wf_union; [exact id_laws|exact (forest_wf g Hwf)].
  - unfold h; rewrite allocate_equation; cbn [snd Egraph.nodes].
    apply Map.wf_set; exact (nodes_wf g Hwf).
  - unfold h; rewrite allocate_equation; cbn [snd Egraph.memo].
    apply Map.wf_set; exact (memo_wf g Hwf).
  - intros c; unfold h; rewrite allocate_lookup by exact Hwf.
    rewrite allocate_equation; cbn [snd Egraph.next].
    destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
    + split; [intros _; lia|intros _; eauto].
    + rewrite (allocation g Hwf c); lia.
  - intros c Hin; unfold h in Hin |- *; rewrite allocate_equation in Hin |- *.
    cbn [snd Egraph.uf Egraph.next] in *.
    apply (UnionFind.keys_union Egraph.id_encoding id_laws _ _ _ c
      (forest_wf g Hwf)) in Hin.
    destruct Hin as [->|[->|Hin]]; try lia.
    pose proof (forest_domain g Hwf c Hin); lia.
  - intros c d sc sd Hsame Hc Hd.
    change (same_class (snd (Egraph.allocate a g n key)) c d) in Hsame.
    apply (proj1 (allocate_classes g n key Hwf c d)) in Hsame.
    rewrite !sort_of_equation in Hc, Hd.
    unfold h in Hc, Hd; rewrite !allocate_lookup in Hc, Hd by exact Hwf.
    destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hcne].
    + pose proof (fresh_singleton g d Hwf Hsame) as Heq; subst d.
      destruct (Pos.eq_dec (Egraph.next g) (Egraph.next g)); congruence.
    + destruct (Pos.eq_dec d (Egraph.next g)) as [->|Hdne].
      * assert (Hsame' : same_class g (Egraph.next g) c) by (symmetry; exact Hsame).
        pose proof (fresh_singleton g c Hwf Hsame'); contradiction.
      * apply (class_sorts g Hwf c d sc sd Hsame);
          rewrite sort_of_equation; assumption.
  - intros c m Hnode; unfold h in Hnode |- *.
    rewrite allocate_lookup in Hnode by exact Hwf.
    apply (node_typed_mono g _ m (fun c s => allocate_old_sort g n key c s Hwf)).
    destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
    + injection Hnode as <-; exact Htyped.
    + exact (nodes_typed g Hwf c m Hnode).
  - intros c m Hnode; unfold h in Hnode |- *.
    rewrite allocate_lookup in Hnode by exact Hwf.
    destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
    + destruct (node_witness g n Hwf Htyped) as [e He].
      exists e; exact (allocate_represents g n key e Hwf He).
    + destruct (finite_witness g Hwf c m Hnode) as [e He].
      exists e; exact (Hrep c e He).
  - intros k c Hget; unfold h in Hget |- *.
    rewrite allocate_equation in Hget; cbn [snd Egraph.memo] in Hget.
    destruct (Pos.eq_dec k key) as [->|Hne].
    + rewrite Map.get_set_same in Hget by exact (memo_wf g Hwf).
      injection Hget as <-; exists (Egraph.next g), n, n.
      split.
      * rewrite allocate_lookup by exact Hwf; destruct (Pos.eq_dec _ _); congruence.
      * split; [reflexivity|split; reflexivity].
    + rewrite (Map.get_set_other _ id_laws) in Hget
        by (try exact Hne; exact (memo_wf g Hwf)).
      destruct (memo_correct g Hwf k c Hget)
        as [i [m [old [Hnode [Hsame [Hcode Hcanon]]]]]].
      exists i, m, old; split; [exact (allocate_old_lookup g n key i m Hwf Hnode)|].
      split; [apply Hmono; exact Hsame|].
      split; [exact Hcode|exact (canonical_mono g _ old m Hmono Hcanon)].
Qed.

Local Lemma add_node_equation g n :
  Egraph.add_node a g n =
    if Egraph.node_valid a g n then
      match Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
        (Egraph.memo g) with
      | Some c => Some (Egraph.find a g c, g)
      | None => Some (Egraph.allocate a g (Egraph.canonical a g n)
        (Egraph.node_code a (Egraph.canonical a g n)))
      end
    else None.
Proof.
  unfold Egraph.add_node, Egraph.add_node_c; rewrite Cost.value_bind.
  fold (Egraph.node_valid a g n); destruct (Egraph.node_valid a g n); [|reflexivity].
  rewrite !Cost.value_bind.
  fold (Egraph.canonical a g n) (Egraph.node_code a (Egraph.canonical a g n)).
  fold (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g)).
  destruct (Map.get _ _ _); reflexivity.
Qed.

(** Successful node insertion preserves WF, including finite witnesses for new classes. *)
Theorem add_node_wf g n c h :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) -> wf h.
Proof.
  intros Hl Hwf; rewrite add_node_equation.
  destruct (Egraph.node_valid a g n) eqn:Hvalid; [|discriminate].
  destruct (Map.get _ _ _) as [d|] eqn:Hhit.
  - intro Heq; injection Heq as <- <-; exact Hwf.
  - rewrite allocate_equation; intro Heq; injection Heq as Hc Hh; subst c h.
    change (wf (snd (Egraph.allocate a g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n))))).
    apply allocate_wf; [exact Hwf|].
    apply canonical_typed; [exact Hwf|apply (proj1 (node_valid_spec g n Hl)); exact Hvalid].
Qed.

(** Successful node insertion keeps every old represented term and class equality. *)
Theorem add_node_preserves g n c h :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) ->
  (forall d e, represents g d e -> represents h d e) /\
  (forall d e, same_class g d e -> same_class h d e).
Proof.
  intros Hl Hwf; rewrite add_node_equation.
  destruct (Egraph.node_valid a g n); [|discriminate].
  destruct (Map.get _ _ _) as [d|].
  - intro Heq; injection Heq as <- <-; split; auto.
  - rewrite allocate_equation; intro Heq; injection Heq as Hc Hh; subst c h.
    exact (allocate_preserves g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n)) Hwf).
Qed.

Local Lemma node_represents_canonical g n e :
  wf g -> node_represents g n e -> node_represents g (Egraph.canonical a g n) e.
Proof.
  intros Hwf Hrep; destruct Hrep as [s v|s op cs es Hargs]; rewrite canonical_equation.
  - constructor.
  - constructor; induction Hargs as [|c e cs es He Hrest IH]; cbn [map].
    + constructor.
    + constructor.
      * apply (represents_same g c (Egraph.find a g c) e); [|exact He].
        unfold same_class; symmetry; exact (find_idem g c Hwf).
      * exact IH.
Qed.

Local Lemma node_represents_congruent g n m e :
  Egraph.canonical a g n = Egraph.canonical a g m ->
  node_represents g n e -> node_represents g m e.
Proof.
  intros Hcanon Hrep.
  destruct Hrep as [s v|s op cs es Hargs]; destruct m as [s' v'|s' op' ds];
    rewrite !canonical_equation in Hcanon; try discriminate.
  - injection Hcanon as <- <-; constructor.
  - injection Hcanon as Hs Hop Hcs; subst s' op'; constructor.
    revert ds Hcs.
    induction Hargs as [|c e cs es He Hrest IH]; intros [|d ds] Hcs;
      cbn in Hcs; try discriminate; [constructor|].
    injection Hcs as Hcd Hds; constructor.
    + exact (represents_same g c d e Hcd He).
    + exact (IH _ Hds).
Qed.

Local Lemma stored_represents g i n c e :
  nodes_get g i = Some n -> same_class g i c ->
  node_represents g n e -> represents g c e.
Proof.
  intros Hnode Hclass Hrep; destruct Hrep.
  - eapply rep_var; eassumption.
  - eapply rep_app; eassumption.
Qed.

(** Successful insertion represents every finite term supplied by the node's children. *)
Theorem add_node_represents g n c h e :
  encoding_laws -> wf g -> Egraph.add_node a g n = Some (c, h) ->
  node_represents g n e -> represents h c e.
Proof.
  intros Hl Hwf; rewrite add_node_equation.
  destruct (Egraph.node_valid a g n); [|discriminate].
  destruct (Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
    (Egraph.memo g)) as [d|] eqn:Hhit.
  - intros Heq Hrep; injection Heq as <- <-.
    destruct (memo_correct g Hwf _ d Hhit)
      as [i [m [old [Hnode [Hsame [Hcode Hcanon]]]]]].
    apply (node_code_injective Hl) in Hcode; subst old.
    assert (Hmatching : Egraph.canonical a g n = Egraph.canonical a g m).
    { rewrite <- (canonical_idem g n Hwf); exact Hcanon. }
    apply (stored_represents g i m (Egraph.find a g d) e Hnode).
    + unfold same_class in *; rewrite find_idem by exact Hwf; exact Hsame.
    + exact (node_represents_congruent g n m e Hmatching Hrep).
  - rewrite allocate_equation; intros Heq Hrep; injection Heq as Hc Hh; subst c h.
    apply (allocate_represents g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n)) e Hwf).
    exact (node_represents_canonical g n e Hwf Hrep).
Qed.

(** A clean graph reuses the existing canonical class without changing its state. *)
Theorem add_node_hashcons g n i m c h :
  encoding_laws -> clean g -> node_typed g n -> nodes_get g i = Some m ->
  Egraph.canonical a g n = Egraph.canonical a g m ->
  Egraph.add_node a g n = Some (c, h) -> h = g /\ same_class g c i.
Proof.
  intros Hl Hclean Htyped Hnode Hcanon.
  destruct (memo_complete g Hclean i m Hnode) as [d [Hhit Hsame]].
  rewrite add_node_equation.
  rewrite (proj2 (node_valid_spec g n Hl) Htyped), Hcanon, Hhit.
  intro Heq; injection Heq as <- <-; split; [reflexivity|].
  unfold same_class in *; rewrite find_idem by exact (clean_wf g Hclean).
  symmetry; exact Hsame.
Qed.

Local Lemma add_node_total g n :
  encoding_laws -> node_typed g n -> exists c h, Egraph.add_node a g n = Some (c, h).
Proof.
  intros Hl Htyped; rewrite add_node_equation, (proj2 (node_valid_spec g n Hl) Htyped).
  destruct (Map.get _ _ _).
  - eauto.
  - destruct (Egraph.allocate a g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n))) as [c h]; eauto.
Qed.

Local Lemma add_term_equation g e :
  Egraph.add_term a g e =
    match e with
    | EggTerm.Var s v => Egraph.add_node a g (Egraph.NVar s v)
    | EggTerm.App s op es =>
      match Egraph.add_terms a g es with
      | None => None
      | Some (cs, h) => Egraph.add_node a h (Egraph.NApp s op cs)
      end
    end.
Proof.
  destruct e; [reflexivity|].
  change (Cost.value (Cost.step ;;
    let* result := Egraph.add_terms_c a g args in
    match result with
    | Some (cs, h) => Egraph.add_node_c a h (Egraph.NApp s op cs)
    | None => Cost.ret None
    end) =
    match Egraph.add_terms a g args with
    | Some (cs, h) => Egraph.add_node a h (Egraph.NApp s op cs)
    | None => None
    end).
  rewrite !Cost.value_bind.
  fold (Egraph.add_terms a g args).
  destruct (Egraph.add_terms a g args) as [[cs h]|]; reflexivity.
Qed.

Local Lemma add_terms_equation g es :
  Egraph.add_terms a g es =
    match es with
    | [] => Some ([], g)
    | e :: es =>
      match Egraph.add_term a g e with
      | None => None
      | Some (c, h) =>
        option_map (fun result => (c :: fst result, snd result)) (Egraph.add_terms a h es)
      end
    end.
Proof.
  destruct es as [|e es]; [reflexivity|].
  change (Cost.value (Cost.step ;;
    let* result := Egraph.add_term_c a g e in
    match result with
    | None => Cost.ret None
    | Some (c, h) =>
      let* result := Egraph.add_terms_c a h es in
      Cost.ret (option_map (fun result => (c :: fst result, snd result)) result)
    end) =
    match Egraph.add_term a g e with
    | None => None
    | Some (c, h) =>
      option_map (fun result => (c :: fst result, snd result)) (Egraph.add_terms a h es)
    end).
  rewrite !Cost.value_bind.
  fold (Egraph.add_term a g e).
  destruct (Egraph.add_term a g e) as [[c h]|]; reflexivity.
Qed.

(** Extensions retain finite representations and old class equalities. *)
Definition extends (g h : Egraph.t K Sort V) : Prop :=
  (forall c e, represents g c e -> represents h c e) /\
  (forall c d, same_class g c d -> same_class h c d).

Local Lemma extends_trans g h j : extends g h -> extends h j -> extends g j.
Proof.
  intros [Hgh Hcgh] [Hhj Hchj]; split; eauto.
Qed.

Local Lemma args_preserved g h cs es :
  extends g h -> Forall2 (represents g) cs es -> Forall2 (represents h) cs es.
Proof.
  intros [Hrep Hsame] Hargs; induction Hargs; constructor; auto.
Qed.

Local Lemma terms_sort g cs es :
  wf g -> Forall2 (represents g) cs es ->
  Forall2 (fun c s => Egraph.sort_of a g c = Some s) cs (map EggTerm.sort_of es).
Proof.
  intros Hwf Hargs; induction Hargs; cbn [map]; constructor; auto using represents_sort.
Qed.

Local Lemma term_ind_all (P : EggTerm.t K Sort V -> Prop)
    (Hvar : forall s v, P (EggTerm.Var s v))
    (Happ : forall s op es, Forall P es -> P (EggTerm.App s op es)) :
  forall e, P e.
Proof.
  fix IH 1; intros [s v|s op es].
  - apply Hvar.
  - apply Happ; induction es; constructor; auto.
Qed.

Local Lemma add_terms_correct es :
  Forall (fun e => forall g, wf g ->
    (forall c h, Egraph.add_term a g e = Some (c, h) ->
      wf h /\ represents h c e /\ extends g h) /\
    (EggTerm.typed a e -> exists c h, Egraph.add_term a g e = Some (c, h))) es ->
  forall g, wf g ->
    (forall cs h, Egraph.add_terms a g es = Some (cs, h) ->
      wf h /\ Forall2 (represents h) cs es /\ extends g h) /\
    (Forall (EggTerm.typed a) es -> exists cs h, Egraph.add_terms a g es = Some (cs, h)).
Proof.
  intro Hchildren; induction Hchildren as [|e es He Hrest IH]; intros g Hwf.
  - rewrite add_terms_equation; split.
    + intros cs h Heq; injection Heq as <- <-; split; [exact Hwf|].
      split; [constructor|split; auto].
    + intros _; eauto.
  - split.
    + intros cs h; rewrite add_terms_equation.
      destruct (Egraph.add_term a g e) as [[c j]|] eqn:Heq; [|discriminate].
      destruct (proj1 (He g Hwf) c j Heq) as [Hj [Hrep Hext]].
      destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Hes; [|discriminate].
      intros Hresult; injection Hresult as <- <-.
      destruct (proj1 (IH j Hj) ds k Hes) as [Hk [Hreps Hext']].
      split; [exact Hk|]; split.
      * constructor; [exact (proj1 Hext' c e Hrep)|exact Hreps].
      * exact (extends_trans g j k Hext Hext').
    + intros Htyped; inversion Htyped as [|e' es' Hte Htes]; subst.
      destruct (proj2 (He g Hwf) Hte) as [c [j Heq]].
      destruct (proj1 (He g Hwf) c j Heq) as [Hj _].
      destruct (proj2 (IH j Hj) Htes) as [cs [k Hcs]].
      exists (c :: cs), k; rewrite add_terms_equation, Heq, Hcs; reflexivity.
Qed.

Local Lemma add_term_correct :
  encoding_laws -> forall e g, wf g ->
    (forall c h, Egraph.add_term a g e = Some (c, h) ->
      wf h /\ represents h c e /\ extends g h) /\
    (EggTerm.typed a e -> exists c h, Egraph.add_term a g e = Some (c, h)).
Proof.
  intros Hl; apply (term_ind_all (fun e => forall g, wf g ->
    (forall c h, Egraph.add_term a g e = Some (c, h) ->
      wf h /\ represents h c e /\ extends g h) /\
    (EggTerm.typed a e -> exists c h, Egraph.add_term a g e = Some (c, h)))).
  - intros s v g Hwf; rewrite add_term_equation; split.
    + intros c h Hadded; split; [eapply add_node_wf; eassumption|]; split.
      * eapply add_node_represents; [exact Hl|exact Hwf|exact Hadded|constructor].
      * exact (add_node_preserves g _ c h Hl Hwf Hadded).
    + intro Htyped; inversion Htyped as [s' v' Hsort|]; subst.
      apply add_node_total; [exact Hl|exact Hsort].
  - intros s op es IH g Hwf; split.
    + intros c h; rewrite add_term_equation.
      destruct (Egraph.add_terms a g es) as [[cs j]|] eqn:Hargs; [|discriminate].
      intro Hadded.
      destruct (proj1 (add_terms_correct es IH g Hwf) cs j Hargs) as [Hj [Hreps Hext]].
      split; [eapply add_node_wf; eassumption|]; split.
      * eapply add_node_represents; [exact Hl|exact Hj|exact Hadded|constructor; exact Hreps].
      * apply (extends_trans g j h Hext).
        exact (add_node_preserves j _ c h Hl Hj Hadded).
    + intro Htyped; inversion Htyped as [|s' op' es' Htes Hshape]; subst.
      destruct (proj2 (add_terms_correct es IH g Hwf) Htes) as [cs [j Hargs]].
      destruct (proj1 (add_terms_correct es IH g Hwf) cs j Hargs) as [Hj [Hreps Hext]].
      destruct (add_node_total j (Egraph.NApp s op cs) Hl
        (ex_intro _ (map EggTerm.sort_of es) (conj (terms_sort j cs es Hj Hreps) Hshape)))
        as [c [h Hadded]].
      exists c, h; rewrite add_term_equation, Hargs; exact Hadded.
Qed.

(** Successful term insertion represents its input, and every typed input can be inserted. *)
Theorem add_term_represents g e :
  encoding_laws -> wf g ->
  (forall c h, Egraph.add_term a g e = Some (c, h) ->
    represents h c e /\ wf h /\ extends g h) /\
  (EggTerm.typed a e -> exists c h, Egraph.add_term a g e = Some (c, h)).
Proof.
  intros Hl Hwf; destruct (add_term_correct Hl e g Hwf) as [Hsuccess Htotal].
  split; [|exact Htotal]; intros c h Hadded.
  destruct (Hsuccess c h Hadded) as [Hh [Hrep Hext]]; auto.
Qed.

Local Lemma observed_node g key c :
  wf g ->
  In (key, c) (rev (map (EggIndex.observe a g) (Map.elements (Egraph.nodes g)))) <->
  exists i n, nodes_get g i = Some n /\
    Egraph.node_code a (Egraph.canonical a g n) = key /\ Egraph.find a g i = c.
Proof.
  intro Hwf; rewrite <- in_rev, in_map_iff; split.
  - intros [[i n] [Heq Hin]]; exists i, n.
    apply (Map.elements_spec Egraph.id_encoding id_laws _ _ _ (nodes_wf g Hwf)) in Hin.
    split; [exact Hin|unfold EggIndex.observe in Heq; cbn [fst snd] in Heq; split; congruence].
  - intros [i [n [Hnode [Hkey Hclass]]]]; exists (i, n); split.
    + unfold EggIndex.observe; cbn [fst snd]; congruence.
    + apply (Map.elements_spec Egraph.id_encoding id_laws _ _ _ (nodes_wf g Hwf)); exact Hnode.
Qed.

Local Definition reindex g :=
  Egraph.Make K Sort V (Egraph.uf g) (Egraph.nodes g) (fst (Egraph.scan a g))
    (Egraph.next g) (Egraph.private g).

Local Lemma reindex_represents g c e :
  represents (reindex g) c e <-> represents g c e.
Proof.
  split; apply represents_mono; intros; assumption.
Qed.

Local Lemma reindex_wf g : wf g -> wf (reindex g).
Proof.
  intro Hwf; constructor; try exact (forest_wf g Hwf); try exact (nodes_wf g Hwf).
  - exact (EggIndex.table_wf _ _ _ (EggIndex.graph_scan_correct a g)).
  - exact (allocation g Hwf).
  - exact (forest_domain g Hwf).
  - exact (class_sorts g Hwf).
  - exact (nodes_typed g Hwf).
  - intros c n Hnode; destruct (finite_witness g Hwf c n Hnode) as [e He].
    exists e; apply reindex_represents; exact He.
  - intros key c Hhit.
    pose proof (EggIndex.table_sound _ _ _ (EggIndex.graph_scan_correct a g) key c Hhit)
      as Hseen.
    apply (proj1 (observed_node g key c Hwf)) in Hseen.
    destruct Hseen as [i [n [Hnode [Hkey Hclass]]]].
    exists i, n, (Egraph.canonical a g n); split; [exact Hnode|].
    split; [change (same_class g i c); unfold same_class; rewrite <- Hclass;
      symmetry; apply find_idem; exact Hwf|].
    split; [exact Hkey|change
      (Egraph.canonical a g (Egraph.canonical a g n) = Egraph.canonical a g n);
      apply canonical_idem; exact Hwf].
Qed.

Local Lemma scan_clean g :
  wf g -> snd (Egraph.scan a g) = None -> clean (reindex g).
Proof.
  intros Hwf Hnone; pose proof (EggIndex.graph_scan_correct a g) as Hscan.
  assert (Hlookup : forall i n, nodes_get g i = Some n ->
    Map.get Egraph.id_encoding (Egraph.node_code a (Egraph.canonical a g n))
      (fst (Egraph.scan a g)) = Some (Egraph.find a g i)).
  { intros i n Hnode; apply (EggIndex.no_collision _ _ _ Hscan Hnone).
    apply (proj2 (observed_node g _ _ Hwf)); exists i, n; auto. }
  constructor.
  - exact (reindex_wf g Hwf).
  - intros i j n m Hi Hj Hcanon.
    pose proof (Hlookup i n Hi) as Hleft; pose proof (Hlookup j m Hj) as Hright.
    change (Egraph.canonical a g n = Egraph.canonical a g m) in Hcanon.
    rewrite Hcanon in Hleft.
    change (Egraph.find a g i = Egraph.find a g j); congruence.
  - intros key c Hhit.
    pose proof (EggIndex.table_sound _ _ _ Hscan key c Hhit) as Hseen.
    apply (proj1 (observed_node g key c Hwf)) in Hseen.
    destruct Hseen as [i [n [Hnode [Hkey Hclass]]]]; exists i, n.
    split; [exact Hnode|]; split; [|exact Hkey].
    change (same_class g i c); unfold same_class; rewrite <- Hclass.
    symmetry; apply find_idem; exact Hwf.
  - intros i n Hnode; exists (Egraph.find a g i).
    split; [exact (Hlookup i n Hnode)|].
    change (same_class g i (Egraph.find a g i)).
    unfold same_class; symmetry; apply find_idem; exact Hwf.
Qed.

Local Lemma scan_pair g c d :
  encoding_laws -> wf g -> snd (Egraph.scan a g) = Some (c, d) ->
  c <> d /\ exists i n j m, nodes_get g i = Some n /\ nodes_get g j = Some m /\
    Egraph.find a g i = c /\ Egraph.find a g j = d /\
    Egraph.canonical a g n = Egraph.canonical a g m.
Proof.
  intros Hl Hwf Hcollision.
  destruct (EggIndex.collision_sound _ _ _ (EggIndex.graph_scan_correct a g) c d Hcollision)
    as [Hne [key [Hc Hd]]].
  apply (proj1 (observed_node g key c Hwf)) in Hc.
  apply (proj1 (observed_node g key d Hwf)) in Hd.
  destruct Hc as [i [n [Hi [Hkey Hclass]]]], Hd as [j [m [Hj [Hkey' Hclass']]]].
  split; [exact Hne|]; exists i, n, j, m; repeat split; try assumption.
  apply (node_code_injective Hl); congruence.
Qed.

Local Lemma scan_union g c d :
  encoding_laws -> wf g -> snd (Egraph.scan a g) = Some (c, d) ->
  exists h, Egraph.union a (reindex g) c d = Some h.
Proof.
  intros Hl Hwf Hcollision.
  destruct (scan_pair g c d Hl Hwf Hcollision)
    as [Hne [i [n [j [m [Hi [Hj [Hc [Hd Hcanon]]]]]]]]].
  assert (Hsort : Egraph.node_sort n = Egraph.node_sort m).
  { destruct n, m; rewrite !canonical_equation in Hcanon; inversion Hcanon; reflexivity. }
  assert (Hsc : Egraph.sort_of a g c = Some (Egraph.node_sort n)).
  { rewrite <- Hc; apply root_sort; [exact Hwf|rewrite sort_of_equation, Hi; reflexivity]. }
  assert (Hsd : Egraph.sort_of a g d = Some (Egraph.node_sort n)).
  { rewrite Hsort, <- Hd; apply root_sort; [exact Hwf|rewrite sort_of_equation, Hj; reflexivity]. }
  change (Egraph.sort_of a (reindex g) c = Some (Egraph.node_sort n)) in Hsc.
  change (Egraph.sort_of a (reindex g) d = Some (Egraph.node_sort n)) in Hsd.
  rewrite union_equation, Hsc, Hsd.
  rewrite (proj2 (Map.code_compare_eq _ _) eq_refl); eauto.
Qed.

Local Lemma congruent_sound {H F C} adm (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) g c d :
  encoding_laws -> wf g -> sound adm facts rules g ->
  snd (Egraph.scan a g) = Some (c, d) ->
  forall t u, represents (reindex g) c t -> represents (reindex g) d u ->
    EggEqual.rel a adm facts rules t u.
Proof.
  intros Hl Hwf Hsound Hcollision t u Ht Hu.
  apply (proj1 (reindex_represents g c t)) in Ht.
  apply (proj1 (reindex_represents g d u)) in Hu.
  destruct (scan_pair g c d Hl Hwf Hcollision)
    as [Hne [i [n [j [m [Hi [Hj [Hc [Hd Hcanon]]]]]]]]].
  destruct (node_witness g n Hwf (nodes_typed g Hwf i n Hi)) as [e He].
  assert (Hec : represents g c e).
  { apply (stored_represents g i n c e Hi); [unfold same_class; rewrite <- Hc;
      symmetry; apply find_idem; exact Hwf|exact He]. }
  assert (Hed : represents g d e).
  { apply (stored_represents g j m d e Hj); [unfold same_class; rewrite <- Hd;
      symmetry; apply find_idem; exact Hwf|].
    exact (node_represents_congruent g n m e Hcanon He). }
  eapply EggEqual.trans; [exact (Hsound c t e Ht Hec)|exact (Hsound d e u Hed Hu)].
Qed.

Local Lemma rebuild_step_equation g :
  Cost.value (Egraph.rebuild_step_c a g) =
    match snd (Egraph.scan a g) with
    | None => inr (reindex g)
    | Some (c, d) =>
      match Egraph.union a (reindex g) c d with
      | Some h => inl h
      | None => inr (reindex g)
      end
    end.
Proof.
  unfold Egraph.rebuild_step_c; rewrite Cost.value_bind; fold (Egraph.scan a g).
  unfold reindex; destruct (Egraph.scan a g) as [table [[c d]|]]; [|reflexivity].
  cbn [fst snd].
  rewrite Cost.value_bind; fold (Egraph.union a
    (Egraph.Make K Sort V (Egraph.uf g) (Egraph.nodes g) table (Egraph.next g)
      (Egraph.private g)) c d).
  destruct (Egraph.union _ _ _ _); reflexivity.
Qed.

Local Lemma rebuild_correct g :
  encoding_laws -> wf g ->
  clean (Egraph.rebuild a g) /\ extends g (Egraph.rebuild a g) /\
  (forall H F C adm (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)),
    sound adm facts rules g -> sound adm facts rules (Egraph.rebuild a g)).
Proof.
  intros Hl Hwf.
  set (ids := map fst (Map.elements (Egraph.nodes g))).
  set (measure := fun h => EggIndex.missing (Egraph.find a h) ids).
  set (I := fun h => wf h /\ Egraph.nodes h = Egraph.nodes g /\ extends g h /\
    forall H F C adm (facts : EggFact.t F K Sort V C)
      (rules : list (EggRule.t K Sort V H F)), sound adm facts rules g -> sound adm facts rules h).
  assert (Hinitial : I g).
  { unfold I; split; [exact Hwf|]; split; [reflexivity|]; split; [split; auto|auto]. }
  assert (Hstep : forall h, I h ->
    match Cost.value (Egraph.rebuild_step_c a h) with
    | inl j => I j /\ (measure j < measure h)%nat
    | inr j => I j /\ clean j
    end).
  { intros h [Hh [Hnodes [Hext Hsound]]]; rewrite rebuild_step_equation.
    assert (Hrext : extends g (reindex h)).
    { destruct Hext as [Hrep Hsame]; split.
      - intros c e He; apply reindex_represents, Hrep, He.
      - exact Hsame. }
    assert (Hrsound : forall H F C adm (facts : EggFact.t F K Sort V C)
      (rules : list (EggRule.t K Sort V H F)),
      sound adm facts rules g -> sound adm facts rules (reindex h)).
    { intros H F C adm facts rules Hsg c t u Ht Hu.
      apply (Hsound H F C adm facts rules Hsg c t u);
        apply reindex_represents; assumption. }
    destruct (snd (Egraph.scan a h)) as [[c d]|] eqn:Hcollision.
    - destruct (scan_union h c d Hl Hh Hcollision) as [j Hunion]; rewrite Hunion.
      destruct (union_preserves (reindex h) c d j Hl (reindex_wf h Hh) Hunion)
        as [Hrep Hmono].
      assert (Hnew : wf j) by (eapply union_wf; [exact Hl|apply reindex_wf; exact Hh|exact Hunion]).
      split.
      + unfold I; split; [exact Hnew|]; split.
        * destruct (union_inv _ _ _ _ Hl Hunion) as [s [Hc [Hd ->]]]; exact Hnodes.
        * split; [exact (extends_trans g (reindex h) j Hrext (conj Hrep Hmono))|].
          intros H F C adm facts rules Hsg.
          apply (union_sound adm facts rules (reindex h) c d j Hl (reindex_wf h Hh)).
          -- exact (Hrsound H F C adm facts rules Hsg).
          -- apply congruent_sound; [exact Hl|exact Hh|apply Hsound; exact Hsg|exact Hcollision].
          -- exact Hunion.
      + destruct (scan_pair h c d Hl Hh Hcollision)
          as [Hne [i [n [k [m [Hi [Hk [Hc [Hd Hcanon]]]]]]]]].
        unfold measure; apply (EggIndex.missing_decreases _ _ ids i k).
        * unfold ids; apply in_map_iff; exists (i, n); split; [reflexivity|].
          apply (Map.elements_spec Egraph.id_encoding id_laws); [exact (nodes_wf g Hwf)|].
          change (Map.get Egraph.id_encoding i (Egraph.nodes g) = Some n).
          rewrite <- Hnodes; exact Hi.
        * unfold ids; apply in_map_iff; exists (k, m); split; [reflexivity|].
          apply (Map.elements_spec Egraph.id_encoding id_laws); [exact (nodes_wf g Hwf)|].
          change (Map.get Egraph.id_encoding k (Egraph.nodes g) = Some m).
          rewrite <- Hnodes; exact Hk.
        * congruence.
        * pose proof (union_same (reindex h) c d j Hl (reindex_wf h Hh) Hunion) as Hcd.
          assert (Hic : same_class (reindex h) i c).
          { change (same_class h i c); unfold same_class; rewrite <- Hc.
            symmetry; apply find_idem; exact Hh. }
          assert (Hkd : same_class (reindex h) k d).
          { change (same_class h k d); unfold same_class; rewrite <- Hd.
            symmetry; apply find_idem; exact Hh. }
          specialize (Hmono _ _ Hic); pose proof
            (proj2 (union_preserves _ _ _ _ Hl (reindex_wf h Hh) Hunion) _ _ Hkd) as Hkd'.
          unfold same_class in *; congruence.
        * exact Hmono.
    - split; [|exact (scan_clean h Hh Hcollision)].
      unfold I; split; [apply reindex_wf; exact Hh|]; split; [exact Hnodes|].
      split; assumption. }
  set (fuel := Pos.mul (Pos.of_succ_nat (Map.size (Egraph.nodes g)))
    (Pos.of_succ_nat (Map.size (Egraph.nodes g)))).
  assert (Hfuel : (measure g < Pos.to_nat fuel)%nat).
  { pose proof (EggIndex.missing_bound (Egraph.find a g) ids).
    unfold measure, fuel; rewrite Pos2Nat.inj_mul, !SuccNat2Pos.id_succ.
    unfold ids in *; rewrite length_map in *; rewrite Map.size_elements; nia. }
  destruct (EggIndex.iterate_stops (Egraph.rebuild_step_c a) I
    (fun h => I h /\ clean h) measure fuel g Hstep Hinitial Hfuel) as [h [Hrun [HI Hclean]]].
  assert (Hresult : Egraph.rebuild a g = h).
  { unfold Egraph.rebuild, Egraph.rebuild_c; rewrite !Cost.value_bind.
    change (Cost.value
      (match Cost.value (iterate (Egraph.rebuild_step_c a) fuel g) with
      | inr j => Cost.ret j
      | inl j => let* result := Egraph.scan_c a j in
        Cost.ret (Egraph.Make K Sort V (Egraph.uf j) (Egraph.nodes j) (fst result)
          (Egraph.next j) (Egraph.private j))
      end) = h).
    rewrite Hrun; reflexivity. }
  rewrite Hresult; destruct HI as [_ [_ [Hext Hsound]]]; auto.
Qed.

(** Rebuilding closes congruence and restores a current complete memo on every WF graph. *)
Theorem rebuild_clean g :
  encoding_laws -> wf g -> clean (Egraph.rebuild a g).
Proof.
  intros Hl Hwf; exact (proj1 (rebuild_correct g Hl Hwf)).
Qed.

(** Rebuilding retains every represented finite term and every old class equality. *)
Theorem rebuild_preserves g :
  encoding_laws -> wf g -> extends g (Egraph.rebuild a g).
Proof.
  intros Hl Hwf; exact (proj1 (proj2 (rebuild_correct g Hl Hwf))).
Qed.

(** Congruence rebuilding preserves generated equality soundness without rule-soundness premises. *)
Theorem rebuild_sound {H F C} adm (facts : EggFact.t F K Sort V C)
    (rules : list (EggRule.t K Sort V H F)) g :
  encoding_laws -> wf g -> sound adm facts rules g ->
  sound adm facts rules (Egraph.rebuild a g).
Proof.
  intros Hl Hwf; exact (proj2 (proj2 (rebuild_correct g Hl Hwf)) H F C adm facts rules).
Qed.

(** Rebuilding a clean graph keeps every class equality, including unknown singleton IDs. *)
Theorem rebuild_idle g :
  encoding_laws -> clean g -> same_class_equal g (Egraph.rebuild a g).
Proof.
  intros Hl Hclean; pose proof (clean_wf g Hclean) as Hwf.
  assert (Hnone : snd (Egraph.scan a g) = None).
  { destruct (snd (Egraph.scan a g)) as [[c d]|] eqn:Hcollision; [|reflexivity].
    destruct (scan_pair g c d Hl Hwf Hcollision)
      as [Hne [i [n [j [m [Hi [Hj [Hc [Hd Hcanon]]]]]]]]].
    pose proof (congruence_closed g Hclean i j n m Hi Hj Hcanon); unfold same_class in *.
    exfalso; apply Hne; congruence. }
  assert (Hstep : Cost.value (Egraph.rebuild_step_c a g) = inr (reindex g)).
  { rewrite rebuild_step_equation, Hnone; reflexivity. }
  pose proof (EggIndex.iterate_immediate (Egraph.rebuild_step_c a)
    (Pos.mul (Pos.of_succ_nat (Map.size (Egraph.nodes g)))
      (Pos.of_succ_nat (Map.size (Egraph.nodes g)))) g (reindex g) Hstep) as Hrun.
  assert (Hresult : Egraph.rebuild a g = reindex g).
  { unfold Egraph.rebuild, Egraph.rebuild_c; rewrite !Cost.value_bind.
    fold (Map.size (Egraph.nodes g)).
    change (Cost.value
      (match Cost.value (iterate (Egraph.rebuild_step_c a)
        (Pos.mul (Pos.of_succ_nat (Map.size (Egraph.nodes g)))
          (Pos.of_succ_nat (Map.size (Egraph.nodes g)))) g) with
      | inr j => Cost.ret j
      | inl j => let* result := Egraph.scan_c a j in
        Cost.ret (Egraph.Make K Sort V (Egraph.uf j) (Egraph.nodes j) (fst result)
          (Egraph.next j) (Egraph.private j))
      end) = reindex g).
    rewrite Hrun; reflexivity. }
  rewrite Hresult; intros c d; reflexivity.
Qed.

End Graph.

End EggSpec.
