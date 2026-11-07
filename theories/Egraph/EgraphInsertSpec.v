(** * Sound insertion into e-graphs

    Fresh allocation adds a singleton class whose finite terms come from old child classes.
    For example, inserting f(a) cannot add new terms to a's existing class.
    Builds on: EgraphGraph, EgraphSpec and the public Base forest laws. *)

From Stdlib Require Import List PArith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseUnionFind.
From Galois.Egraph Require Import
  EgraphSyntax EgraphRules EgraphEquality EgraphGraph EgraphSpec.
Import List.ListNotations Cost.Notations EggSpec.

Module EggInsertSpec.

Section Graph.
Context {K Sort V : Type} (a : EggAlg.t K Sort V).

Local Lemma id_laws : BaseEncoding.encoding_laws Egraph.id_encoding.
Proof.
  exact positive_encoding_laws.
Qed.

Local Lemma allocate_equation g n key :
  Egraph.allocate a g n key =
    (Egraph.next g, Egraph.Make K Sort V
      (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g))
      (Map.set Egraph.id_encoding (Egraph.next g) n (Egraph.nodes g))
      (Map.set Egraph.id_encoding key (Egraph.next g) (Egraph.memo g))
      (Pos.succ (Egraph.next g))).
Proof.
  reflexivity.
Qed.

Local Lemma allocate_classes g n key c d :
  wf a g -> (same_class a (snd (Egraph.allocate a g n key)) c d <-> same_class a g c d).
Proof.
  intro Hwf; rewrite allocate_equation.
  change (UnionFind.equiv Egraph.id_encoding
    (UnionFind.union Egraph.id_encoding (Egraph.next g) (Egraph.next g) (Egraph.uf g)) c d <->
    UnionFind.equiv Egraph.id_encoding (Egraph.uf g) c d).
  rewrite (UnionFind.union_equiv Egraph.id_encoding id_laws _ _ _ _ _
    (forest_wf a g Hwf)).
  unfold UnionFind.equiv; intuition congruence.
Qed.

Local Lemma fresh_singleton g c :
  wf a g -> same_class a g (Egraph.next g) c -> c = Egraph.next g.
Proof.
  intros Hwf Hsame.
  apply (UnionFind.keys_support Egraph.id_encoding id_laws (Egraph.uf g) (Egraph.next g) c).
  - exact (forest_wf a g Hwf).
  - intro Hin; pose proof (forest_domain a g Hwf _ Hin); lia.
  - exact Hsame.
Qed.

Local Lemma allocate_lookup g n key c :
  wf a g -> nodes_get (snd (Egraph.allocate a g n key)) c =
    if Pos.eq_dec c (Egraph.next g) then Some n else nodes_get g c.
Proof.
  intro Hwf; rewrite allocate_equation; unfold nodes_get; cbn [snd Egraph.nodes].
  destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
  - apply Map.get_set_same; exact (nodes_wf a g Hwf).
  - apply Map.get_set_other; [exact id_laws|exact (nodes_wf a g Hwf)|exact Hne].
Qed.

(** A fresh node cannot become a production of an old allocated class. *)
Local Lemma allocate_old_node g n key c i m :
  wf a g -> (c < Egraph.next g)%positive ->
  same_class a (snd (Egraph.allocate a g n key)) i c ->
  nodes_get (snd (Egraph.allocate a g n key)) i = Some m ->
  nodes_get g i = Some m /\ same_class a g i c.
Proof.
  intros Hwf Hbound Hclass Hnode.
  apply (proj1 (allocate_classes g n key i c Hwf)) in Hclass.
  rewrite allocate_lookup in Hnode by exact Hwf.
  destruct (Pos.eq_dec i (Egraph.next g)) as [->|Hne].
  - pose proof (fresh_singleton g c Hwf Hclass); subst c; lia.
  - split; assumption.
Qed.

(** The fresh singleton has exactly its new production, even when old classes are cyclic. *)
Local Lemma allocate_new_node g n key i m :
  wf a g ->
  same_class a (snd (Egraph.allocate a g n key)) i (Egraph.next g) ->
  nodes_get (snd (Egraph.allocate a g n key)) i = Some m -> m = n.
Proof.
  intros Hwf Hclass Hnode.
  apply (proj1 (allocate_classes g n key i (Egraph.next g) Hwf)) in Hclass.
  assert (Hi : i = Egraph.next g).
  { apply fresh_singleton; [exact Hwf|symmetry; exact Hclass]. }
  subst i; rewrite allocate_lookup in Hnode by exact Hwf.
  destruct (Pos.eq_dec (Egraph.next g) (Egraph.next g)); congruence.
Qed.

(** This proof-side condition excludes a newly allocated node from its own child list. *)
Local Definition children_known (g : Egraph.t K Sort V) (n : Egraph.enode K Sort V) : Prop :=
  match n with
  | Egraph.NVar _ _ => True
  | Egraph.NApp _ _ cs => Forall (fun c => (c < Egraph.next g)%positive) cs
  end.

Local Lemma sort_known g c s :
  wf a g -> Egraph.sort_of a g c = Some s -> (c < Egraph.next g)%positive.
Proof.
  intros Hwf Hsort; apply (proj1 (allocation a g Hwf c)).
  change (option_map Egraph.node_sort (nodes_get g c) = Some s) in Hsort.
  destruct (nodes_get g c) as [n|] eqn:Hnode; [eauto|discriminate].
Qed.

Local Lemma stored_children_known g i n :
  wf a g -> nodes_get g i = Some n -> children_known g n.
Proof.
  intros Hwf Hnode; pose proof (nodes_typed a g Hwf i n Hnode) as Htyped.
  destruct n as [s v|s op cs]; [exact I|].
  destruct Htyped as [ss [Hsorts Hshape]]; clear Hshape Hnode; cbn [children_known].
  induction Hsorts as [|c s' cs ss Hsort Hrest IH]; constructor.
  - exact (sort_known g c s' Hwf Hsort).
  - exact IH.
Qed.

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
  destruct cs as [|c cs]; [reflexivity|].
  unfold Egraph.child_sorts, Egraph.child_sorts_c.
  rewrite !value_fold_right_c.
  cbn [fold_right]; rewrite Cost.value_bind; reflexivity.
Qed.

Local Lemma child_sorts_known g cs ss :
  wf a g -> Egraph.child_sorts a g cs = Some ss ->
  Forall (fun c => (Egraph.find a g c < Egraph.next g)%positive) cs.
Proof.
  intro Hwf; revert ss; induction cs as [|c cs IH]; intros ss Hsorts.
  - constructor.
  - rewrite child_sorts_equation in Hsorts.
    destruct (Egraph.sort_of a g c) as [s|] eqn:Hsort; [|discriminate].
    destruct (Egraph.child_sorts a g cs) as [ds|] eqn:Hrest; [|discriminate].
    constructor; [exact (find_wf a g c s Hwf Hsort)|exact (IH ds eq_refl)].
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

Local Lemma checked_children_known g n :
  wf a g -> Egraph.node_valid a g n = true ->
  children_known g (Egraph.canonical a g n).
Proof.
  intros Hwf Hvalid; destruct n as [s v|s op cs]; rewrite canonical_equation; [exact I|].
  unfold Egraph.node_valid, Egraph.node_valid_c in Hvalid; rewrite Cost.value_bind in Hvalid.
  fold (Egraph.child_sorts a g cs) in Hvalid.
  destruct (Egraph.child_sorts a g cs) as [ss|] eqn:Hsorts; [|discriminate].
  pose proof (child_sorts_known g cs ss Hwf Hsorts) as Hknown.
  clear Hsorts Hvalid; cbn [children_known].
  induction Hknown as [|c cs Hc Hrest IH]; cbn [map].
  - constructor.
  - constructor; assumption.
Qed.

Local Lemma represents_ind_all g (P : Egraph.id -> EggTerm.t K Sort V -> Prop)
    (Hvar : forall c i s v, same_class a g i c ->
      nodes_get g i = Some (Egraph.NVar s v) -> P c (EggTerm.Var s v))
    (Happ : forall c i s op cs args, same_class a g i c ->
      nodes_get g i = Some (Egraph.NApp s op cs) ->
      Forall2 (represents a g) cs args -> Forall2 P cs args ->
      P c (EggTerm.App s op args)) :
  forall c e, represents a g c e -> P c e.
Proof.
  fix IH 3.
  intros c e Hrep; destruct Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs].
  - exact (Hvar c i s v Hclass Hnode).
  - apply (Happ c i s op cs args Hclass Hnode Hargs).
    clear Hclass Hnode; induction Hargs as [|d e ds es Hrep Hrest IHrest].
    + constructor.
    + constructor; [exact (IH d e Hrep)|exact IHrest].
Qed.

(** New derivations at old identifiers retract to the same old finite terms. *)
Local Lemma allocate_old_represents g n key :
  wf a g -> forall c e, represents a (snd (Egraph.allocate a g n key)) c e ->
  (c < Egraph.next g)%positive -> represents a g c e.
Proof.
  intro Hwf; apply (represents_ind_all (snd (Egraph.allocate a g n key))
    (fun c e => (c < Egraph.next g)%positive -> represents a g c e)).
  - intros c i s v Hclass Hnode Hbound.
    destruct (allocate_old_node g n key c i _ Hwf Hbound Hclass Hnode) as [Hi Hsame].
    exact (rep_var a g c i s v Hsame Hi).
  - intros c i s op cs args Hclass Hnode Hargs IHargs Hbound.
    destruct (allocate_old_node g n key c i _ Hwf Hbound Hclass Hnode) as [Hi Hsame].
    apply (rep_app a g c i s op cs args Hsame Hi).
    pose proof (stored_children_known g i _ Hwf Hi) as Hchildren.
    change (Forall (fun d => (d < Egraph.next g)%positive) cs) in Hchildren.
    clear Hclass Hnode Hargs Hi Hsame Hbound; revert Hchildren.
    induction IHargs as [|d e ds es IHe Hrest IHrest]; intro Hchildren.
    + constructor.
    + inversion Hchildren as [|d' ds' Hd Hds]; subst.
      constructor; [exact (IHe Hd)|exact (IHrest Hds)].
Qed.

Local Lemma guarded_Forall2 {A B} (P Q : A -> B -> Prop) (D : A -> Prop) xs ys :
  Forall2 P xs ys -> Forall D xs ->
  (forall x y, D x -> P x y -> Q x y) -> Forall2 Q xs ys.
Proof.
  intro Hrel; induction Hrel as [|x y xs ys Hxy Hrest IH]; intros Hdomain Himpl.
  - constructor.
  - inversion Hdomain as [|x' xs' Hx Hxs]; subst; constructor.
    + exact (Himpl x y Hx Hxy).
    + exact (IH Hxs Himpl).
Qed.

(** Every finite term of the fresh class uses its production and old child terms. *)
Local Lemma allocate_new_represents g n key e :
  wf a g -> children_known g n ->
  represents a (snd (Egraph.allocate a g n key)) (Egraph.next g) e ->
  node_represents a g n e.
Proof.
  intros Hwf Hchildren Hrep.
  inversion Hrep as [c i s v Hclass Hnode|c i s op cs args Hclass Hnode Hargs]; subst c.
  - pose proof (allocate_new_node g n key i _ Hwf Hclass Hnode) as Heq; subst n.
    constructor.
  - pose proof (allocate_new_node g n key i _ Hwf Hclass Hnode) as Heq; subst n.
    constructor; apply (guarded_Forall2 _ _ _ cs args Hargs Hchildren).
    intros d t Hd Hchild.
    exact (allocate_old_represents g (Egraph.NApp s op cs) key Hwf d t Hchild Hd).
Qed.

Section Semantics.
Context {H F C : Type} (adm : EggSem.t K V C -> Prop)
  (facts : EggFact.t F K Sort V C) (rules : list (EggRule.t K Sort V H F)).

(** The empty graph is sound because it allocates no class that can represent a finite term. *)
Theorem empty_sound : sound a adm facts rules Egraph.empty.
Proof.
  intros c t u Ht Hu.
  pose proof (represents_allocated a Egraph.empty c t (empty_wf a) Ht) as Hbound.
  change (c < 1)%positive in Hbound; lia.
Qed.

Local Lemma node_sound g n t u :
  sound a adm facts rules g -> node_represents a g n t -> node_represents a g n u ->
  EggEqual.rel a adm facts rules t u.
Proof.
  intros Hsound Ht Hu; destruct Ht as [s v|s op cs ts Hts];
    inversion Hu as [s' v'|s' op' cs' us Hus]; subst.
  - apply EggEqual.refl.
  - apply EggEqual.app; clear Hu; revert us Hus.
    induction Hts as [|d t ds ts Ht Hrest IH]; intros us Hus;
      inversion Hus as [|d' u ds' us' Hu Htail]; subst.
    + constructor.
    + constructor; [exact (Hsound d t u Ht Hu)|exact (IH _ Htail)].
Qed.

(** Old classes gain no terms, and fresh-class terms are related by old-child congruence. *)
Local Lemma allocate_sound g n key :
  wf a g -> wf a (snd (Egraph.allocate a g n key)) -> children_known g n ->
  sound a adm facts rules g -> sound a adm facts rules (snd (Egraph.allocate a g n key)).
Proof.
  intros Hwf Hnew Hchildren Hsound c t u Ht Hu.
  destruct (Pos.eq_dec c (Egraph.next g)) as [->|Hne].
  - apply (node_sound g n t u Hsound).
    + exact (allocate_new_represents g n key t Hwf Hchildren Ht).
    + exact (allocate_new_represents g n key u Hwf Hchildren Hu).
  - pose proof (represents_allocated a _ c t Hnew Ht) as Hbound.
    rewrite allocate_equation in Hbound; cbn [snd Egraph.next] in Hbound.
    assert (Hold : (c < Egraph.next g)%positive) by lia.
    apply (Hsound c t u).
    + exact (allocate_old_represents g n key Hwf c t Ht Hold).
    + exact (allocate_old_represents g n key Hwf c u Hu Hold).
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

(** Successful node insertion preserves old generated-equality soundness under WF and key laws. *)
Theorem add_node_sound g n c h :
  encoding_laws a -> wf a g -> sound a adm facts rules g ->
  Egraph.add_node a g n = Some (c, h) -> sound a adm facts rules h.
Proof.
  intros Hl Hwf Hsound Hadded.
  pose proof (add_node_wf a g n c h Hl Hwf Hadded) as Hnew.
  rewrite add_node_equation in Hadded.
  destruct (Egraph.node_valid a g n) eqn:Hvalid; [|discriminate].
  destruct (Map.get _ _ _) as [d|] eqn:Hhit.
  - injection Hadded as <- <-; exact Hsound.
  - rewrite allocate_equation in Hadded; injection Hadded as Hc Hh; subst c h.
    apply (allocate_sound g (Egraph.canonical a g n)
      (Egraph.node_code a (Egraph.canonical a g n)) Hwf Hnew).
    + exact (checked_children_known g n Hwf Hvalid).
    + exact Hsound.
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
  rewrite !Cost.value_bind; fold (Egraph.add_terms a g args).
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
  rewrite !Cost.value_bind; fold (Egraph.add_term a g e).
  destruct (Egraph.add_term a g e) as [[c h]|]; reflexivity.
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

Local Lemma add_terms_wf es :
  encoding_laws a -> forall g cs h, wf a g ->
  Egraph.add_terms a g es = Some (cs, h) -> wf a h.
Proof.
  intro Hl; induction es as [|e es IH]; intros g cs h Hwf Hargs;
    rewrite add_terms_equation in Hargs.
  - injection Hargs as <- <-; exact Hwf.
  - destruct (Egraph.add_term a g e) as [[d j]|] eqn:Hchild; [|discriminate].
    destruct (proj1 (add_term_represents a g e Hl Hwf) d j Hchild) as [_ [Hj Hext]].
    destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Hrest; [|discriminate].
    injection Hargs as <- <-; exact (IH j ds k Hj Hrest).
Qed.

Local Lemma add_terms_sound es :
  encoding_laws a ->
  Forall (fun e => forall g c h, wf a g -> sound a adm facts rules g ->
    Egraph.add_term a g e = Some (c, h) -> sound a adm facts rules h) es ->
  forall g cs h, wf a g -> sound a adm facts rules g ->
    Egraph.add_terms a g es = Some (cs, h) -> sound a adm facts rules h.
Proof.
  intros Hl Hchildren; induction Hchildren as [|e es He Hrest IH]; intros g cs h Hwf Hsound.
  - rewrite add_terms_equation; intro Heq; injection Heq as <- <-; exact Hsound.
  - rewrite add_terms_equation.
    destruct (Egraph.add_term a g e) as [[c j]|] eqn:Heq; [|discriminate].
    pose proof (He g c j Hwf Hsound Heq) as Hsj.
    destruct (proj1 (add_term_represents a g e Hl Hwf) c j Heq) as [_ [Hj Hext]].
    destruct (Egraph.add_terms a j es) as [[ds k]|] eqn:Hes; [|discriminate].
    intro Hresult; injection Hresult as <- <-.
    exact (IH j ds k Hj Hsj Hes).
Qed.

(** Successful finite-term insertion preserves soundness through each intermediate child graph. *)
Theorem add_term_sound :
  encoding_laws a -> forall e g c h, wf a g -> sound a adm facts rules g ->
  Egraph.add_term a g e = Some (c, h) -> sound a adm facts rules h.
Proof.
  intro Hl; apply (term_ind_all (fun e => forall g c h, wf a g ->
    sound a adm facts rules g -> Egraph.add_term a g e = Some (c, h) ->
      sound a adm facts rules h)).
  - intros s v g c h Hwf Hsound; rewrite add_term_equation.
    exact (add_node_sound g (Egraph.NVar s v) c h Hl Hwf Hsound).
  - intros s op es IH g c h Hwf Hsound; rewrite add_term_equation.
    destruct (Egraph.add_terms a g es) as [[cs j]|] eqn:Hargs; [|discriminate].
    intro Hadded.
    pose proof (add_terms_sound es Hl IH g cs j Hwf Hsound Hargs) as Hsj.
    pose proof (add_terms_wf es Hl g cs j Hwf Hargs) as Hj.
    exact (add_node_sound j (Egraph.NApp s op cs) c h Hl Hj Hsj Hadded).
Qed.

End Semantics.
End Graph.

End EggInsertSpec.
