(** * Uniqueness of exact immediate-parent maps

    The public tree contract determines every parent lookup.
    For example, two exact trees on the same prepared graph have identical parent maps.
    Builds on: GraphDomSpec, GraphCheckDom and canonical map extensionality. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphCheckDom.

Module DomParents.

(** Two immediate dominators of a reachable node coincide by semantic antisymmetry. *)
Theorem immediate_unique {V E} (p : Prepared.t V E) d e n :
  Prepared.ready p -> reachable (Prepared.graph p) n ->
  immediately_dominates (Prepared.graph p) d n ->
  immediately_dominates (Prepared.graph p) e n -> d = e.
Proof.
  intros Hready Hn [[Hd Hdn] Hnearest_d] [[He Hen] Hnearest_e].
  apply (prepared_dominates_antisym p d e Hready).
  - exact (DomCheck.dominator_reachable _ d n Hn Hd).
  - exact (DomCheck.dominator_reachable _ e n Hn He).
  - apply Hnearest_e. split; assumption.
  - apply Hnearest_d. split; assumption.
Qed.

(** An exact tree's present lookup is equivalent to immediate dominance of the named nodes. *)
Theorem get_iff_immediate {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> Dom.exact p t ->
  reachable (Prepared.graph p) n ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (Map.get positive_encoding v (Dom.idom t) = Some u <->
    immediately_dominates (Prepared.graph p) d n).
Proof.
  intros Hready Htree Hn Hv Hu.
  pose proof (proj2 (proj2 Hready)) as Hp.
  split.
  - intro Hget. apply (Dom.idom_sound p t Htree v u n d Hget).
    + now apply Prepared.name_of_id_of.
    + now apply Prepared.name_of_id_of.
  - intro Himmediate.
    destruct (Map.get positive_encoding v (Dom.idom t)) as [w|] eqn:Hget.
    + destruct (Dom.idom_domain p t Htree v w Hget) as [n' [e [Hn' [He [Hnreach Hereach]]]]].
      pose proof (Prepared.name_of_id_of p n v Hp Hv) as Hname.
      assert (Hsame : n' = n) by congruence. subst n'.
      pose proof (Dom.idom_sound p t Htree v w n e Hget Hname He) as Hother.
      pose proof (immediate_unique p d e n Hready Hn Himmediate Hother) as Heq. subst e.
      pose proof (Prepared.id_of_name_of p w d Hp He) as Hw.
      assert (u = w) by congruence. now subst w.
    + exfalso. apply (proj1 (Dom.idom_complete p t Htree n v Hn Hv) Hget d).
      exact (proj1 Himmediate).
Qed.

(** Exact parent maps agree at every ID, including unknown and unreachable IDs. *)
Theorem get_agrees {V E} (p : Prepared.t V E) first second :
  Prepared.ready p -> Dom.exact p first -> Dom.exact p second ->
  forall v, Map.get positive_encoding v (Dom.idom first) =
    Map.get positive_encoding v (Dom.idom second).
Proof.
  intros Hready Hfirst Hsecond v.
  pose proof (proj2 (proj2 Hready)) as Hp.
  destruct (Map.get positive_encoding v (Dom.idom first)) as [u|] eqn:Hleft.
  - destruct (Dom.idom_domain p first Hfirst v u Hleft)
      as [n [d [Hn [Hd [Hreach Hdomreach]]]]].
    pose proof (Prepared.id_of_name_of p v n Hp Hn) as Hv.
    pose proof (Prepared.id_of_name_of p u d Hp Hd) as Hu.
    symmetry. apply (get_iff_immediate p second n d v u Hready Hsecond Hreach Hv Hu).
    exact (Dom.idom_sound p first Hfirst v u n d Hleft Hn Hd).
  - destruct (Map.get positive_encoding v (Dom.idom second)) as [u|] eqn:Hright;
      [|reflexivity].
    destruct (Dom.idom_domain p second Hsecond v u Hright)
      as [n [d [Hn [Hd [Hreach Hdomreach]]]]].
    pose proof (Prepared.id_of_name_of p v n Hp Hn) as Hv.
    pose proof (Prepared.id_of_name_of p u d Hp Hd) as Hu.
    pose proof (proj2 (get_iff_immediate p first n d v u Hready Hfirst Hreach Hv Hu)
      (Dom.idom_sound p second Hsecond v u n d Hright Hn Hd)) as Hsome.
    congruence.
Qed.

(** Canonical storage turns complete lookup agreement into equality of the actual parent maps. *)
Theorem maps_agree {V E} (p : Prepared.t V E) first second :
  Prepared.ready p -> Dom.exact p first -> Dom.exact p second ->
  Dom.idom first = Dom.idom second.
Proof.
  intros Hready Hfirst Hsecond.
  apply (Map.ext positive_encoding positive_encoding_laws).
  - exact (proj1 (Dom.maps_wf p first Hfirst)).
  - exact (proj1 (Dom.maps_wf p second Hsecond)).
  - exact (get_agrees p first second Hready Hfirst Hsecond).
Qed.

End DomParents.
