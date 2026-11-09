(** * Charged erasure and dense-ID transport

    Erasure rebuilds a canonical map after converting both endpoints of each stored binding.
    For example, a parent binding to the virtual root disappears because the root has no real ID.
    Builds on: GraphDomVirtual, GraphDomParents and public map and preparation contracts. *)

From Stdlib Require Import List PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared GraphDomSpec GraphDomVirtual
  GraphDomParents.
Import List.ListNotations Cost.Notations.

Module DomErase.

(** Missing endpoint conversions omit a binding and never manufacture an ID. *)
Definition binding_c (rename : positive -> Cost.t (option positive))
    (binding : positive * positive) (tail : Map.t positive positive) :=
  Cost.step ;;
  let* child := rename (fst binding) in
  Cost.step ;;
  let* parent := rename (snd binding) in
  match child, parent with
  | Some v, Some u => Map.set_c positive_encoding v u tail
  | _, _ => Cost.ret tail
  end.

Definition binding (rename : positive -> option positive)
    (kv : positive * positive) (tail : Map.t positive positive) :=
  match rename (fst kv), rename (snd kv) with
  | Some v, Some u => Map.set positive_encoding v u tail
  | _, _ => tail
  end.

Local Lemma binding_value rename kv tail :
  Cost.value (binding_c rename kv tail) =
    binding (fun x => Cost.value (rename x)) kv tail.
Proof.
  unfold binding_c, binding. autorewrite with galois_cost.
  destruct (Cost.value (rename (fst kv))), (Cost.value (rename (snd kv)));
    reflexivity.
Qed.

(** Endpoint erasure charges the actual stored-map enumeration and all conversion callbacks. *)
Definition with_c rename (m : Map.t positive positive) :=
  let* bindings := Map.elements_c m in
  fold_right_c (binding_c rename) Map.empty bindings.

Definition with_map rename m := Cost.value (with_c rename m).

(** Erasure preserves right-fold overwrite order on arbitrary raw storage. *)
Theorem with_equation rename m :
  with_map rename m =
    fold_right (binding (fun x => Cost.value (rename x))) Map.empty (Map.elements m).
Proof.
  unfold with_map, with_c. autorewrite with galois_cost.
  fold (Map.elements m).
  induction (Map.elements m) as [|kv rest IH]; [reflexivity|].
  cbn [fold_right]. now rewrite binding_value, IH.
Qed.

Local Lemma list_wf rename xs :
  Map.wf positive_encoding (fold_right (binding rename) Map.empty xs).
Proof.
  induction xs as [|[v u] rest IH]; [apply Map.wf_empty|].
  cbn [fold_right]. unfold binding at 1. cbn [fst snd].
  destruct (rename v), (rename u); try exact IH. now apply Map.wf_set.
Qed.

(** Rebuilding establishes representation validity even if the input storage is malformed. *)
Theorem with_wf rename m : Map.wf positive_encoding (with_map rename m).
Proof.
  rewrite with_equation. apply list_wf.
Qed.

(** A partial endpoint conversion is injective on the successful conversion domain. *)
Definition injective (rename : positive -> option positive) :=
  forall i j v, rename i = Some v -> rename j = Some v -> i = j.

Local Lemma list_get rename xs :
  injective rename -> NoDup (map fst xs) -> forall v u,
  (Map.get positive_encoding v (fold_right (binding rename) Map.empty xs) = Some u <->
    exists i j, In (i, j) xs /\ rename i = Some v /\ rename j = Some u).
Proof.
  intros Hinjective Hnodup. induction xs as [|[i j] rest IH]; intros v u.
  - cbn [fold_right]. rewrite Map.get_empty. split; [discriminate|].
    intros [a [b [Hfalse _]]]. contradiction.
  - inversion Hnodup as [|key keys Hfresh Hrest]; subst.
    cbn [fold_right]. unfold binding at 1. cbn [fst snd].
    destruct (rename i) as [a|] eqn:Hi; destruct (rename j) as [b|] eqn:Hj.
    + destruct (Pos.eq_dec v a) as [->|Hne].
      * rewrite Map.get_set_same by apply list_wf. split.
        -- intro Heq. injection Heq as <-. exists i, j.
           split; [now left|]. split; assumption.
        -- intros [x [y [[Heq|Hin] [Hx Hy]]]].
           ++ injection Heq as <- <-. rewrite Hj in Hy. exact Hy.
           ++ assert (x = i) by (eapply Hinjective; [exact Hx|exact Hi]).
              subst x. exfalso. apply Hfresh.
              apply in_map_iff. exists (i, y). auto.
      * rewrite Map.get_set_other by (try exact positive_encoding_laws;
          try apply list_wf; exact Hne).
        rewrite IH by exact Hrest. split.
        -- intros [x [y [Hin [Hx Hy]]]]. exists x, y.
           split; [now right|auto].
        -- intros [x [y [[Heq|Hin] [Hx Hy]]]].
           ++ injection Heq as <- <-. congruence.
           ++ exists x, y. auto.
    + rewrite IH by exact Hrest. split.
      * intros [x [y [Hin [Hx Hy]]]]. exists x, y. split; [now right|auto].
      * intros [x [y [[Heq|Hin] [Hx Hy]]]].
        -- injection Heq as <- <-. congruence.
        -- exists x, y. auto.
    + rewrite IH by exact Hrest. split.
      * intros [x [y [Hin [Hx Hy]]]]. exists x, y. split; [now right|auto].
      * intros [x [y [[Heq|Hin] [Hx Hy]]]].
        -- injection Heq as <- <-. congruence.
        -- exists x, y. auto.
    + rewrite IH by exact Hrest. split.
      * intros [x [y [Hin [Hx Hy]]]]. exists x, y. split; [now right|auto].
      * intros [x [y [[Heq|Hin] [Hx Hy]]]].
        -- injection Heq as <- <-. congruence.
        -- exists x, y. auto.
Qed.

(** Successful injective conversion preserves precisely the original represented bindings. *)
Theorem with_get rename m v u :
  injective (fun x => Cost.value (rename x)) -> Map.wf positive_encoding m ->
  (Map.get positive_encoding v (with_map rename m) = Some u <->
    exists i j, Map.get positive_encoding i m = Some j /\
      Cost.value (rename i) = Some v /\ Cost.value (rename j) = Some u).
Proof.
  intros Hinjective Hmap. rewrite with_equation.
  rewrite list_get by (try exact Hinjective;
    exact (Map.elements_nodup positive_encoding m Hmap)).
  split; intros [i [j [Hbinding Hrest]]]; exists i, j; split; [|exact Hrest| |exact Hrest].
  - apply (Map.elements_spec positive_encoding positive_encoding_laws _ _ _ Hmap).
    exact Hbinding.
  - apply (Map.elements_spec positive_encoding positive_encoding_laws _ _ _ Hmap).
    exact Hbinding.
Qed.

(** A virtual ID converts through its actual name and then through the original prepared table. *)
Definition real_id_c {V E F} (p : Prepared.t V E) (q : Prepared.t (option V) F) i :=
  let* name := Prepared.name_of_c q i in
  match name with
  | Some (Some v) => Prepared.id_of_c p v
  | _ => Cost.ret None
  end.

Definition real_id {V E F} (p : Prepared.t V E) (q : Prepared.t (option V) F) i :=
  Cost.value (real_id_c p q i).

(** Root and absent names have no original dense ID. *)
Theorem real_id_equation {V E F} (p : Prepared.t V E) (q : Prepared.t (option V) F) i :
  real_id p q i =
    match Prepared.name_of q i with
    | Some (Some v) => Prepared.id_of p v
    | _ => None
    end.
Proof.
  unfold real_id, real_id_c. rewrite Cost.value_bind.
  fold (Prepared.name_of q i).
  destruct (Prepared.name_of q i) as [[v|]|]; reflexivity.
Qed.

(** Successful dense-ID transport records the same real node in both prepared tables. *)
Theorem real_id_spec {V E F} (p : Prepared.t V E) (q : Prepared.t (option V) F) i v :
  real_id p q i = Some v <->
    exists n, Prepared.name_of q i = Some (Some n) /\ Prepared.id_of p n = Some v.
Proof.
  rewrite real_id_equation.
  destruct (Prepared.name_of q i) as [[n|]|] eqn:Hname.
  - split; [intro H; exists n; auto|intros [a [Heq Ha]]].
    injection Heq as <-. exact Ha.
  - split; [discriminate|intros [a [Hfalse _]]; discriminate].
  - split; [discriminate|intros [a [Hfalse _]]; discriminate].
Qed.

(** Prepared inverse laws make successful dense-ID transport injective. *)
Theorem real_id_injective {V E F} (p : Prepared.t V E) (q : Prepared.t (option V) F) :
  Prepared.laws p -> Prepared.laws q -> injective (real_id p q).
Proof.
  intros Hp Hq i j v Hi Hj.
  apply real_id_spec in Hi, Hj.
  destruct Hi as [a [Hia Ha]]. destruct Hj as [b [Hjb Hb]].
  pose proof (Prepared.name_of_id_of p a v Hp Ha) as Hnamea.
  pose proof (Prepared.name_of_id_of p b v Hp Hb) as Hnameb.
  assert (a = b) by congruence. subst b.
  pose proof (Prepared.id_of_name_of q i (Some a) Hq Hia) as Hidi.
  pose proof (Prepared.id_of_name_of q j (Some a) Hq Hjb) as Hidj.
  congruence.
Qed.

(** Injective endpoint erasure preserves parent well-foundedness without assigning ranks to absent names. *)
Theorem with_finite rename m :
  injective (fun x => Cost.value (rename x)) ->
  Map.wf positive_encoding m ->
  well_founded (fun u v => Map.get positive_encoding v m = Some u) ->
  well_founded (fun u v => Map.get positive_encoding v (with_map rename m) = Some u).
Proof.
  intros Hinjective Hmap Hfinite.
  assert (Htransport : forall rank, Acc (fun u v => Map.get positive_encoding v m = Some u) rank ->
    forall v, Cost.value (rename rank) = Some v ->
      Acc (fun u v => Map.get positive_encoding v (with_map rename m) = Some u) v).
  { intros rank Hacc. induction Hacc as [rank Hparents IH]. intros v Hname.
    constructor. intros u Hget. apply (with_get rename m v u Hinjective Hmap) in Hget.
    destruct Hget as [i [j [Hparent [Hi Hj]]]].
    assert (i = rank) by (eapply Hinjective; [exact Hi|exact Hname]). subst i.
    exact (IH j Hparent u Hj). }
  intro v. destruct (Map.get positive_encoding v (with_map rename m)) as [u|] eqn:Hget.
  - apply (with_get rename m v u Hinjective Hmap) in Hget.
    destruct Hget as [i [j [Hparent [Hi Hj]]]]. exact (Htransport i (Hfinite i) v Hi).
  - constructor. intros u Hparent. congruence.
Qed.

(** Virtual erasure returns a sentinel-free map using the original graph's actual dense IDs. *)
Definition erase_c {V E} (p : Prepared.t V E) m :=
  let* q := DomVirtual.virtual_c p in
  with_c (real_id_c p q) m.

Definition erase {V E} (p : Prepared.t V E) m := Cost.value (erase_c p m).

(** Every erased map has canonical storage independently of graph readiness. *)
Theorem erase_wf {V E} (p : Prepared.t V E) m :
  Map.wf positive_encoding (erase p m).
Proof.
  apply with_wf.
Qed.

(** Real-node parent lookups after erasure are precisely the original virtual lookups. *)
Theorem erase_get {V E} (p : Prepared.t V E) m v u :
  Prepared.ready p -> Map.wf positive_encoding m ->
  (Map.get positive_encoding v (erase p m) = Some u <->
    exists i j, Map.get positive_encoding i m = Some j /\
      real_id p (DomVirtual.virtual p) i = Some v /\
      real_id p (DomVirtual.virtual p) j = Some u).
Proof.
  intros Hready Hmap. apply with_get; [|exact Hmap].
  apply real_id_injective.
  - exact (proj2 (proj2 Hready)).
  - exact (proj2 (proj2 (DomVirtual.virtual_ready p Hready))).
Qed.

Local Lemma virtual_id_exists {V E} (p : Prepared.t V E) n :
  Prepared.ready p -> In n (Graph.nodes (Prepared.graph p)) ->
  exists i, Prepared.id_of (DomVirtual.virtual p) (Some n) = Some i.
Proof.
  intros Hready Hnode.
  apply (Prepared.ids_domain _ (proj2 (proj2 (DomVirtual.virtual_ready p Hready)))).
  rewrite DomVirtual.prepared_graph, DomVirtual.graph_equation.
  cbn [Graph.nodes]. apply in_or_app. left. now apply in_map.
Qed.

Local Lemma original_id_injective {V E} (p : Prepared.t V E) a b i :
  Prepared.laws p ->
  Prepared.id_of p a = Some i -> Prepared.id_of p b = Some i -> a = b.
Proof.
  intros Hp Ha Hb.
  pose proof (Prepared.name_of_id_of p a i Hp Ha).
  pose proof (Prepared.name_of_id_of p b i Hp Hb). congruence.
Qed.

(** Erasure of an exact virtual tree gives exactly every reachable real immediate parent. *)
Theorem erase_virtual_exact {V E} (p : Prepared.t V E) t n d v u :
  Prepared.ready p -> Dom.exact (DomVirtual.virtual p) t ->
  reachable (Prepared.graph p) n ->
  Prepared.id_of p n = Some v -> Prepared.id_of p d = Some u ->
  (Map.get positive_encoding v (erase p (Dom.idom t)) = Some u <->
    immediately_dominates (Prepared.graph p) d n).
Proof.
  intros Hready Htree Hn Hv Hu.
  pose proof (proj2 (proj2 Hready)) as Hp.
  pose proof (DomVirtual.virtual_ready p Hready) as Hvirtual.
  pose proof (proj2 (proj2 Hvirtual)) as Hq.
  pose proof (Prepared.encoding_valid p Hp) as Henc.
  rewrite erase_get by (try exact Hready; exact (proj1 (Dom.maps_wf _ t Htree))).
  split.
  - intros [i [j [Hget [Hchild Hparent]]]].
    apply real_id_spec in Hchild, Hparent.
    destruct Hchild as [a [Ha Hia]]. destruct Hparent as [b [Hb Hib]].
    assert (a = n) by (eapply original_id_injective; eauto). subst a.
    assert (b = d) by (eapply original_id_injective; eauto). subst b.
    pose proof (Dom.idom_sound _ t Htree i j (Some n) (Some d) Hget Ha Hb) as Himmediate.
    rewrite DomVirtual.prepared_graph in Himmediate.
    apply (proj2 (DomVirtual.virtual_immediate_iff _ _ d n Henc)). exact Himmediate.
  - intro Himmediate.
    destruct (virtual_id_exists p n Hready
      (proj2 (Prepared.ids_domain p Hp n) (ex_intro _ v Hv))) as [i Hi].
    destruct (virtual_id_exists p d Hready
      (proj2 (Prepared.ids_domain p Hp d) (ex_intro _ u Hu))) as [j Hj].
    assert (Hreach : reachable (Prepared.graph (DomVirtual.virtual p)) (Some n)).
    { rewrite DomVirtual.prepared_graph.
      apply (proj2 (DomVirtual.virtual_reachable_iff _ _ n Henc)). exact Hn. }
    exists i, j. split.
    + apply (proj2 (DomParents.get_iff_immediate _ t (Some n) (Some d) i j
        Hvirtual Htree Hreach Hi Hj)).
      rewrite DomVirtual.prepared_graph.
      apply (proj1 (DomVirtual.virtual_immediate_iff _ _ d n Henc)). exact Himmediate.
    + split; apply real_id_spec.
      * exists n. split; [now apply Prepared.name_of_id_of|exact Hv].
      * exists d. split; [now apply Prepared.name_of_id_of|exact Hu].
Qed.

End DomErase.
