(** * Dominance over every entry path

    Dominance counts the initial node and every edge target of each entry path.
    For example, adding a second entry can invalidate a former dominator.
    Builds on: GraphModel, GraphPrepared and BaseEq. *)

From Stdlib Require Import List Bool PArith.
From Stdlib.Relations Require Import Relation_Operators.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Graph Require Import GraphModel GraphPrepared.
Import List.ListNotations.

(** A dominator occurs on every entry path, including the initial node. *)
Definition dominates {V E} (g : Graph.t V E) (d n : V) : Prop :=
  forall s es, In s (Graph.entries g) -> path g s es n ->
    d = s \/ exists e, In e es /\ Graph.target g e = d.

(** A strict dominator is distinct from its dominated node. *)
Definition strictly_dominates {V E} (g : Graph.t V E) d n :=
  dominates g d n /\ d <> n.

(** Every strict dominator of a child dominates its immediate dominator. *)
Definition immediately_dominates {V E} (g : Graph.t V E) d n :=
  strictly_dominates g d n /\
  forall x, strictly_dominates g x n -> dominates g x d.

(** Parent ancestry is the reflexive transitive closure of parent-to-child bindings. *)
Definition idom_ancestor (m : Map.t positive positive) :=
  clos_refl_trans positive (fun u v => Map.get positive_encoding v m = Some u).

Local Lemma path_endpoint {V E} (g : Graph.t V E) s es n :
  path g s es n -> n = s \/ exists e, In e es /\ Graph.target g e = n.
Proof.
  intro Hpath. induction Hpath as [v|e es n Hedge Hpath IH].
  - left. reflexivity.
  - right. destruct IH as [Heq|[a [Hin Heq]]].
    + exists e. split; [left; reflexivity|symmetry; exact Heq].
    + exists a. split; [right; exact Hin|exact Heq].
Qed.

Local Lemma path_prefix_target {V E} (g : Graph.t V E) s es n e :
  path g s es n -> In e es ->
  exists pre, path g s pre (Graph.target g e) /\ incl pre es.
Proof.
  intro Hpath. induction Hpath as [v|a es n Hedge Hpath IH]; intro Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst e. exists [a]. split.
      * constructor; [exact Hedge|constructor].
      * intros b [Heq|Hin]; [left; exact Heq|contradiction].
    + destruct (IH Hin) as [pre [Hpre Hsub]]. exists (a :: pre). split.
      * constructor; assumption.
      * intros b [Heq|Hb]; [left; exact Heq|right; apply Hsub; exact Hb].
Qed.

(** Every node dominates itself, even when entry reachability is empty. *)
Theorem dominates_refl {V E} (g : Graph.t V E) n : dominates g n n.
Proof.
  intros s es Hentry Hpath. now apply path_endpoint in Hpath.
Qed.

(** Dominance composes by restricting an entry path to its prefix. *)
Theorem dominates_trans {V E} (g : Graph.t V E) a b c :
  dominates g a b -> dominates g b c -> dominates g a c.
Proof.
  intros Hab Hbc s es Hentry Hpath.
  destruct (Hbc s es Hentry Hpath) as [Heq|[e [Hin Htarget]]].
  - subst b. destruct (Hab s [] Hentry (path_nil s)) as [Heq|[e [Hin _]]].
    + left. exact Heq.
    + contradiction.
  - destruct (path_prefix_target g s es c e Hpath Hin) as [pre [Hpre Hsub]].
    rewrite Htarget in Hpre.
    destruct (Hab s pre Hentry Hpre) as [Heq|[aedge [Ha Htargeta]]].
    + left. exact Heq.
    + right. exists aedge. split; [apply Hsub; exact Ha|exact Htargeta].
Qed.

Local Lemma path_last {V E} (g : Graph.t V E) s es n :
  path g s es n -> es <> [] ->
  exists pre e, es = pre ++ [e] /\ path g s pre (Graph.source g e) /\
    Graph.target g e = n /\ In e (Graph.out g (Graph.source g e)).
Proof.
  intro Hpath. induction Hpath as [v|a es n Hedge Hpath IH]; intro Hnonempty.
  - contradiction.
  - destruct es as [|b rest].
    + inversion Hpath; subst n. exists [], a. split; [reflexivity|].
      split; [constructor|auto].
    + destruct (IH ltac:(discriminate)) as [pre [e [Hes [Hpre [Htarget He]]]]].
      exists (a :: pre), e. split; [cbn; now rewrite Hes|].
      split; [constructor; assumption|auto].
Qed.

(** A non-entry node's unique predecessor dominates it across all entries. *)
Theorem dominates_unique_predecessor {V E} (g : Graph.t V E) d n :
  ~ In n (Graph.entries g) ->
  (forall e, In e (Graph.out g (Graph.source g e)) ->
    Graph.target g e = n -> Graph.source g e = d) ->
  dominates g d n.
Proof.
  intros Hentry Hpred s es Hs Hpath.
  destruct es as [|a rest].
  - assert (s = n) by now inversion Hpath. subst s. exfalso. exact (Hentry Hs).
  - destruct (path_last g s (a :: rest) n Hpath ltac:(discriminate))
      as [pre [e [Hes [Hpre [Htarget He]]]]].
    rewrite (Hpred e He Htarget) in Hpre.
    destruct (path_endpoint g s pre d Hpre) as [Heq|[b [Hb Htargetb]]].
    + now left.
    + right. exists b. split; [rewrite Hes; apply in_or_app; now left|exact Htargetb].
Qed.

Local Lemma path_without {V E} (eq : V -> V -> Cost.t bool) d (g : Graph.t V E) s es n :
  path (without eq d g) s es n <->
  path g s es n /\ forall e, In e es -> Cost.value (eq (Graph.target g e) d) = false.
Proof.
  split.
  - intro Hpath. induction Hpath as [v|e es n Hedge Hpath IH].
    + split; [constructor|intros e Hin; contradiction].
    + rewrite without_out in Hedge. apply filter_In in Hedge.
      destruct Hedge as [Hedge Hfree].
      apply Bool.negb_true_iff in Hfree.
      destruct IH as [Horiginal Htargets]. split.
      * exact (@path_cons V E g e es n Hedge Horiginal).
      * intros a [Heq|Hin]; [subst a; exact Hfree|apply Htargets; exact Hin].
  - intros [Hpath Htargets]. induction Hpath as [v|e es n Hedge Hpath IH].
    + constructor.
    + refine (@path_cons V E (without eq d g) e es n _ _).
      * rewrite without_out. apply filter_In. split; [exact Hedge|].
        apply Bool.negb_true_iff. apply Htargets. left. reflexivity.
      * apply IH. intros a Hin. apply Htargets. right. exact Hin.
Qed.

Local Lemma reachable_without {V E} (eq : V -> V -> Cost.t bool) d (g : Graph.t V E) n :
  reachable (without eq d g) n <->
  exists s es, In s (Graph.entries g) /\ path g s es n /\
    Cost.value (eq s d) = false /\
    forall e, In e es -> Cost.value (eq (Graph.target g e) d) = false.
Proof.
  rewrite reachable_iff_path. split.
  - intros [s [es [Hentry Hpath]]].
    apply filter_In in Hentry. destruct Hentry as [Hentry Hfree].
    apply Bool.negb_true_iff in Hfree.
    apply path_without in Hpath. destruct Hpath as [Hpath Htargets].
    exists s, es. auto.
  - intros [s [es [Hentry [Hpath [Hfree Htargets]]]]].
    exists s, es. split.
    + apply filter_In. split; [exact Hentry|now apply Bool.negb_true_iff].
    + apply path_without. auto.
Qed.

Local Lemma occurrence_dec {V E} (enc : encoding V) (HE : encoding_laws enc)
    (g : Graph.t V E) d s es :
  {d = s \/ exists e, In e es /\ Graph.target g e = d} +
  {d <> s /\ forall e, In e es -> Graph.target g e <> d}.
Proof.
  destruct (eqb_dec enc HE d s) as [Heq|Hne].
  - left. now left.
  - induction es as [|e es IH].
    + right. split; [exact Hne|intros a Hin; contradiction].
    + destruct (eqb_dec enc HE (Graph.target g e) d) as [Heq|Hedge].
      * left. right. exists e. split; [left; reflexivity|exact Heq].
      * destruct IH as [Hoccurs|[_ Htargets]].
        -- left. destruct Hoccurs as [Heq|[a [Hin Htarget]]].
           ++ now left.
           ++ right. exists a. split; [right; exact Hin|exact Htarget].
        -- right. split; [exact Hne|].
           intros a [Heq|Hin]; [subst a; exact Hedge|apply Htargets; exact Hin].
Qed.

(** Deleting one node makes precisely its dominated nodes unreachable. *)
Theorem dominates_iff_unreachable_without {V E} (enc : encoding V)
    (HE : encoding_laws enc) (g : Graph.t V E) d n :
  dominates g d n <-> ~ reachable (without (eqb_c enc) d g) n.
Proof.
  split.
  - intros Hdom Hreach. apply reachable_without in Hreach.
    destruct Hreach as [s [es [Hentry [Hpath [Hfree Htargets]]]]].
    apply (eqb_false_iff enc HE) in Hfree.
    destruct (Hdom s es Hentry Hpath) as [Heq|[e [Hin Htarget]]].
    + congruence.
    + specialize (Htargets e Hin). apply (eqb_false_iff enc HE) in Htargets.
      contradiction.
  - intros Hunreach s es Hentry Hpath.
    destruct (occurrence_dec enc HE g d s es) as [Hoccurs|[Hstart Htargets]].
    + exact Hoccurs.
    + exfalso. apply Hunreach. apply reachable_without.
      exists s, es. split; [exact Hentry|]. split; [exact Hpath|]. split.
      * apply (eqb_false_iff enc HE). congruence.
      * intros e Hin. apply (eqb_false_iff enc HE). apply Htargets. exact Hin.
Qed.

(** Post-dominance quantifies over every path to any supplied exit. *)
Definition post_dominates {V E} (g : Graph.t V E) exits d n :=
  forall z es, In z exits -> path g n es z ->
    d = n \/ exists e, In e es /\ Graph.target g e = d.

(** A dominance back edge returns to a dominator of its source. *)
Definition back_edge {V E} (g : Graph.t V E) e :=
  In e (Graph.out g (Graph.source g e)) /\
  dominates g (Graph.target g e) (Graph.source g e).

Module Dom.

Record tree := Tree {
  idom : Map.t positive positive;
  tin : Map.t positive positive;
  tout : Map.t positive positive
}.

(** Exact trees cover reachable nodes and number the finite immediate-dominator forest. *)
Record exact {V E} (p : Prepared.t V E) (t : tree) : Prop := {
  maps_wf : Map.wf positive_encoding (idom t) /\
    Map.wf positive_encoding (tin t) /\ Map.wf positive_encoding (tout t);
  idom_sound : forall v u n d,
    Map.get positive_encoding v (idom t) = Some u ->
    Prepared.name_of p v = Some n -> Prepared.name_of p u = Some d ->
    immediately_dominates (Prepared.graph p) d n;
  idom_complete : forall n v, reachable (Prepared.graph p) n ->
    Prepared.id_of p n = Some v ->
    (Map.get positive_encoding v (idom t) = None <->
      forall d, ~ strictly_dominates (Prepared.graph p) d n);
  idom_domain : forall v u, Map.get positive_encoding v (idom t) = Some u ->
    exists n d, Prepared.name_of p v = Some n /\ Prepared.name_of p u = Some d /\
      reachable (Prepared.graph p) n /\ reachable (Prepared.graph p) d;
  parent_finite : well_founded (fun u v => Map.get positive_encoding v (idom t) = Some u);
  numbering : forall n d v u, reachable (Prepared.graph p) n ->
    reachable (Prepared.graph p) d -> Prepared.id_of p n = Some v ->
    Prepared.id_of p d = Some u ->
    exists a b c e, Map.get positive_encoding u (tin t) = Some a /\
      Map.get positive_encoding v (tin t) = Some b /\
      Map.get positive_encoding v (tout t) = Some c /\
      Map.get positive_encoding u (tout t) = Some e /\
      ((a <= b /\ c <= e)%positive <-> idom_ancestor (idom t) u v)
}.

End Dom.
