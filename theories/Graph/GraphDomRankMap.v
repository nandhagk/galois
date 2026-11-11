(** * Finite partial rank-map folds

    These proof lemmas describe insertion folds after partial key and value conversion.
    For example, injective rank conversion prevents a later vertex from replacing another vertex.
    Builds on: public canonical map insertion and lookup contracts. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseMap.

Module DomRankMap.

Definition insert {A B} (key : A -> option positive) (value : A -> option B)
    (m : Map.t positive B) x :=
  match key x, value x with
  | Some k, Some v => Map.set positive_encoding k v m
  | _, _ => m
  end.

Local Lemma insert_wf {A B} (key : A -> option positive) (value : A -> option B) m x :
  Map.wf positive_encoding m -> Map.wf positive_encoding (insert key value m x).
Proof.
  intro Hmap. unfold insert. destruct (key x), (value x);
    [now apply Map.wf_set|exact Hmap|exact Hmap|exact Hmap].
Qed.

(** A partial insertion fold always maintains canonical storage. *)
Theorem fold_wf {A B} (key : A -> option positive) (value : A -> option B) xs :
  forall m, Map.wf positive_encoding m ->
  Map.wf positive_encoding (fold_left (insert key value) xs m).
Proof.
  induction xs as [|x rest IH]; intros m Hmap; [exact Hmap|].
  cbn [fold_left]. apply IH. now apply insert_wf.
Qed.

Local Lemma insert_sound {A B} (key : A -> option positive) (value : A -> option B)
    m x k v :
  Map.wf positive_encoding m ->
  Map.get positive_encoding k (insert key value m x) = Some v ->
  Map.get positive_encoding k m = Some v \/ key x = Some k /\ value x = Some v.
Proof.
  intros Hmap. unfold insert. destruct (key x) as [a|] eqn:Hkey;
    destruct (value x) as [b|] eqn:Hvalue; try (intro Hget; now left).
  destruct (Pos.eq_dec k a) as [->|Hne].
  - rewrite Map.get_set_same by exact Hmap.
    intro Heq. injection Heq as <-. right. auto.
  - rewrite Map.get_set_other by (try exact positive_encoding_laws; assumption).
    intro Hget. now left.
Qed.

(** Every binding after a partial insertion fold comes from the original map or a supplied element. *)
Theorem fold_sound {A B} (key : A -> option positive) (value : A -> option B) xs :
  forall m, Map.wf positive_encoding m -> forall k v,
  Map.get positive_encoding k (fold_left (insert key value) xs m) = Some v ->
  Map.get positive_encoding k m = Some v \/
    exists x, In x xs /\ key x = Some k /\ value x = Some v.
Proof.
  induction xs as [|x rest IH]; intros m Hmap k v Hget.
  - now left.
  - cbn [fold_left] in Hget.
    apply (IH _ (insert_wf key value m x Hmap)) in Hget.
    destruct Hget as [Hfirst|[y [Hy Hbinding]]].
    + destruct (insert_sound key value m x k v Hmap Hfirst) as [Hold|Hnew].
      * now left.
      * right. exists x. split; [now left|exact Hnew].
    + right. exists y. split; [now right|exact Hbinding].
Qed.

Local Lemma insert_preserves {A B} (key : A -> option positive) (value : A -> option B)
    candidate k v m x :
  (forall a b i, key a = Some i -> key b = Some i -> a = b) ->
  key candidate = Some k -> value candidate = Some v -> Map.wf positive_encoding m ->
  Map.get positive_encoding k m = Some v ->
  Map.get positive_encoding k (insert key value m x) = Some v.
Proof.
  intros Hinjective Hkey Hvalue Hmap Hget. unfold insert.
  destruct (key x) as [a|] eqn:Ha; destruct (value x) as [b|] eqn:Hb;
    try exact Hget.
  destruct (Pos.eq_dec k a) as [->|Hne].
  - assert (candidate = x) by (eapply Hinjective; eauto). subst x.
    rewrite Hvalue in Hb. injection Hb as <-. now apply Map.get_set_same.
  - rewrite Map.get_set_other by (try exact positive_encoding_laws; assumption).
    exact Hget.
Qed.

Local Lemma fold_preserves {A B} (key : A -> option positive) (value : A -> option B)
    candidate k v xs :
  (forall a b i, key a = Some i -> key b = Some i -> a = b) ->
  key candidate = Some k -> value candidate = Some v ->
  forall m, Map.wf positive_encoding m -> Map.get positive_encoding k m = Some v ->
  Map.get positive_encoding k (fold_left (insert key value) xs m) = Some v.
Proof.
  intros Hinjective Hkey Hvalue.
  induction xs as [|x rest IH]; intros m Hmap Hget; [exact Hget|].
  cbn [fold_left]. apply IH; [now apply insert_wf|].
  exact (insert_preserves key value candidate k v m x Hinjective Hkey Hvalue Hmap Hget).
Qed.

(** Injective key conversion preserves the binding of every successfully converted input element. *)
Theorem fold_complete {A B} (key : A -> option positive) (value : A -> option B)
    candidate k v xs :
  (forall a b i, key a = Some i -> key b = Some i -> a = b) ->
  key candidate = Some k -> value candidate = Some v -> In candidate xs ->
  forall m, Map.wf positive_encoding m ->
  Map.get positive_encoding k (fold_left (insert key value) xs m) = Some v.
Proof.
  intros Hinjective Hkey Hvalue Hin.
  induction xs as [|x rest IH]; intros m Hmap; [contradiction|].
  cbn [fold_left]. destruct Hin as [Heq|Hin].
  - subst x. apply (fold_preserves key value candidate k v rest Hinjective Hkey Hvalue).
    + now apply insert_wf.
    + unfold insert. rewrite Hkey, Hvalue. now apply Map.get_set_same.
  - apply IH; [exact Hin|now apply insert_wf].
Qed.

End DomRankMap.
