(** * Exact representative transport through public forest equations

    Parent-index proofs distinguish unchanged root identifiers from mere class equivalence.
    For example, registering a fresh singleton preserves every previously observed root.
    Builds on: the public BaseUnionFind equations and compression contracts. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.

Module EggForest.

Section Forest.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).

Local Lemma bounded_find_same_parents fuel x first second :
  UnionFind.parents first = UnionFind.parents second ->
  fst (UnionFind.find_fuel E fuel x first) = fst (UnionFind.find_fuel E fuel x second).
Proof.
  revert x first second; induction fuel as [|fuel IH]; intros x first second Hparents.
  - rewrite !UnionFind.find_fuel_equation; reflexivity.
  - rewrite !UnionFind.find_fuel_equation, Hparents.
    destruct (Map.get E x (UnionFind.parents second)) as [y|]; [|reflexivity].
    pose proof (IH y first second Hparents) as Hroot.
    destruct (UnionFind.find_fuel E fuel y first) as [r first'].
    destruct (UnionFind.find_fuel E fuel y second) as [s second'].
    exact Hroot.
Qed.

(** Find observes the same roots in forests with equal parent maps and equal fuel bounds. *)
Theorem find_same_parents x first second :
  UnionFind.parents first = UnionFind.parents second ->
  UnionFind.max_rank first = UnionFind.max_rank second ->
  fst (UnionFind.find E x first) = fst (UnionFind.find E x second).
Proof.
  intros Hparents Hmaximum; rewrite !UnionFind.find_equation, Hmaximum.
  apply bounded_find_same_parents; exact Hparents.
Qed.

(** Registering a rank-zero key leaves the representative function unchanged. *)
Theorem touch_representatives uf registered query :
  fst (UnionFind.find E query (UnionFind.touch E registered uf)) =
    fst (UnionFind.find E query uf).
Proof.
  apply find_same_parents;
    rewrite UnionFind.touch_equation;
    destruct (Map.get E registered (UnionFind.ranks uf)); reflexivity.
Qed.

(** A self-union compresses paths and registers support without changing any representative. *)
Theorem self_union_representatives uf registered query :
  UnionFind.wf E uf ->
  fst (UnionFind.find E query (UnionFind.union E registered registered uf)) =
    fst (UnionFind.find E query uf).
Proof.
  intro Hwf; rewrite UnionFind.union_equation.
  pose proof (UnionFind.wf_find E HE uf registered Hwf) as Hfirst.
  pose proof (UnionFind.find_rep_stable E HE uf registered registered Hwf) as Hsame.
  pose proof (UnionFind.find_rep_stable E HE uf query registered Hwf) as Hquery.
  destruct (UnionFind.find E registered uf) as [root first] eqn:Hregistered.
  cbn [fst snd] in Hfirst, Hsame, Hquery.
  pose proof (UnionFind.find_rep_stable E HE first query registered Hfirst) as Hsecond.
  destruct (UnionFind.find E registered first) as [root' second] eqn:Hagain.
  cbn [fst snd] in Hsame, Hsecond.
  subst root'; rewrite eqb_refl, touch_representatives, Hsecond, Hquery; reflexivity.
Qed.

End Forest.

End EggForest.
