(** * Labelled paths and relation closures

    Paths keep edge labels while closures describe reachability without labels.
    For example, two labelled steps compose into a path with two labels.
    Builds on: Stdlib lists. *)

From Stdlib Require Import List.
Import List.ListNotations.

Module Rel.

(** A labelled path records each step in its traversal order. *)
Inductive lpath {A L} (step : A -> L -> A -> Prop) : A -> list L -> A -> Prop :=
  | lpath_nil x : lpath step x [] x
  | lpath_cons x l y ls z :
      step x l y -> lpath step y ls z -> lpath step x (l :: ls) z.

(** Concatenating paths concatenates their label lists. *)
Theorem lpath_app {A L} (step : A -> L -> A -> Prop) x ls y ms z :
  lpath step x ls y -> lpath step y ms z -> lpath step x (ls ++ ms) z.
Proof.
  intros Hpath Htail. induction Hpath as [x|x l y ls v Hstep Hpath IH].
  - exact Htail.
  - cbn [app]. econstructor; [exact Hstep|now apply IH].
Qed.

(** Paths admit induction by appending the final step. *)
Theorem lpath_snoc_ind {A L} (step : A -> L -> A -> Prop)
    (P : A -> list L -> A -> Prop)
    (Hnil : forall x, P x [] x)
    (Hsnoc : forall x ls y l z,
      lpath step x ls y -> P x ls y -> step y l z -> P x (ls ++ [l]) z) :
  forall x ls z, lpath step x ls z -> P x ls z.
Proof.
  assert (Happend : forall x ls y, lpath step x ls y ->
    forall ms z, lpath step y ms z -> P x ls y -> P x (ls ++ ms) z).
  { intros x ls y Hprefix ms z Hsuffix. revert x ls Hprefix.
    induction Hsuffix as [y|y l v ms z Hstep Hsuffix IH];
      intros x ls Hprefix HP.
    - now rewrite app_nil_r.
    - change (P x (ls ++ ([l] ++ ms)) z). rewrite app_assoc.
      apply (IH x (ls ++ [l])).
      + eapply lpath_app; [exact Hprefix|].
        econstructor; [exact Hstep|constructor].
      + now apply (Hsnoc x ls y l v). }
  intros x ls z Hpath.
  change (P x ([] ++ ls) z).
  eapply Happend; [constructor|exact Hpath|apply Hnil].
Qed.

(** Every path of a subrelation is a path of its containing relation. *)
Theorem lpath_mono {A L} (R S : A -> L -> A -> Prop) :
  (forall x l y, R x l y -> S x l y) ->
  forall x ls y, lpath R x ls y -> lpath S x ls y.
Proof.
  intros Hstep x ls y Hpath. induction Hpath as [x|x l y ls z Hxy Hpath IH].
  - constructor.
  - econstructor; [apply Hstep; exact Hxy|exact IH].
Qed.

(** Mapping states and labels transports a path when it transports every step. *)
Theorem lpath_map {A B L M} (R : A -> L -> A -> Prop) (S : B -> M -> B -> Prop)
    (f : A -> B) (g : L -> M) :
  (forall x l y, R x l y -> S (f x) (g l) (f y)) ->
  forall x ls y, lpath R x ls y -> lpath S (f x) (map g ls) (f y).
Proof.
  intros Hstep x ls y Hpath. induction Hpath as [x|x l y ls z Hxy Hpath IH].
  - constructor.
  - cbn [map]. econstructor; [apply Hstep; exact Hxy|exact IH].
Qed.

(** A step-closed predicate holds at every path endpoint reached from an initial member. *)
Theorem lpath_invariant {A L} (step : A -> L -> A -> Prop) (P : A -> Prop) :
  (forall x l y, P x -> step x l y -> P y) ->
  forall x ls y, lpath step x ls y -> P x -> P y.
Proof.
  intros Hclosed x ls y Hpath. induction Hpath as [x|x l y ls z Hstep Hpath IH].
  - exact (fun HP => HP).
  - intro HP. apply IH. now apply (Hclosed x l y).
Qed.

(** Reflexive transitive closure allows an empty traversal. *)
Inductive star {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | star_refl x : star R x x
  | star_cons x y z : R x y -> star R y z -> star R x z.

(** Strict transitive closure requires at least one step. *)
Definition plus {A} (R : A -> A -> Prop) (x z : A) : Prop :=
  exists y, R x y /\ star R y z.

(** Unlabelled closure is equivalent to a path with a list of unit labels. *)
Theorem star_iff_lpath {A} (R : A -> A -> Prop) x y :
  star R x y <-> exists ls, lpath (fun a (_ : unit) b => R a b) x ls y.
Proof.
  split.
  - intro Hstar. induction Hstar as [x|x y z Hxy Hstar [ls Hpath]].
    + exists []. constructor.
    + exists (tt :: ls). econstructor; eassumption.
  - intros [ls Hpath]. induction Hpath as [x|x l y ls z Hxy Hpath IH].
    + constructor.
    + econstructor; eassumption.
Qed.

(** Closure traversals compose at their shared endpoint. *)
Theorem star_trans {A} (R : A -> A -> Prop) x y z :
  star R x y -> star R y z -> star R x z.
Proof.
  intros Hxy Hyz. induction Hxy as [x|x v y Hxv Hvy IH].
  - exact Hyz.
  - econstructor; [exact Hxv|now apply IH].
Qed.

(** Taking reflexive transitive closure twice adds no reachable endpoints. *)
Theorem star_idem {A} (R : A -> A -> Prop) x y :
  star (star R) x y <-> star R x y.
Proof.
  split.
  - intro Hstar. induction Hstar as [x|x v y Hxv Hvy IH].
    + constructor.
    + eapply star_trans; eassumption.
  - intro Hstar. econstructor; [exact Hstar|constructor].
Qed.

(** Closure is monotone in its step relation. *)
Theorem star_mono {A} (R S : A -> A -> Prop) :
  (forall x y, R x y -> S x y) ->
  forall x y, star R x y -> star S x y.
Proof.
  intros Hstep x y Hstar. induction Hstar as [x|x v y Hxv Hvy IH].
  - constructor.
  - econstructor; [apply Hstep; exact Hxv|exact IH].
Qed.

(** Every nonempty traversal is also a reflexive transitive traversal. *)
Theorem plus_star {A} (R : A -> A -> Prop) x y :
  plus R x y -> star R x y.
Proof.
  intros [z [Hxz Hzy]]. econstructor; eassumption.
Qed.

(** A predicate closed by individual steps is closed by reflexive transitive traversal. *)
Theorem star_invariant {A} (R : A -> A -> Prop) (P : A -> Prop) :
  (forall x y, P x -> R x y -> P y) ->
  forall x y, star R x y -> P x -> P y.
Proof.
  intros Hclosed x y Hstar. induction Hstar as [x|x v y Hxv Hvy IH].
  - exact (fun HP => HP).
  - intro HP. apply IH. now apply (Hclosed x v).
Qed.

End Rel.
Import Rel.
