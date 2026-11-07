(** * Region folds and subtree tables

    One bottom-up traversal retains every subtree result at its relative position.
    For example, DFirst selects the left summary of a sequence.
    Builds on: ProgramSkeleton, FrameworkUtil and BaseMap. *)

From Stdlib Require Import List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Program Require Import ProgramSkeleton.
From Galois.Framework Require Import FrameworkUtil.
Import List.ListNotations Cost.Notations Skeleton.

Module Region.

(** Each statement constructor has one charged algebra operation. *)
Record algebra (A G R : Type) := Make {
  on_atom_c : A -> Cost.t R;
  on_seq_c : R -> R -> Cost.t R;
  on_if_c : G -> R -> R -> Cost.t R;
  on_block_c : R -> Cost.t R;
  on_loop_c : R -> Cost.t R;
  on_jump_c : nat -> Cost.t R;
  on_jump_if_c : G -> nat -> Cost.t R;
  on_jump_table_c : G -> list nat -> nat -> Cost.t R
}.
Arguments Make {A G R}.
Arguments on_atom_c {A G R}.
Arguments on_seq_c {A G R}.
Arguments on_if_c {A G R}.
Arguments on_block_c {A G R}.
Arguments on_loop_c {A G R}.
Arguments on_jump_c {A G R}.
Arguments on_jump_if_c {A G R}.
Arguments on_jump_table_c {A G R}.

Definition on_atom {A G R} (a : algebra A G R) x := Cost.value (on_atom_c a x).
Definition on_seq {A G R} (a : algebra A G R) x y := Cost.value (on_seq_c a x y).
Definition on_if {A G R} (a : algebra A G R) g x y := Cost.value (on_if_c a g x y).
Definition on_block {A G R} (a : algebra A G R) x := Cost.value (on_block_c a x).
Definition on_loop {A G R} (a : algebra A G R) x := Cost.value (on_loop_c a x).
Definition on_jump {A G R} (a : algebra A G R) n := Cost.value (on_jump_c a n).
Definition on_jump_if {A G R} (a : algebra A G R) g n := Cost.value (on_jump_if_c a g n).
Definition on_jump_table {A G R} (a : algebra A G R) g ns n :=
  Cost.value (on_jump_table_c a g ns n).

(** Pure algebras treat each supplied operation as a client primitive. *)
Definition of_pure {A G R} atom seq branch block loop jump jump_if jump_table :
    algebra A G R :=
  Make (fun a => Cost.step ;; Cost.ret (atom a))
    (fun x y => Cost.step ;; Cost.ret (seq x y))
    (fun g x y => Cost.step ;; Cost.ret (branch g x y))
    (fun x => Cost.step ;; Cost.ret (block x))
    (fun x => Cost.step ;; Cost.ret (loop x))
    (fun n => Cost.step ;; Cost.ret (jump n))
    (fun g n => Cost.step ;; Cost.ret (jump_if g n))
    (fun g ns n => Cost.step ;; Cost.ret (jump_table g ns n)).

Fixpoint fold_c {A G R} (alg : algebra A G R) (s : stmt A G) : Cost.t R :=
  Cost.step ;;
  match s with
  | Atom a => Cost.step ;; on_atom_c alg a
  | Seq l r =>
    let* x := fold_c alg l in
    let* y := fold_c alg r in
    Cost.step ;; on_seq_c alg x y
  | If g l r =>
    let* x := fold_c alg l in
    let* y := fold_c alg r in
    Cost.step ;; on_if_c alg g x y
  | Block b => let* x := fold_c alg b in Cost.step ;; on_block_c alg x
  | Loop b => let* x := fold_c alg b in Cost.step ;; on_loop_c alg x
  | Jump n => Cost.step ;; on_jump_c alg n
  | JumpIf g n => Cost.step ;; on_jump_if_c alg g n
  | JumpTable g ns n => Cost.step ;; on_jump_table_c alg g ns n
  end.

Definition fold {A G R} (alg : algebra A G R) s := Cost.value (fold_c alg s).

(** The fold equation exposes only constructor-wise algebra application. *)
Theorem fold_equation {A G R} (alg : algebra A G R) s :
  fold alg s =
  match s with
  | Atom a => on_atom alg a
  | Seq l r => on_seq alg (fold alg l) (fold alg r)
  | If g l r => on_if alg g (fold alg l) (fold alg r)
  | Block b => on_block alg (fold alg b)
  | Loop b => on_loop alg (fold alg b)
  | Jump n => on_jump alg n
  | JumpIf g n => on_jump_if alg g n
  | JumpTable g ns n => on_jump_table alg g ns n
  end.
Proof.
  destruct s; reflexivity.
Qed.

Definition prefix {R} d (xs : list (position * R)) :=
  map (fun pr => (d :: fst pr, snd pr)) xs.

Definition prefix_c {R} d (xs : list (position * R)) :=
  map_c (fun pr => Cost.ret (d :: fst pr, snd pr)) xs.

(** Rows are a specification of preorder subtree results, independent of map construction. *)
Fixpoint rows {A G R} (alg : algebra A G R) (s : stmt A G) :=
  ([], fold alg s) ::
  match s with
  | Seq l r | If _ l r => prefix DFirst (rows alg l) ++ prefix DSecond (rows alg r)
  | Block b | Loop b => prefix DBody (rows alg b)
  | _ => []
  end.

Definition binary_c {R} (f : R -> R -> Cost.t R)
    (l r : R * list (position * R)) :=
  Cost.step ;;
  let* result := f (fst l) (fst r) in
  let* ls := prefix_c DFirst (snd l) in
  let* rs := prefix_c DSecond (snd r) in
  let* rest := app_c ls rs in
  Cost.ret (result, ([], result) :: rest).

Definition unary_c {R} (f : R -> Cost.t R) (b : R * list (position * R)) :=
  Cost.step ;;
  let* result := f (fst b) in
  let* rest := prefix_c DBody (snd b) in
  Cost.ret (result, ([], result) :: rest).

Definition leaf_c {R} (m : Cost.t R) : Cost.t (R * list (position * R)) :=
  Cost.step ;; Cost.map (fun result => (result, [([], result)])) m.

(** A single syntax traversal returns both the root result and all subtree rows. *)
Fixpoint visit_c {A G R} (alg : algebra A G R) (s : stmt A G) :
    Cost.t (R * list (position * R)) :=
  Cost.step ;;
  match s with
  | Atom a => leaf_c (on_atom_c alg a)
  | Seq l r =>
    let* l := visit_c alg l in
    let* r := visit_c alg r in
    binary_c (on_seq_c alg) l r
  | If g l r =>
    let* l := visit_c alg l in
    let* r := visit_c alg r in
    binary_c (on_if_c alg g) l r
  | Block b => let* b := visit_c alg b in unary_c (on_block_c alg) b
  | Loop b => let* b := visit_c alg b in unary_c (on_loop_c alg) b
  | Jump n => leaf_c (on_jump_c alg n)
  | JumpIf g n => leaf_c (on_jump_if_c alg g n)
  | JumpTable g ns n => leaf_c (on_jump_table_c alg g ns n)
  end.

(** Retained rows and root results agree with the structural specifications. *)
Theorem visit_spec {A G R} (alg : algebra A G R) s :
  Cost.value (visit_c alg s) = (fold alg s, rows alg s).
Proof.
  induction s; cbn [visit_c]; autorewrite with galois_cost;
    rewrite ?IHs, ?IHs1, ?IHs2;
    unfold binary_c, unary_c, leaf_c, prefix_c;
    autorewrite with galois_cost;
    cbn [rows prefix fst snd]; reflexivity.
Qed.

Definition table_c {A G R} (alg : algebra A G R) s :=
  let* result := visit_c alg s in
  Map.of_list_c position_encoding (snd result).

Definition table {A G R} (alg : algebra A G R) s := Cost.value (table_c alg s).

(** Tables are the public map constructor applied to retained preorder rows. *)
Theorem table_equation {A G R} (alg : algebra A G R) s :
  table alg s = Map.of_list position_encoding (rows alg s).
Proof.
  unfold table, table_c; rewrite Cost.value_bind, visit_spec; reflexivity.
Qed.

Local Lemma prefix_nil {R} d (xs : list (position * R)) r :
  ~ In ([], r) (prefix d xs).
Proof.
  unfold prefix; rewrite in_map_iff; intros [[p v] [Hbad _]]; discriminate.
Qed.

Local Lemma prefix_cons {R} d e p (xs : list (position * R)) r :
  In (d :: p, r) (prefix e xs) <-> d = e /\ In (p, r) xs.
Proof.
  unfold prefix; rewrite in_map_iff; split.
  - intros [[q v] [Heq Hin]]; cbn in Heq; inversion Heq; subst; auto.
  - intros [-> Hin]; exists (p, r); auto.
Qed.

Local Lemma rows_exact {A G R} (alg : algebra A G R) s p r :
  In (p, r) (rows alg s) <-> exists t, sub s p = Some t /\ r = fold alg t.
Proof.
  revert p r; induction s; intros [|d p] r; cbn [rows In].
  all: rewrite ?in_app_iff.
  all: try solve [
    split;
    [intros [Heq|Htail]; [inversion Heq; subst; eexists; split; reflexivity|];
      exfalso; first
        [destruct Htail; eapply prefix_nil; eassumption
        |eapply prefix_nil; eassumption
        |exact Htail]
    |intros [t [Heq ->]]; rewrite sub_root_equation in Heq;
      inversion Heq; subst; left; reflexivity]].
  all: try destruct d.
  all: rewrite ?prefix_cons.
  all: rewrite ?sub_cons_equation, ?sub_root_equation.
  all: rewrite <- ?IHs, <- ?IHs1, <- ?IHs2.
  all: try solve [intuition congruence].
  all: split.
  all: try solve [intros [t [Hbad _]]; discriminate].
  all: intros [Hbad|Hbad]; [discriminate|].
  all: try solve [contradiction].
  all: intuition congruence.
Qed.

Local Lemma list_lookup_value {K R} (E : encoding K) (HE : encoding_laws E)
    (xs : list (K * R)) k r :
  In (k, r) xs ->
  (forall q v, In (q, v) xs -> q = k -> v = r) ->
  Map.get E k (Map.of_list E xs) = Some r.
Proof.
  intros Hin Hsame; rewrite Map.of_list_get.
  assert (Hfold : forall ys old,
    (forall q v, In (q, v) ys -> q = k -> v = r) ->
    (old = Some r \/ In (k, r) ys) ->
    fold_left (fun old kv => if eqb E k (fst kv) then Some (snd kv) else old)
      ys old = Some r).
  { induction ys as [|[q v] ys IH]; intros old Hall Hhit; cbn [fold_left fst snd].
    - destruct Hhit as [->|[]]; reflexivity.
    - apply IH.
      + intros q' v' Hy; apply Hall; right; exact Hy.
      + destruct (eqb E k q) eqn:Hq.
        * left; apply (eqb_true_iff E HE) in Hq; subst q.
          f_equal; exact (Hall k v (or_introl eq_refl) eq_refl).
        * destruct Hhit as [Hhit|[Hhit|Hhit]]; [left; exact Hhit| |right; exact Hhit].
          inversion Hhit; subst; rewrite eqb_refl in Hq; discriminate. }
  apply Hfold; [exact Hsame|right; exact Hin].
Qed.

(** Every successful subtree lookup returns that subtree's fold result. *)
Theorem table_get_spec {A G R} (alg : algebra A G R) s p s' :
  sub s p = Some s' ->
  Map.get position_encoding p (table alg s) = Some (fold alg s').
Proof.
  intro Hsub; rewrite table_equation.
  apply list_lookup_value; [apply position_encoding_laws| |].
  - apply rows_exact; exists s'; auto.
  - intros q v Hin ->; apply rows_exact in Hin.
    destruct Hin as [t [Ht ->]]; rewrite Hsub in Ht; inversion Ht; reflexivity.
Qed.

Arguments fold_c {A G R} alg s : simpl never.
Arguments fold {A G R} alg s : simpl never.
Arguments table_c {A G R} alg s : simpl never.
Arguments table {A G R} alg s : simpl never.

End Region.
