(** * Semi-NCA forward settlement

    A forward pass walks already settled parents to the semidominator rank threshold.
    For example, either arm at a diamond's join walks to the common branching ancestor.
    Builds on: the shared GraphDomSemi data and GraphDomRank numeric comparisons. *)

From Stdlib Require Import List PArith NArith Arith.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphDomSemi GraphDomLink GraphDomRank.
Import Cost.Notations.

Module DomNca.

Definition walk_body_c limit (m : Map.t positive positive) v
    (rec : forall a, (Pos.to_nat a < Pos.to_nat v)%nat -> Cost.t positive) :=
  Cost.step ;;
  let* order := DomRank.compare_c v limit in
  match order with
  | Eq => Cost.ret v
  | Lt => Cost.ret v
  | Gt =>
    let* parent := Map.get_c positive_encoding v m in
    match parent with
    | None => Cost.ret v
    | Some parent =>
      let* decrease := DomRank.smaller_c parent v in
      match decrease with
      | left Hsmaller => rec parent Hsmaller
      | right _ => Cost.ret v
      end
    end
  end.

(** The walk recurses on the actual discovery rank and requires no unary fuel conversion. *)
Definition walk_c limit m := fix_wf Pos.to_nat (walk_body_c limit m).

Local Lemma cost_ext {A} (m n : Cost.t A) :
  Cost.value m = Cost.value n -> Cost.ticks m = Cost.ticks n -> m = n.
Proof.
  destruct m as [v ticks], n as [w work]. cbn.
  intros Hvalue Hticks. subst w work. reflexivity.
Qed.

Local Lemma walk_ext limit m v f g :
  (forall a H, f a H = g a H) -> walk_body_c limit m v f = walk_body_c limit m v g.
Proof.
  intro Hagree. apply cost_ext; unfold walk_body_c; autorewrite with galois_cost;
    destruct (Cost.value (DomRank.compare_c v limit)); autorewrite with galois_cost;
    try reflexivity; fold (Map.get positive_encoding v m);
    destruct (Map.get positive_encoding v m) as [parent|];
    autorewrite with galois_cost; try reflexivity;
    destruct (Cost.value (DomRank.smaller_c parent v)) as [Hsmaller|Hsmaller];
    autorewrite with galois_cost; [rewrite Hagree| |rewrite Hagree|]; reflexivity.
Qed.

(** The walk equation exposes one threshold test and a possible strict rank descent. *)
Theorem walk_equation limit m v :
  walk_c limit m v = walk_body_c limit m v (fun a _ => walk_c limit m a).
Proof.
  apply fix_wf_unfold. apply walk_ext.
Qed.

(** The actual walk returns at the threshold and otherwise follows only a checked decreasing binding. *)
Theorem walk_value limit m v :
  Cost.value (walk_c limit m v) =
    match Pos.compare v limit with
    | Gt =>
      match Map.get positive_encoding v m with
      | None => v
      | Some parent =>
        match Cost.value (DomRank.smaller_c parent v) with
        | left _ => Cost.value (walk_c limit m parent)
        | right _ => v
        end
      end
    | _ => v
    end.
Proof.
  rewrite walk_equation. unfold walk_body_c. autorewrite with galois_cost.
  rewrite DomRank.compare_value. destruct (Pos.compare v limit); [reflexivity|reflexivity|].
  autorewrite with galois_cost. fold (Map.get positive_encoding v m).
  destruct (Map.get positive_encoding v m); [|reflexivity].
  autorewrite with galois_cost. destruct (Cost.value (DomRank.smaller_c p v));
    autorewrite with galois_cost; reflexivity.
Qed.

Definition step_c {L} (ranked : DomSemi.layout L) semis m v :=
  let* parent := Map.get_c positive_encoding v (DomSemi.parents ranked) in
  match parent with
  | None => Cost.ret m
  | Some parent =>
    let* limit := DomLink.identity_value_c semis v in
    let* ancestor := walk_c limit m parent in
    Map.set_c positive_encoding v ancestor m
  end.

(** The Semi-NCA finisher consumes the same prologue without another virtual-graph search. *)
Definition finish_c {V E} (shared : DomSemi.semi V E) :=
  let* order := rev_c (DomSemi.reverse_order (DomSemi.ranked shared)) in
  fold_left_c
    (step_c (DomSemi.ranked shared) (DomSemi.semis (DomSemi.settled shared)))
    order Map.empty.

Definition finish {V E} (shared : DomSemi.semi V E) := Cost.value (finish_c shared).

(** One forward step stores the actual threshold walk from the recorded DFS parent. *)
Theorem step_value {L} (ranked : DomSemi.layout L) semis m v :
  Cost.value (step_c ranked semis m v) =
    match Map.get positive_encoding v (DomSemi.parents ranked) with
    | None => m
    | Some parent => Map.set positive_encoding v
        (Cost.value (walk_c (DomLink.identity_value semis v) m parent)) m
    end.
Proof.
  unfold step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (DomSemi.parents ranked)).
  destruct (Map.get positive_encoding v (DomSemi.parents ranked)); [|reflexivity].
  autorewrite with galois_cost. reflexivity.
Qed.

(** The finisher is exactly its actual increasing-rank forward fold. *)
Theorem finish_value {V E} (shared : DomSemi.semi V E) :
  finish shared =
    fold_left (fun m v => Cost.value
      (step_c (DomSemi.ranked shared) (DomSemi.semis (DomSemi.settled shared)) m v))
      (rev (DomSemi.reverse_order (DomSemi.ranked shared))) Map.empty.
Proof.
  unfold finish, finish_c. autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma step_wf {L} (ranked : DomSemi.layout L) semis m v :
  Map.wf positive_encoding m ->
  Map.wf positive_encoding (Cost.value (step_c ranked semis m v)).
Proof.
  intro Hmap. unfold step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (DomSemi.parents ranked)).
  destruct (Map.get positive_encoding v (DomSemi.parents ranked));
    autorewrite with galois_cost; [now apply Map.wf_set|exact Hmap].
Qed.

Local Lemma fold_wf {L} (ranked : DomSemi.layout L) semis xs :
  forall m, Map.wf positive_encoding m ->
  Map.wf positive_encoding
    (fold_left (fun m v => Cost.value (step_c ranked semis m v)) xs m).
Proof.
  induction xs as [|v rest IH]; intros m Hmap; [exact Hmap|].
  cbn [fold_left]. apply IH. now apply step_wf.
Qed.

(** Semi-NCA's output has canonical storage for every computational prologue value. *)
Theorem finish_wf {V E} (shared : DomSemi.semi V E) :
  Map.wf positive_encoding (finish shared).
Proof.
  unfold finish, finish_c. rewrite Cost.value_bind, value_fold_left_c.
  apply fold_wf. apply Map.wf_empty.
Qed.

End DomNca.
