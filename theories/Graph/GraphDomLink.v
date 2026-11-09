(** * Link and evaluation on discovery-rank IDs

    Shortcuts compress paths whose vertex IDs are their strictly decreasing discovery ranks.
    For example, linking rank three below rank two permits a query to compress their path.
    Builds on: GraphDomRank, explicit maps and CostLoop well-founded recursion. *)

From Stdlib Require Import PArith NArith Arith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap.
From Galois.Graph Require Import GraphDomRank.
Import Cost.Notations.

Module DomLink.

(** The original forest is retained independently of compressed shortcuts and segment labels. *)
Record t := Links {
  original : Map.t positive positive;
  shortcut : Map.t positive positive;
  labels : Map.t positive positive
}.

Definition empty := Links Map.empty Map.empty Map.empty.

(** Absence represents the identity function for unsettled scores and implicit self labels. *)
Definition identity_value_c (m : Map.t positive positive) v :=
  let* stored := Map.get_c positive_encoding v m in
  Cost.ret (match stored with
    | Some value => value
    | None => v
    end).

Definition identity_value m v := Cost.value (identity_value_c m v).

(** Identity-valued maps have a specified self value at absent keys, rather than an absent rank. *)
Theorem identity_value_equation m v :
  identity_value m v =
    match Map.get positive_encoding v m with
    | Some value => value
    | None => v
    end.
Proof.
  reflexivity.
Qed.

(** Minimum selection retains the left argument when the returned scores tie. *)
Definition minimum_c (score : positive -> Cost.t positive) u v :=
  Cost.step ;;
  let* a := score u in
  Cost.step ;;
  let* b := score v in
  let* order := DomRank.compare_c a b in
  Cost.ret (match order with
    | Gt => v
    | _ => u
    end).

(** Minimum selection compares the actual callback values and keeps the left argument at a tie. *)
Theorem minimum_value score u v :
  Cost.value (minimum_c score u v) =
    match Pos.compare (Cost.value (score u)) (Cost.value (score v)) with
    | Gt => v
    | _ => u
    end.
Proof.
  unfold minimum_c. autorewrite with galois_cost.
  now rewrite DomRank.compare_value.
Qed.

Definition query := (t * (positive * option positive))%type.

(** One compression layer preserves the original links and updates only shortcut metadata. *)
Definition compress_body_c (score : positive -> Cost.t positive) (st : t) v
    (rec : forall a, (Pos.to_nat a < Pos.to_nat v)%nat -> Cost.t query) : Cost.t query :=
  Cost.step ;;
  let* parent := Map.get_c positive_encoding v (shortcut st) in
  match parent with
  | None => Cost.ret (st, (v, None))
  | Some a =>
    let* smaller := DomRank.smaller_c a v in
    match smaller with
    | right _ => Cost.ret (st, (v, None))
    | left Hsmaller =>
      let* result := rec a Hsmaller in
      let '(st', (root, part)) := result in
      let* label := identity_value_c (labels st) v in
      let* best :=
        match part with
        | None => Cost.ret label
        | Some u => minimum_c score label u
        end in
      let* shortcuts := Map.set_c positive_encoding v root (shortcut st') in
      let* labels := Map.set_c positive_encoding v best (labels st') in
      Cost.ret (Links (original st') shortcuts labels, (root, Some best))
    end
  end.

(** Compression follows the actual numeric rank and has no fuel conversion or default rank. *)
Definition compress_c score st :=
  fix_wf Pos.to_nat (compress_body_c score st).

Local Lemma cost_ext {A} (m n : Cost.t A) :
  Cost.value m = Cost.value n -> Cost.ticks m = Cost.ticks n -> m = n.
Proof.
  destruct m as [v ticks], n as [w work]. cbn.
  intros Hvalue Hticks. subst w work. reflexivity.
Qed.

Local Lemma compress_ext score st v f g :
  (forall a H, f a H = g a H) ->
  compress_body_c score st v f = compress_body_c score st v g.
Proof.
  intro Hagree. apply cost_ext; unfold compress_body_c; autorewrite with galois_cost;
    fold (Map.get positive_encoding v (shortcut st));
    destruct (Map.get positive_encoding v (shortcut st)) as [a|];
    autorewrite with galois_cost; try reflexivity;
    destruct (Cost.value (DomRank.smaller_c a v)) as [Hsmaller|Hsmaller];
    autorewrite with galois_cost; [rewrite Hagree| |rewrite Hagree|]; reflexivity.
Qed.

(** The compression equation exposes one rank-decreasing step through the shared recursion wrapper. *)
Theorem compress_equation score st v :
  compress_c score st v =
    compress_body_c score st v (fun a _ => compress_c score st a).
Proof.
  apply fix_wf_unfold. apply compress_ext.
Qed.

(** Compression's value equation retains the exact returned recursive state and selected labels. *)
Theorem compress_value score st v :
  Cost.value (compress_c score st v) =
    match Map.get positive_encoding v (shortcut st) with
    | None => (st, (v, None))
    | Some a =>
      match Cost.value (DomRank.smaller_c a v) with
      | right _ => (st, (v, None))
      | left _ =>
        let '(st', (root, part)) := Cost.value (compress_c score st a) in
        let label := identity_value (labels st) v in
        let best := match part with
          | None => label
          | Some u => Cost.value (minimum_c score label u)
          end in
        (Links (original st')
          (Map.set positive_encoding v root (shortcut st'))
          (Map.set positive_encoding v best (labels st')), (root, Some best))
      end
    end.
Proof.
  rewrite compress_equation. unfold compress_body_c.
  autorewrite with galois_cost. fold (Map.get positive_encoding v (shortcut st)).
  destruct (Map.get positive_encoding v (shortcut st)) as [a|]; [|reflexivity].
  autorewrite with galois_cost.
  destruct (Cost.value (DomRank.smaller_c a v)) as [Hsmaller|Hnot];
    autorewrite with galois_cost; [|reflexivity].
  destruct (Cost.value (compress_c score st a)) as [st' [root part]].
  fold (identity_value (labels st) v).
  destruct part; autorewrite with galois_cost; reflexivity.
Qed.

(** Evaluation retains the selected nonroot label and compression updates. *)
Definition eval_c score st v :=
  let* result := compress_c score st v in
  let '(st', (_, part)) := result in
  Cost.ret (st', match part with
    | None => v
    | Some best => best
    end).

(** Evaluation selects the actual compression result and retains the returned compressed state. *)
Theorem eval_value score st v :
  Cost.value (eval_c score st v) =
    let '(st', (_, part)) := Cost.value (compress_c score st v) in
    (st', match part with
      | None => v
      | Some best => best
      end).
Proof.
  unfold eval_c. rewrite Cost.value_bind.
  destruct (Cost.value (compress_c score st v)) as [st' [root part]]. reflexivity.
Qed.

(** Linking starts a one-vertex label segment at a previously unlinked vertex. *)
Definition link_c st v parent :=
  let* original := Map.set_c positive_encoding v parent (original st) in
  let* shortcut := Map.set_c positive_encoding v parent (shortcut st) in
  let* labels := Map.set_c positive_encoding v v (labels st) in
  Cost.ret (Links original shortcut labels).

(** Linking sets all three actual maps and starts the new vertex's identity label. *)
Theorem link_value st v parent :
  Cost.value (link_c st v parent) =
    Links (Map.set positive_encoding v parent (original st))
      (Map.set positive_encoding v parent (shortcut st))
      (Map.set positive_encoding v v (labels st)).
Proof.
  reflexivity.
Qed.

End DomLink.
