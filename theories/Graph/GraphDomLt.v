(** * Lengauer-Tarjan bucket settlement

    Reverse bucket processing installs provisional parents and a forward pass corrects them.
    For example, a diamond's join is corrected to its branching ancestor.
    Builds on: the shared GraphDomSemi data and GraphDomLink evaluation. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseIndex.
From Galois.Graph Require Import GraphDomSemi GraphDomLink GraphDomRank.
Import List.ListNotations Cost.Notations.

Module DomLt.

Definition bucket_insert_c (semis : Map.t positive positive)
    (buckets : Map.t positive (list positive)) v :=
  let* semi := Map.get_c positive_encoding v semis in
  match semi with
  | None => Cost.ret buckets
  | Some s =>
    let* members := Index.find_c positive_encoding s buckets in
    Map.set_c positive_encoding s (v :: members) buckets
  end.

(** Bucket insertion retains the actual stored semidominator and prepends one occurrence. *)
Theorem bucket_insert_value semis buckets v :
  Cost.value (bucket_insert_c semis buckets v) =
    match Map.get positive_encoding v semis with
    | None => buckets
    | Some s => Map.set positive_encoding s
        (v :: Index.find positive_encoding s buckets) buckets
    end.
Proof.
  unfold bucket_insert_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v semis).
  destruct (Map.get positive_encoding v semis); autorewrite with galois_cost; reflexivity.
Qed.

(** The bucket observer is the value of the actual charged insertion fold. *)
Definition bucket_index semis order :=
  Cost.value (fold_left_c (bucket_insert_c semis) order Map.empty).

(** The actual bucket index follows its insertion fold on arbitrary computational maps. *)
Theorem bucket_index_value semis order :
  bucket_index semis order =
    fold_left (fun buckets v => Cost.value (bucket_insert_c semis buckets v)) order Map.empty.
Proof.
  unfold bucket_index. apply value_fold_left_c.
Qed.

Record state := State {
  links : DomLink.t;
  provisional : Map.t positive positive
}.

Definition member_c semis s st v :=
  let* result := DomLink.eval_c (DomLink.identity_value_c semis) (links st) v in
  let '(links', u) := result in
  let* score := DomLink.identity_value_c semis u in
  let* order := DomRank.compare_c score s in
  let parent := match order with
    | Lt => u
    | _ => s
    end in
  let* provisional := Map.set_c positive_encoding v parent (provisional st) in
  Cost.ret (State links' provisional).

(** A bucket member stores the actual evaluated representative only for a strictly lower score. *)
Theorem member_value semis s st v :
  Cost.value (member_c semis s st v) =
    let '(links', u) :=
      Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) (links st) v) in
    State links' (Map.set positive_encoding v
      (match Pos.compare (DomLink.identity_value semis u) s with
      | Lt => u
      | _ => s
      end) (provisional st)).
Proof.
  unfold member_c. autorewrite with galois_cost.
  destruct (Cost.value (DomLink.eval_c (DomLink.identity_value_c semis) (links st) v)).
  autorewrite with galois_cost. rewrite DomRank.compare_value. reflexivity.
Qed.

(** A bucket is settled before the bucket root receives its DFS parent link. *)
Definition reverse_step_c {L} (ranked : DomSemi.layout L) semis buckets st s :=
  let* members := Index.find_c positive_encoding s buckets in
  let* st' := fold_left_c (member_c semis s) members st in
  let* parent := Map.get_c positive_encoding s (DomSemi.parents ranked) in
  match parent with
  | None => Cost.ret st'
  | Some parent =>
    let* links := DomLink.link_c (links st') s parent in
    Cost.ret (State links (provisional st'))
  end.

(** Reverse settlement folds the actual bucket before adding the current recorded parent link. *)
Theorem reverse_step_value {L} (ranked : DomSemi.layout L) semis buckets st s :
  Cost.value (reverse_step_c ranked semis buckets st s) =
    let st' := fold_left (fun st v => Cost.value (member_c semis s st v))
      (Index.find positive_encoding s buckets) st in
    match Map.get positive_encoding s (DomSemi.parents ranked) with
    | None => st'
    | Some parent =>
      State (Cost.value (DomLink.link_c (links st') s parent)) (provisional st')
    end.
Proof.
  unfold reverse_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding s (DomSemi.parents ranked)).
  destruct (Map.get positive_encoding s (DomSemi.parents ranked)); reflexivity.
Qed.

Definition correct_step_c semis provisional corrected v :=
  let* parent := Map.get_c positive_encoding v provisional in
  match parent with
  | None => Cost.ret corrected
  | Some parent =>
    let* semi := DomLink.identity_value_c semis v in
    let* direct := positive_eqb_c parent semi in
    let* corrected_parent :=
      if direct then Cost.ret parent else DomLink.identity_value_c corrected parent in
    Map.set_c positive_encoding v corrected_parent corrected
  end.

(** Forward correction either retains the semidominator or reads the earlier corrected parent. *)
Theorem correct_step_value semis provisional corrected v :
  Cost.value (correct_step_c semis provisional corrected v) =
    match Map.get positive_encoding v provisional with
    | None => corrected
    | Some parent => Map.set positive_encoding v
        (if Pos.eqb parent (DomLink.identity_value semis v) then parent
        else DomLink.identity_value corrected parent) corrected
    end.
Proof.
  unfold correct_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v provisional).
  destruct (Map.get positive_encoding v provisional); [|reflexivity].
  autorewrite with galois_cost. rewrite positive_eqb_equation.
  fold (DomLink.identity_value semis v).
  destruct (Pos.eqb p (DomLink.identity_value semis v));
    autorewrite with galois_cost; reflexivity.
Qed.

(** The LT finisher consumes the shared prologue and never constructs or searches a virtual graph. *)
Definition finish_c {V E} (shared : DomSemi.semi V E) :=
  let ranked := DomSemi.ranked shared in
  let semis := DomSemi.semis (DomSemi.settled shared) in
  let* order := rev_c (DomSemi.reverse_order ranked) in
  let* buckets := fold_left_c (bucket_insert_c semis) order Map.empty in
  let* reverse := fold_left_c (reverse_step_c ranked semis buckets)
    (DomSemi.reverse_order ranked) (State DomLink.empty Map.empty) in
  fold_left_c (correct_step_c semis (provisional reverse)) order Map.empty.

Definition finish {V E} (shared : DomSemi.semi V E) := Cost.value (finish_c shared).

(** The reverse observer is the value of the same actual bucket-building and settlement folds. *)
Definition reverse_result {V E} (shared : DomSemi.semi V E) :=
  let ranked := DomSemi.ranked shared in
  let semis := DomSemi.semis (DomSemi.settled shared) in
  Cost.value (fold_left_c
    (reverse_step_c ranked semis (bucket_index semis (rev (DomSemi.reverse_order ranked))))
    (DomSemi.reverse_order ranked) (State DomLink.empty Map.empty)).

(** The stored reverse result is the actual reverse fold over the same computed bucket index. *)
Theorem reverse_result_value {V E} (shared : DomSemi.semi V E) :
  reverse_result shared =
    fold_left (fun st s => Cost.value (reverse_step_c (DomSemi.ranked shared)
      (DomSemi.semis (DomSemi.settled shared))
      (bucket_index (DomSemi.semis (DomSemi.settled shared))
        (rev (DomSemi.reverse_order (DomSemi.ranked shared)))) st s))
      (DomSemi.reverse_order (DomSemi.ranked shared)) (State DomLink.empty Map.empty).
Proof.
  unfold reverse_result. apply value_fold_left_c.
Qed.

(** The actual finisher corrects precisely the provisional map from its actual reverse result. *)
Theorem finish_value {V E} (shared : DomSemi.semi V E) :
  finish shared =
    fold_left (fun corrected v => Cost.value (correct_step_c
      (DomSemi.semis (DomSemi.settled shared)) (provisional (reverse_result shared)) corrected v))
      (rev (DomSemi.reverse_order (DomSemi.ranked shared))) Map.empty.
Proof.
  unfold finish, finish_c, reverse_result, bucket_index.
  autorewrite with galois_cost. reflexivity.
Qed.

Local Lemma correct_step_wf semis provisional corrected v :
  Map.wf positive_encoding corrected ->
  Map.wf positive_encoding (Cost.value (correct_step_c semis provisional corrected v)).
Proof.
  intro Hmap. unfold correct_step_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v provisional).
  destruct (Map.get positive_encoding v provisional); autorewrite with galois_cost;
    [|exact Hmap].
  apply Map.wf_set. exact Hmap.
Qed.

Local Lemma correct_fold_wf semis provisional xs :
  forall corrected, Map.wf positive_encoding corrected ->
  Map.wf positive_encoding
    (fold_left (fun m v => Cost.value (correct_step_c semis provisional m v)) xs corrected).
Proof.
  induction xs as [|v rest IH]; intros corrected Hmap; [exact Hmap|].
  cbn [fold_left]. apply IH. now apply correct_step_wf.
Qed.

(** LT's corrected output has canonical storage for every computational prologue value. *)
Theorem finish_wf {V E} (shared : DomSemi.semi V E) :
  Map.wf positive_encoding (finish shared).
Proof.
  unfold finish, finish_c. rewrite !Cost.value_bind, value_fold_left_c.
  apply correct_fold_wf. apply Map.wf_empty.
Qed.

End DomLt.
