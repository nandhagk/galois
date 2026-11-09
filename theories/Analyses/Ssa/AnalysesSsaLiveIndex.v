(** * Certified search orders for liveness preparation

    Liveness preparation uses supplied search data under its independent exactness contract.
    For example, a non-back edge advances reverse postorder even when no search producer is called.
    Builds on: GraphPrepared, GraphSearchSpec and GraphSearchOrder. *)

From Stdlib Require Import List Bool PArith NArith Lia Relation_Operators.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseRel BaseSetCost BaseTrieCost.
From Galois.Graph Require Import GraphModel GraphPrepared GraphSearchSpec GraphSearchOrder.
Import List.ListNotations Cost.Notations.

Module LiveIndex.

Local Lemma arc_source_unique {N E} (p : Prepared.t N E) u v a b e :
  Prepared.arc p u e v -> Prepared.arc p a e b -> u = a.
Proof.
  intros [s [t [_ [Hs [_ [Hsource _]]]]]] [s' [t' [_ [Hs' [_ [Hsource' _]]]]]].
  assert (s = s') by congruence; subst s'; congruence.
Qed.

Local Lemma before_reverse {A} (xs : list A) u v :
  before xs u v -> before (rev xs) v u.
Proof.
  intros [left [middle [right ->]]].
  exists (rev right), (rev middle), (rev left).
  rewrite rev_app_distr; cbn [rev].
  rewrite rev_app_distr; cbn [rev].
  rewrite <- !app_assoc; reflexivity.
Qed.

Local Lemma edge_to_white {N E} (p : Prepared.t N E) scope roots r u e v :
  Search.exact p scope roots r ->
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  Prepared.arc p u e v -> before (Search.preorder r) u v -> Search.ancestor r u v.
Proof.
  intros Hexact Hu Hv Harc Hbefore.
  destruct (SearchOrder.recorded_admitted p scope roots r u Hexact Hu) as [Hvalidu Hadmitu].
  destruct (SearchOrder.recorded_admitted p scope roots r v Hexact Hv) as [Hvalidv Hadmitv].
  apply (proj2 (Search.white_path _ _ _ _ Hexact u v Hu Hv)).
  exists [e]; split.
  - econstructor; [exact Hvalidu|exact Hadmitu|exact Harc|].
    constructor; assumption.
  - split; [right; exact Hbefore|].
    intros a edge b [Heq|Hnone] Harc'; [subst edge|contradiction].
    left; symmetry; exact (arc_source_unique p u v a b e Harc Harc').
Qed.

(** Every non-back edge advances the supplied certified reverse postorder. *)
Theorem nonback_rpo {N E} (p : Prepared.t N E) scope roots r u e v :
  Search.exact p scope roots r ->
  In u (Search.preorder r) -> In v (Search.preorder r) ->
  Prepared.arc p u e v -> ~ Search.ancestor r v u -> before (SearchOrder.rpo r) u v.
Proof.
  intros Hexact Hu Hv Harc Hnonback.
  assert (Hne : u <> v).
  { intro Heq; subst v; apply Hnonback; apply rt_refl. }
  destruct (Search.paren _ _ _ _ Hexact u v Hu Hv)
    as [Hinside|[Houtside|[[Hpre Hpost]|[Hpre Hpost]]]].
  - apply (SearchOrder.rpo_ancestor p scope roots r u v Hexact Hu Hv); [|exact Hne].
    apply (proj1 (Search.ancestor_iff _ _ _ _ Hexact u v Hu Hv)); exact Hinside.
  - exfalso; apply Hnonback.
    apply (proj1 (Search.ancestor_iff _ _ _ _ Hexact v u Hv Hu)); exact Houtside.
  - apply (SearchOrder.rpo_ancestor p scope roots r u v Hexact Hu Hv); [|exact Hne].
    exact (edge_to_white p scope roots r u e v Hexact Hu Hv Harc Hpre).
  - rewrite SearchOrder.rpo_equation; apply before_reverse; exact Hpost.
Qed.

(** Missing reduced rows denote the empty set and retain the map lookup charge. *)
Definition row_c (rows : Map.t positive (FinSet.t positive)) n :=
  Map.find_or_c positive_encoding FinSet.empty n rows.

Definition row rows n := Cost.value (row_c rows n).

(** Row lookup exposes an empty result precisely when the row is absent. *)
Theorem row_equation rows n :
  row rows n =
    match Map.get positive_encoding n rows with
    | Some s => s
    | None => FinSet.empty
    end.
Proof.
  apply Map.find_or_equation.
Qed.

(** A reduced row unions its already prepared successor rows with its reflexive member. *)
Definition reduced_row_c rows n children :=
  let* self := FinSet.add_c positive_encoding n FinSet.empty in
  fold_right_c (fun child rest =>
    let* descendants := row_c rows child in
    FinSet.union_c descendants rest) self children.

Definition reduced_row rows n children := Cost.value (reduced_row_c rows n children).

(** Reduced-row preparation visits the supplied reverse-postorder once from right to left. *)
Definition reduced_rows_c (next_c : positive -> Cost.t (list positive)) order :=
  fold_right_c (fun n rows =>
    Cost.step ;;
    let* children := next_c n in
    let* descendants := reduced_row_c rows n children in
    Map.set_c positive_encoding n descendants rows) Map.empty order.

Definition reduced_rows next_c order := Cost.value (reduced_rows_c next_c order).

(** A prepared row has the literal successor-union fold used by the reduced-path proof. *)
Theorem reduced_row_equation rows n children :
  reduced_row rows n children =
    fold_right (fun child rest => FinSet.union (row rows child) rest)
      (FinSet.add positive_encoding n FinSet.empty) children.
Proof.
  unfold reduced_row, reduced_row_c; rewrite Cost.value_bind, value_fold_right_c.
  reflexivity.
Qed.

(** Reduced rows keep the original right-fold overwrite order and all successor occurrences. *)
Theorem reduced_rows_equation next_c order :
  reduced_rows next_c order =
    match order with
    | [] => Map.empty
    | n :: rest =>
      let rows := reduced_rows next_c rest in
      Map.set positive_encoding n
        (reduced_row rows n (Cost.value (next_c n))) rows
    end.
Proof.
  destruct order; unfold reduced_rows, reduced_rows_c; rewrite !value_fold_right_c;
    reflexivity.
Qed.

Local Lemma row_empty n : row Map.empty n = FinSet.empty.
Proof.
  rewrite row_equation, Map.get_empty; reflexivity.
Qed.

Local Lemma row_set rows key s n :
  Map.wf positive_encoding rows ->
  row (Map.set positive_encoding key s rows) n =
    if Pos.eq_dec n key then s else row rows n.
Proof.
  intro Hwf; rewrite !row_equation.
  destruct (Pos.eq_dec n key) as [->|Hne].
  - rewrite Map.get_set_same by exact Hwf; reflexivity.
  - rewrite Map.get_set_other by assumption || exact positive_encoding_laws; reflexivity.
Qed.

Local Lemma reduced_rows_map_wf next_c order :
  Map.wf positive_encoding (reduced_rows next_c order).
Proof.
  induction order as [|n rest IH]; rewrite reduced_rows_equation.
  - apply Map.wf_empty.
  - apply Map.wf_set; exact IH.
Qed.

Local Lemma reduced_row_wf rows n children :
  (forall child, FinSet.wf positive_encoding (row rows child)) ->
  FinSet.wf positive_encoding (reduced_row rows n children).
Proof.
  intro Hrows; rewrite reduced_row_equation.
  induction children as [|child rest IH]; cbn [fold_right].
  - apply FinSet.wf_add, FinSet.wf_empty.
  - apply FinSet.wf_union; [apply Hrows|exact IH].
Qed.

Local Lemma reduced_rows_wf next_c order n :
  FinSet.wf positive_encoding (row (reduced_rows next_c order) n).
Proof.
  revert n; induction order as [|head rest IH]; intro n; rewrite reduced_rows_equation.
  - rewrite row_empty; apply FinSet.wf_empty.
  - rewrite row_set by apply reduced_rows_map_wf.
    destruct (Pos.eq_dec n head); [|apply IH].
    apply reduced_row_wf; exact IH.
Qed.

Local Lemma reduced_row_mem rows n children u :
  (forall child, FinSet.wf positive_encoding (row rows child)) ->
  (FinSet.mem positive_encoding u (reduced_row rows n children) = true <->
    u = n \/ exists child, In child children /\
      FinSet.mem positive_encoding u (row rows child) = true).
Proof.
  intro Hrows; rewrite reduced_row_equation.
  induction children as [|child rest IH]; cbn [fold_right].
  - rewrite FinSet.mem_add by apply FinSet.wf_empty.
    rewrite FinSet.mem_empty, orb_true_iff, (eqb_true_iff _ positive_encoding_laws).
    split; [intros [Heq|Hfalse]; [exact (or_introl Heq)|discriminate]|].
    intros [Heq|[v [Hnone _]]]; [left; exact Heq|contradiction].
  - assert (Htail : FinSet.wf positive_encoding
      (fold_right (fun child rest => FinSet.union (row rows child) rest)
        (FinSet.add positive_encoding n FinSet.empty) rest)).
    { rewrite <- reduced_row_equation; apply reduced_row_wf; exact Hrows. }
    rewrite FinSet.mem_union by exact Htail || apply Hrows.
    rewrite orb_true_iff, IH; split.
    + intros [Hchild|[Heq|[v [Hv Hmem]]]].
      * right; exists child; split; [now left|exact Hchild].
      * now left.
      * right; exists v; split; [now right|exact Hmem].
    + intros [Heq|[v [[<-|Hv] Hmem]]].
      * right; now left.
      * now left.
      * right; right; exists v; auto.
Qed.

Local Lemma before_cons {A} (head n u : A) rest :
  before (head :: rest) n u ->
    (n = head /\ In u rest) \/ before rest n u.
Proof.
  intros [prefix [middle [suffix Heq]]].
  destruct prefix as [|first prefix].
  - cbn in Heq; injection Heq as Hhead Hrest.
    left; split; [symmetry; exact Hhead|].
    rewrite Hrest; apply in_or_app; right; now left.
  - cbn in Heq; injection Heq as Hhead Hrest.
    right; exists prefix, middle, suffix; exact Hrest.
Qed.

Local Lemma before_member_left {A} (xs : list A) n u :
  before xs n u -> In n xs.
Proof.
  intros [prefix [middle [suffix ->]]].
  apply in_or_app; right; now left.
Qed.

(** One reverse-postorder pass computes exactly reflexive reduced reachability. *)
Theorem reduced_rows_exact next_c order :
  NoDup order ->
  (forall n u, In n order -> In u (Cost.value (next_c n)) -> before order n u) ->
  forall n u, In n order ->
    (FinSet.mem positive_encoding u (row (reduced_rows next_c order) n) = true <->
      Rel.star (fun a b => In b (Cost.value (next_c a))) n u).
Proof.
  intro Hnodup; induction Hnodup as [|head rest Hfresh Hnodup IH];
    intros Horder n u Hn; [contradiction|].
  assert (Htail : forall a b, In a rest -> In b (Cost.value (next_c a)) ->
    before rest a b).
  { intros a b Ha Hb.
    destruct (before_cons head a b rest (Horder a b (or_intror Ha) Hb))
      as [[Heq _]|Hbefore]; [subst a; contradiction|exact Hbefore]. }
  assert (Hchildren : forall child, In child (Cost.value (next_c head)) -> In child rest).
  { intros child Hchild.
    destruct (before_cons head head child rest (Horder head child (or_introl eq_refl) Hchild))
      as [[_ Hin]|Hbefore]; [exact Hin|].
    exfalso; apply Hfresh; exact (before_member_left rest head child Hbefore). }
  rewrite reduced_rows_equation, row_set by apply reduced_rows_map_wf.
  destruct (Pos.eq_dec n head) as [->|Hne].
  - rewrite reduced_row_mem by apply reduced_rows_wf; split.
    + intros [->|[child [Hchild Hmem]]]; [constructor|].
      econstructor; [exact Hchild|].
      apply (proj1 (IH Htail child u (Hchildren child Hchild))); exact Hmem.
    + intro Hpath; inversion Hpath as [|a child dest Hchild Hsuffix]; subst.
      * now left.
      * right; exists child; split; [exact Hchild|].
        apply (proj2 (IH Htail child u (Hchildren child Hchild))); exact Hsuffix.
  - apply IH; [exact Htail|].
    destruct Hn as [Heq|Hn]; [congruence|exact Hn].
Qed.

(** A row stores valid keys from the supplied finite preparation inventory. *)
Definition supported inventory (s : FinSet.t positive) : Prop :=
  FinSet.wf positive_encoding s /\
  forall u, FinSet.mem positive_encoding u s = true -> In u inventory.

Local Lemma supported_empty inventory : supported inventory FinSet.empty.
Proof.
  split; [apply FinSet.wf_empty|].
  intros u Hu; rewrite FinSet.mem_empty in Hu; discriminate.
Qed.

Local Lemma supported_self inventory n :
  In n inventory -> supported inventory (FinSet.add positive_encoding n FinSet.empty).
Proof.
  intro Hn; split; [apply FinSet.wf_add, FinSet.wf_empty|].
  intros u Hu; rewrite FinSet.mem_add_raw, FinSet.mem_empty in Hu.
  apply orb_true_iff in Hu as [Hu|Hu]; [|discriminate].
  apply (eqb_true_iff _ positive_encoding_laws) in Hu; subst u; exact Hn.
Qed.

Local Lemma supported_union inventory a b :
  supported inventory a -> supported inventory b -> supported inventory (FinSet.union a b).
Proof.
  intros [Hawf Ha] [Hbwf Hb]; split.
  - apply FinSet.wf_union; assumption.
  - intros u Hu; rewrite FinSet.mem_union in Hu by assumption.
    apply orb_true_iff in Hu as [Hu|Hu]; [apply Ha|apply Hb]; exact Hu.
Qed.

Local Lemma reduced_row_supported inventory rows n children :
  In n inventory ->
  (forall child, supported inventory (row rows child)) ->
  supported inventory (reduced_row rows n children).
Proof.
  intros Hn Hrows; rewrite reduced_row_equation.
  induction children as [|child rest IH]; cbn [fold_right].
  - apply supported_self; exact Hn.
  - apply supported_union; [apply Hrows|exact IH].
Qed.

Local Lemma reduced_rows_supported next_c order n :
  supported order (row (reduced_rows next_c order) n).
Proof.
  revert n; induction order as [|head rest IH]; intro n; rewrite reduced_rows_equation.
  - rewrite row_empty; apply supported_empty.
  - assert (Htail : forall child,
      supported (head :: rest) (row (reduced_rows next_c rest) child)).
    { intro child; destruct (IH child) as [Hwf Hsupport]; split; [exact Hwf|].
      intros u Hu; right; apply Hsupport; exact Hu. }
    rewrite row_set by apply reduced_rows_map_wf.
    destruct (Pos.eq_dec n head).
    + apply reduced_row_supported; [now left|exact Htail].
    + apply Htail.
Qed.

Local Lemma supported_size inventory s :
  supported inventory s -> (FinSet.size s <= length inventory)%nat.
Proof.
  intros [Hwf Hsupport]; rewrite FinSet.size_elements.
  apply NoDup_incl_length.
  - apply (FinSet.elements_nodup positive_encoding); exact Hwf.
  - intros u Hu; apply Hsupport.
    apply (proj1 (FinSet.elements_spec _ positive_encoding_laws u s Hwf)); exact Hu.
Qed.

(** Scalar-ID lookup pays its actual encoder and queried-key width. *)
Theorem row_cost rows n :
  Cost.ticks (row_c rows n) = (2 + key_bits positive_encoding n)%N.
Proof.
  unfold row_c; rewrite Map.find_or_cost, Map.get_cost.
  rewrite positive_encoding_cost, positive_encoding_equation, <- positive_encoding_bits.
  reflexivity.
Qed.

(** The row-union price bounds the actual supported right operand, including its unit callback. *)
Definition row_union_price count width :=
  ((TrieCost.trie_k + 1) * (1 + count * width))%N.

Local Lemma supported_union_cost inventory left right width :
  supported inventory right ->
  (forall u, In u inventory -> (key_bits positive_encoding u <= width)%N) ->
  (Cost.ticks (FinSet.union_c left right) <=
    row_union_price (N.of_nat (length inventory)) width)%N.
Proof.
  intros Hsupport Hwidth.
  pose proof (FinSetCost.union_numeric_cost_right positive_encoding left right width
    (proj1 Hsupport) (fun u Hu => Hwidth u (proj2 Hsupport u Hu))) as Hcost.
  pose proof (supported_size inventory right Hsupport) as Hsize.
  unfold row_union_price; eapply N.le_trans; [exact Hcost|].
  apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r; lia.
Qed.

(** Reduced-row work includes self insertion, successor lookups and each actual trie union. *)
Theorem reduced_row_cost inventory rows n children width :
  In n inventory -> incl children inventory ->
  (forall child, supported inventory (row rows child)) ->
  (forall u, In u inventory -> (key_bits positive_encoding u <= width)%N) ->
  (Cost.ticks (reduced_row_c rows n children) <=
    2 + width + N.of_nat (length children) *
      (3 + width + row_union_price (N.of_nat (length inventory)) width))%N.
Proof.
  intros Hn Hchildren Hrows Hwidth.
  unfold reduced_row_c; rewrite Cost.ticks_bind.
  set (price := (2 + width + row_union_price (N.of_nat (length inventory)) width)%N).
  pose proof (ticks_fold_right_c_potential
    (fun child rest => let* descendants := row_c rows child in
      FinSet.union_c descendants rest)
    (supported inventory) (fun _ => 0%N) price children
    (FinSet.add positive_encoding n FinSet.empty)) as Hfold.
  assert (Hstep : forall child rest, In child children -> supported inventory rest ->
    supported inventory (Cost.value
      (let* descendants := row_c rows child in FinSet.union_c descendants rest)) /\
    (Cost.ticks (let* descendants := row_c rows child in FinSet.union_c descendants rest) +
      0 <= price + 0)%N).
  { intros child rest Hchild Hrest; split.
    - rewrite Cost.value_bind; apply supported_union; [apply Hrows|exact Hrest].
    - rewrite Cost.ticks_bind, row_cost.
      pose proof (Hwidth child (Hchildren child Hchild)) as Hkey.
      pose proof (supported_union_cost inventory (row rows child) rest width Hrest Hwidth)
        as Hunion.
      unfold price; change (2 + key_bits positive_encoding child +
        Cost.ticks (FinSet.union_c (row rows child) rest) + 0 <=
        2 + width + row_union_price (N.of_nat (length inventory)) width + 0)%N.
      lia. }
  destruct (Hfold Hstep (supported_self inventory n Hn)) as [_ Hfoldcost].
  cbn beta in Hfoldcost.
  rewrite FinSet.add_cost, positive_encoding_cost, positive_encoding_equation.
  rewrite <- positive_encoding_bits.
  fold (FinSet.add positive_encoding n FinSet.empty).
  pose proof (Hwidth n Hn) as Hkey.
  unfold price in Hfoldcost; nia.
Qed.

(** The per-vertex price includes dispatch, callback, self/update work and bounded adjacency work. *)
Definition reduced_vertex_price callback degree count width :=
  (2 + callback + 2 * (2 + width) +
    N.of_nat degree * (3 + width + row_union_price count width))%N.

Local Lemma rows_set_supported inventory rows n s :
  Map.wf positive_encoding rows ->
  (forall child, supported inventory (row rows child)) -> supported inventory s ->
  forall child, supported inventory (row (Map.set positive_encoding n s rows) child).
Proof.
  intros Hmap Hrows Hs child; rewrite row_set by exact Hmap.
  destruct (Pos.eq_dec child n); [exact Hs|apply Hrows].
Qed.

(** The entire reduced-row pass is bounded by primitive callback, adjacency and stored-key widths. *)
Theorem reduced_rows_cost next_c order width callback degree :
  (forall u, In u order -> (key_bits positive_encoding u <= width)%N) ->
  (forall n, In n order ->
    incl (Cost.value (next_c n)) order /\
    (length (Cost.value (next_c n)) <= degree)%nat /\
    (Cost.ticks (next_c n) <= callback)%N) ->
  (Cost.ticks (reduced_rows_c next_c order) <=
    N.of_nat (length order) *
      reduced_vertex_price callback degree (N.of_nat (length order)) width)%N.
Proof.
  intros Hwidth Hnext.
  set (invariant := fun rows : Map.t positive (FinSet.t positive) =>
    Map.wf positive_encoding rows /\ forall child, supported order (row rows child)).
  set (price := (reduced_vertex_price callback degree (N.of_nat (length order)) width - 1)%N).
  assert (Hstep : forall n rows, In n order -> invariant rows ->
    invariant (Cost.value
      (Cost.step ;; let* children := next_c n in
       let* descendants := reduced_row_c rows n children in
       Map.set_c positive_encoding n descendants rows)) /\
    (Cost.ticks
      (Cost.step ;; let* children := next_c n in
       let* descendants := reduced_row_c rows n children in
       Map.set_c positive_encoding n descendants rows) + 0 <= price + 0)%N).
  { intros n rows Hn [Hmap Hrows].
    destruct (Hnext n Hn) as [Hchildren [Hdegree Hcallback]].
    split.
    - autorewrite with galois_cost; split; [apply Map.wf_set; exact Hmap|].
      apply rows_set_supported; [exact Hmap|exact Hrows|].
      apply reduced_row_supported; assumption.
    - rewrite !Cost.ticks_bind, Cost.ticks_step, Map.set_cost.
      rewrite positive_encoding_cost, positive_encoding_equation, <- positive_encoding_bits.
      pose proof (reduced_row_cost order rows n (Cost.value (next_c n)) width
        Hn Hchildren Hrows Hwidth) as Hrow.
      pose proof (Hwidth n Hn) as Hkey.
      unfold price, reduced_vertex_price; nia. }
  assert (Hinitial : invariant Map.empty).
  { split; [apply Map.wf_empty|].
    intro child; rewrite row_empty; apply supported_empty. }
  unfold reduced_rows_c.
  destruct (ticks_fold_right_c_potential _ invariant (fun _ => 0%N) price order Map.empty
    Hstep Hinitial) as [_ Hcost].
  cbn beta in Hcost.
  unfold price, reduced_vertex_price in Hcost |- *; nia.
Qed.

(** Uniformly varying reduced-row families retain the full traversal and primitive numeric prices. *)
Theorem reduced_rows_bigO {X} (next : X -> positive -> Cost.t (list positive))
    (order : X -> list positive) width callback degree :
  (forall x u, In u (order x) -> (key_bits positive_encoding u <= width x)%N) ->
  (forall x n, In n (order x) ->
    incl (Cost.value (next x n)) (order x) /\
    (length (Cost.value (next x n)) <= degree x)%nat /\
    (Cost.ticks (next x n) <= callback x)%N) ->
  bigO
    (fun x => (N.of_nat (length (order x)) *
      reduced_vertex_price (callback x) (degree x) (N.of_nat (length (order x))) (width x))%N)
    (fun x => Cost.ticks (reduced_rows_c (next x) (order x))).
Proof.
  intros Hwidth Hnext; exists 1%N; intro x.
  pose proof (reduced_rows_cost (next x) (order x) (width x) (callback x) (degree x)
    (Hwidth x) (Hnext x)) as Hcost; nia.
Qed.

End LiveIndex.
Import LiveIndex.
