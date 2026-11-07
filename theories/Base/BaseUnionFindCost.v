(** * Callee-relative and finite-support union-find bounds

    Query budgets include encoding and actual queried widths, including keys outside support.
    For example, an unknown key needs its own encoding budget even when the known forest is empty.
    Builds on: BaseUnionFindRank, BaseUnionFindLoop and the public Map cost contracts. *)

From Stdlib Require Import List NArith PArith PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind BaseUnionFindLoop
  BaseUnionFindRank BaseHeapLoop.
Import List.ListNotations.

Module UnionFindCost.

Local Open Scope N_scope.

(** A key budget retains both the encoder's charge and the actual encoded width. *)
Definition key_bound {K} (E : encoding K) w (k : K) : Prop :=
  Cost.ticks (encode_c E k) + N.pos (Pos.size (encode E k)) <= w.

(** Known-key budgets range over finite stored support and leave unknown queries explicit. *)
Definition support_budget {K} (E : encoding K) w (uf : UnionFind.t K) : Prop :=
  forall k, UnionFind.support E uf k -> key_bound E w k.

(** The common numeric constant covers two walks, compression and root-link bookkeeping. *)
Definition uf_k : N := 128.

(** Each primitive compression update is budgeted at the accumulator it actually receives. *)
Fixpoint compression_budget {K} (E : encoding K) root path (uf : UnionFind.t K) u : Prop :=
  match path with
  | [] => True
  | key :: rest =>
    Cost.ticks (Map.set_c E key root (UnionFind.parents uf)) <= u /\
    compression_budget E root rest (UnionFind.redirect E key root uf) u
  end.

(** Primitive update budgets compose through the actual compression fold. *)
Theorem compression_cost {K} (E : encoding K) root path (uf : UnionFind.t K) u :
  compression_budget E root path uf u ->
  Cost.ticks (fold_left_c (fun acc key => UnionFind.redirect_c E key root acc) path uf) <=
    N.of_nat (length path) * (1 + u).
Proof.
  revert uf. induction path as [|key path IH]; intros uf Hbudget.
  - reflexivity.
  - destruct Hbudget as [Hset Hrest].
    rewrite ticks_fold_left_c_cons, UnionFind.redirect_cost.
    specialize (IH _ Hrest). cbn [length]. rewrite Nat2N.inj_succ.
    change (1 + Cost.ticks (Map.set_c E key root (UnionFind.parents uf)) +
      Cost.ticks (fold_left_c (fun acc key => UnionFind.redirect_c E key root acc)
        path (UnionFind.redirect E key root uf)) <=
      N.succ (N.of_nat (length path)) * (1 + u)).
    nia.
Qed.

(** A bounded find composes its closed-domain lookup budget and reached compression updates. *)
Theorem find_fuel_cost_callee {K} (E : encoding K) fuel x uf (allowed : K -> Prop) g u :
  allowed x ->
  (forall a b, allowed a -> Map.get E a (UnionFind.parents uf) = Some b -> allowed b) ->
  (forall a, allowed a -> Cost.ticks (Map.get_c E a (UnionFind.parents uf)) <= g) ->
  (let '(root, path) := Cost.value (UnionFindLoop.walk_c E (UnionFind.parents uf) fuel x) in
    compression_budget E root path uf u) ->
  Cost.ticks (UnionFind.find_fuel_c E fuel x uf) <=
    (g + 2) * (N.of_nat fuel + 1) +
    2 * N.pos (Pos.size (Pos.of_nat (S fuel))) + N.of_nat fuel * (1 + u).
Proof.
  intros Hx Hclosed Hget Hsets.
  pose proof (UnionFindLoop.walk_cost E (UnionFind.parents uf) fuel x allowed g
    Hx Hclosed Hget) as Hwalk.
  pose proof (UnionFindLoop.walk_correct E (UnionFind.parents uf) fuel x) as Hpath.
  rewrite UnionFind.find_fuel_callee_cost.
  destruct (Cost.value (UnionFindLoop.walk_c E (UnionFind.parents uf) fuel x)) as [root path].
  pose proof (compression_cost E root path uf u Hsets) as Hcompression.
  pose proof (UnionFindLoop.path_length E _ _ _ _ _ Hpath) as Hlength.
  assert (HlengthN : N.of_nat (length path) <= N.of_nat fuel) by lia. nia.
Qed.

Local Lemma parent_known {K} (E : encoding K) uf a b :
  UnionFind.wf E uf -> Map.get E a (UnionFind.parents uf) = Some b ->
  UnionFind.support E uf b.
Proof.
  intros [_ [_ [_ Hrank]]] Hparent. specialize (Hrank a b Hparent).
  unfold UnionFind.support. rewrite !UnionFind.rank_of_equation in Hrank.
  destruct (Map.get E b (UnionFind.ranks uf)) eqn:Hget.
  - right. discriminate.
  - lia.
Qed.

Local Lemma positive_size_small p : (Pos.to_nat (Pos.size p) <= Pos.to_nat p)%nat.
Proof.
  induction p as [p IH|p IH|]; [| |reflexivity].
  - cbn [Pos.size]. rewrite Pos2Nat.inj_succ, Pos2Nat.inj_xI. lia.
  - cbn [Pos.size]. rewrite Pos2Nat.inj_succ, Pos2Nat.inj_xO.
    pose proof (Pos2Nat.is_pos p). lia.
Qed.

Local Lemma fuel_width fuel :
  N.pos (Pos.size (Pos.of_nat (S fuel))) <= N.of_nat (S fuel).
Proof.
  pose proof (positive_size_small (Pos.of_nat (S fuel))) as Hsize.
  rewrite Nat2Pos.id in Hsize by lia.
  assert (Hequal : N.pos (Pos.size (Pos.of_nat (S fuel))) =
    N.of_nat (Pos.to_nat (Pos.size (Pos.of_nat (S fuel))))).
  { symmetry. exact (N2Nat.id (N.pos (Pos.size (Pos.of_nat (S fuel))))). }
  rewrite Hequal. lia.
Qed.

(** Numeric prefix-find bounds need a finite support budget and a separate budget for the query. *)
Theorem find_fuel_cost {K} (E : encoding K) (laws : Map.cost_laws) fuel x uf w :
  UnionFind.wf E uf -> support_budget E w uf -> key_bound E w x ->
  Cost.ticks (UnionFind.find_fuel_c E fuel x uf) <=
    8 * (N.of_nat fuel + 1) * (1 + w).
Proof.
  intros Hwf Hsupport Hx.
  set (allowed := fun a => a = x \/ UnionFind.support E uf a).
  assert (Hkeys : forall a, allowed a -> key_bound E w a).
  { intros a [Hequal|Hknown]; [subst a; exact Hx|apply Hsupport; exact Hknown]. }
  assert (Hclosed : forall a b,
    allowed a -> Map.get E a (UnionFind.parents uf) = Some b -> allowed b).
  { intros a b Ha Hparent. right. eapply parent_known; eassumption. }
  pose proof (UnionFindLoop.walk_correct E (UnionFind.parents uf) fuel x) as Hpath.
  pose proof (UnionFind.find_fuel_callee_cost E fuel x uf) as Hequation.
  destruct (Cost.value (UnionFindLoop.walk_c E (UnionFind.parents uf) fuel x)) as [root path]
    eqn:Hwalk.
  assert (Hallowed : Forall allowed path).
  { exact (proj2 (UnionFindLoop.path_allowed E (UnionFind.parents uf) allowed Hclosed
      _ _ _ _ Hpath (or_introl eq_refl))). }
  assert (Hsets : forall acc, compression_budget E root path acc (1 + w)).
  { clear Hpath Hwalk Hequation.
    induction Hallowed as [|key rest Hkey Hrest IH]; intro acc.
    - exact I.
    - split.
      + rewrite Map.set_cost. specialize (Hkeys key Hkey). unfold key_bound in Hkeys. lia.
      + apply IH. }
  pose proof (UnionFindLoop.walk_cost E (UnionFind.parents uf) fuel x allowed (1 + w)
    (or_introl eq_refl) Hclosed
    ltac:(intros a Ha; rewrite Map.get_cost; specialize (Hkeys a Ha);
      unfold key_bound in Hkeys; lia)) as Hwalkcost.
  pose proof (compression_cost E root path uf (1 + w) (Hsets uf)) as Hcompression.
  pose proof (UnionFindLoop.path_length E _ _ _ _ _ Hpath) as Hlength.
  pose proof (fuel_width fuel) as Hwidth.
  assert (HlengthN : N.of_nat (length path) <= N.of_nat fuel) by lia.
  rewrite Hequation. nia.
Qed.

(** A find's rank-relative bound composes its actual binary walk and compression path. *)
Theorem find_cost_rank {K} (E : encoding K) (laws : Map.cost_laws) x uf w :
  UnionFind.wf E uf -> support_budget E w uf -> key_bound E w x ->
  Cost.ticks (UnionFind.find_c E x uf) <=
    16 * N.of_nat (S (UnionFind.max_rank uf)) * (1 + w).
Proof.
  intros Hwf Hsupport Hx.
  pose proof (find_fuel_cost E laws (S (UnionFind.max_rank uf)) x uf w
    Hwf Hsupport Hx) as Hcost.
  change (Cost.ticks (UnionFind.find_fuel_c E (S (UnionFind.max_rank uf)) x uf) <=
    16 * N.of_nat (S (UnionFind.max_rank uf)) * (1 + w)).
  rewrite Nat2N.inj_succ in *. nia.
Qed.

(** Find is logarithmic in known support under the separately maintained rank-size invariant. *)
Theorem find_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf -> key_bound E w x ->
  Cost.ticks (UnionFind.find_c E x uf) <=
    uf_k * N.of_nat (S (Nat.log2 (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hsupport Hx.
  pose proof (find_cost_rank E laws x uf w
    (UnionFindRank.forest_wf E uf Hinv) Hsupport Hx) as Hcost.
  pose proof (UnionFindRank.max_rank_le_log2_keys E HE uf Hinv) as Hrank.
  unfold uf_k. rewrite Nat2N.inj_succ in *.
  assert (HrankN : N.of_nat (UnionFind.max_rank uf) <=
    N.of_nat (Nat.log2 (length (UnionFind.keys E uf)))) by lia. nia.
Qed.

Local Lemma support_budget_find {K} (E : encoding K) (HE : encoding_laws E) uf x w :
  UnionFind.wf E uf -> support_budget E w uf ->
  support_budget E w (snd (UnionFind.find E x uf)).
Proof.
  intros Hwf Hbudget a Hknown. apply Hbudget.
  apply (proj1 (UnionFind.find_support E HE x uf a Hwf)). exact Hknown.
Qed.

Local Lemma representative_bound {K} (E : encoding K) uf x w :
  UnionFind.wf E uf -> support_budget E w uf -> key_bound E w x ->
  key_bound E w (fst (UnionFind.find E x uf)).
Proof.
  intros Hwf Hsupport Hx.
  destruct (UnionFind.find_fuel_path E (S (UnionFind.max_rank uf)) x uf)
    as [root [path [Hpath Hresult]]].
  rewrite UnionFind.find_equation, Hresult. cbn [fst].
  pose proof (UnionFindLoop.path_allowed E (UnionFind.parents uf)
    (fun a => key_bound E w a)
    ltac:(intros a b Ha Hparent; apply Hsupport; eapply parent_known; eassumption)
    _ _ _ _ Hpath Hx) as Hallowed.
  exact (proj1 Hallowed).
Qed.

Local Lemma equality_cost {K} (E : encoding K) w a b :
  key_bound E w a -> key_bound E w b -> Cost.ticks (eqb_c E a b) <= 2 + 2 * w.
Proof.
  intros Ha Hb. pose proof (eqb_cost E a b) as Hcost.
  pose proof (N.le_min_l (key_bits E a) (key_bits E b)).
  unfold key_bound in Ha, Hb. unfold key_bits in *. nia.
Qed.

Local Lemma touch_cost {K} (E : encoding K) uf x w :
  key_bound E w x -> Cost.ticks (UnionFind.touch_c E x uf) <= 2 * (1 + w).
Proof.
  intro Hx. unfold UnionFind.touch_c. rewrite Cost.ticks_bind.
  fold (Map.get E x (UnionFind.ranks uf)).
  destruct (Map.get E x (UnionFind.ranks uf)); autorewrite with galois_cost;
    rewrite ?Map.get_cost, ?Map.set_cost; unfold key_bound in Hx; nia.
Qed.

Local Lemma link_cost {K} (E : encoding K) uf child root raise w :
  key_bound E w child -> key_bound E w root ->
  Cost.ticks (UnionFind.link_c E child root raise uf) <= 3 * (1 + w).
Proof.
  intros Hchild Hroot. destruct raise.
  - unfold UnionFind.link_c. rewrite !Cost.ticks_bind, Cost.ticks_ret,
      UnionFind.rank_of_cost, Map.get_cost, !Map.set_cost.
    unfold key_bound in *. nia.
  - change (Cost.ticks (UnionFind.redirect_c E child root uf) <= 3 * (1 + w)).
    rewrite UnionFind.redirect_cost, Map.set_cost. unfold key_bound in *. nia.
Qed.

(** Union's numeric bound couples both actual find results and the selected root-link callees. *)
Theorem union_cost_sharp {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x y uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf ->
  key_bound E w x -> key_bound E w y ->
  Cost.ticks (UnionFind.union_c E x y uf) <=
    64 * N.of_nat (S (Nat.log2 (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hbudget Hx Hy.
  pose proof (UnionFindRank.forest_wf E uf Hinv) as Hwf.
  pose proof (UnionFindRank.max_rank_le_log2_keys E HE uf Hinv) as Hrank.
  pose proof (find_cost_rank E laws x uf w Hwf Hbudget Hx) as Hfirst.
  pose proof (representative_bound E uf x w Hwf Hbudget Hx) as Hrx.
  pose proof (UnionFind.wf_find E HE uf x Hwf) as Hwf1.
  pose proof (support_budget_find E HE uf x w Hwf Hbudget) as Hbudget1.
  pose proof (proj2 (UnionFind.find_ranks E uf x)) as Hmax1.
  unfold UnionFind.union_c. rewrite Cost.ticks_bind. fold (UnionFind.find E x uf).
  destruct (UnionFind.find E x uf) as [rx u1] eqn:Hxfind.
  cbn [fst snd] in Hrx, Hwf1, Hbudget1, Hmax1.
  pose proof (find_cost_rank E laws y u1 w Hwf1 Hbudget1 Hy) as Hsecond.
  pose proof (representative_bound E u1 y w Hwf1 Hbudget1 Hy) as Hry.
  rewrite Cost.ticks_bind. fold (UnionFind.find E y u1).
  destruct (UnionFind.find E y u1) as [ry u2] eqn:Hyfind. cbn [fst] in Hry.
  pose proof (equality_cost E w rx ry Hrx Hry) as Hequal.
  rewrite Cost.ticks_bind. fold (eqb E rx ry).
  assert (HrankN : N.of_nat (UnionFind.max_rank uf) <=
    N.of_nat (Nat.log2 (length (UnionFind.keys E uf)))) by lia.
  destruct (eqb E rx ry).
  - pose proof (touch_cost E u2 rx w Hrx). rewrite Hmax1 in Hsecond.
    rewrite Nat2N.inj_succ in *. nia.
  - rewrite !Cost.ticks_bind. fold (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry).
    pose proof (link_cost E u2 ry rx true w Hry Hrx) as Hlinkeq.
    pose proof (link_cost E u2 rx ry false w Hrx Hry) as Hlinklt.
    pose proof (link_cost E u2 ry rx false w Hry Hrx) as Hlinkgt.
    rewrite !UnionFind.rank_of_cost, !Map.get_cost.
    destruct (Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry));
      rewrite Hmax1 in Hsecond; unfold key_bound in Hrx, Hry;
      rewrite Nat2N.inj_succ in *; nia.
Qed.

(** Union has a logarithmic bound and explicit budgets for both possibly unknown queries. *)
Theorem union_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x y uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf ->
  key_bound E w x -> key_bound E w y ->
  Cost.ticks (UnionFind.union_c E x y uf) <=
    uf_k * N.of_nat (S (Nat.log2 (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hbudget Hx Hy.
  pose proof (union_cost_sharp E HE laws x y uf w Hinv Hbudget Hx Hy).
  unfold uf_k. nia.
Qed.

(** Union's callee-relative equation retains both actual compressed forests and selected callees. *)
Theorem union_cost_callee {K} (E : encoding K) x y uf :
  Cost.ticks (UnionFind.union_c E x y uf) =
  let '(rx, u1) := UnionFind.find E x uf in
  let '(ry, u2) := UnionFind.find E y u1 in
  (Cost.ticks (UnionFind.find_c E x uf) + Cost.ticks (UnionFind.find_c E y u1) +
    Cost.ticks (eqb_c E rx ry) +
    if eqb E rx ry then Cost.ticks (UnionFind.touch_c E rx u2)
    else
      Cost.ticks (UnionFind.rank_of_c E u2 rx) +
      Cost.ticks (UnionFind.rank_of_c E u2 ry) +
      match Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry) with
      | Eq => Cost.ticks (UnionFind.link_c E ry rx true u2)
      | Lt => Cost.ticks (UnionFind.link_c E rx ry false u2)
      | Gt => Cost.ticks (UnionFind.link_c E ry rx false u2)
      end).
Proof.
  unfold UnionFind.union_c. rewrite Cost.ticks_bind. fold (UnionFind.find E x uf).
  destruct (UnionFind.find E x uf) as [rx u1].
  rewrite Cost.ticks_bind. fold (UnionFind.find E y u1).
  destruct (UnionFind.find E y u1) as [ry u2].
  rewrite Cost.ticks_bind. fold (eqb E rx ry).
  destruct (eqb E rx ry); [lia|].
  rewrite !Cost.ticks_bind. fold (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry).
  destruct (Nat.compare (UnionFind.rank_of E u2 rx) (UnionFind.rank_of E u2 ry)); lia.
Qed.

(** Boolean equivalence testing charges its two actual finds and their representative comparison. *)
Theorem equivb_cost_callee {K} (E : encoding K) x y uf :
  Cost.ticks (UnionFind.equivb_c E x y uf) =
  let '(rx, u1) := UnionFind.find E x uf in
  let '(ry, u2) := UnionFind.find E y u1 in
  Cost.ticks (UnionFind.find_c E x uf) + Cost.ticks (UnionFind.find_c E y u1) +
    Cost.ticks (eqb_c E rx ry).
Proof.
  unfold UnionFind.equivb_c. rewrite Cost.ticks_bind. fold (UnionFind.find E x uf).
  destruct (UnionFind.find E x uf) as [rx u1].
  rewrite Cost.ticks_bind. fold (UnionFind.find E y u1).
  destruct (UnionFind.find E y u1) as [ry u2].
  rewrite Cost.ticks_bind, Cost.ticks_ret. lia.
Qed.

(** Equivalence testing has the same logarithmic finite-support domain as union. *)
Theorem equivb_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x y uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf ->
  key_bound E w x -> key_bound E w y ->
  Cost.ticks (UnionFind.equivb_c E x y uf) <=
    uf_k * N.of_nat (S (Nat.log2 (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hbudget Hx Hy.
  pose proof (UnionFindRank.forest_wf E uf Hinv) as Hwf.
  pose proof (UnionFindRank.max_rank_le_log2_keys E HE uf Hinv) as Hrank.
  pose proof (find_cost_rank E laws x uf w Hwf Hbudget Hx) as Hfirst.
  pose proof (representative_bound E uf x w Hwf Hbudget Hx) as Hrx.
  pose proof (UnionFind.wf_find E HE uf x Hwf) as Hwf1.
  pose proof (support_budget_find E HE uf x w Hwf Hbudget) as Hbudget1.
  pose proof (proj2 (UnionFind.find_ranks E uf x)) as Hmax1.
  rewrite equivb_cost_callee.
  destruct (UnionFind.find E x uf) as [rx u1] eqn:Hxfind.
  cbn [fst snd] in Hrx, Hwf1, Hbudget1, Hmax1.
  pose proof (find_cost_rank E laws y u1 w Hwf1 Hbudget1 Hy) as Hsecond.
  pose proof (representative_bound E u1 y w Hwf1 Hbudget1 Hy) as Hry.
  destruct (UnionFind.find E y u1) as [ry u2] eqn:Hyfind. cbn [fst] in Hry.
  pose proof (equality_cost E w rx ry Hrx Hry) as Hequal.
  rewrite Hmax1 in Hsecond.
  assert (HrankN : N.of_nat (UnionFind.max_rank uf) <=
    N.of_nat (Nat.log2 (length (UnionFind.keys E uf)))) by lia.
  unfold uf_k. rewrite Nat2N.inj_succ in *. nia.
Qed.

(** A finite universe covers stored support without enumerating the key carrier. *)
Definition within {K} (E : encoding K) (uf : UnionFind.t K) (U : list K) : Prop :=
  forall a, UnionFind.support E uf a -> In a U.

Local Lemma within_union {K} (E : encoding K) (HE : encoding_laws E) uf x y U :
  UnionFind.wf E uf -> within E uf U -> In x U -> In y U ->
  within E (UnionFind.union E x y uf) U.
Proof.
  intros Hwf Hwithin Hx Hy a Ha.
  apply (proj2 (UnionFind.keys_spec E HE _ a (UnionFind.wf_union E HE uf x y Hwf))) in Ha.
  apply (proj1 (UnionFind.keys_union E HE uf x y a Hwf)) in Ha.
  destruct Ha as [Heq|[Heq|Ha]]; [subst; exact Hx|subst; exact Hy|].
  apply Hwithin. apply (proj1 (UnionFind.keys_spec E HE uf a Hwf)). exact Ha.
Qed.

Local Lemma within_size {K} (E : encoding K) (HE : encoding_laws E) uf U :
  UnionFind.wf E uf -> within E uf U ->
  (length (UnionFind.keys E uf) <= length U)%nat.
Proof.
  intros Hwf Hwithin. apply NoDup_incl_length.
  - apply UnionFind.keys_nodup; assumption.
  - intros a Ha. apply Hwithin.
    apply (proj1 (UnionFind.keys_spec E HE uf a Hwf)). exact Ha.
Qed.

Local Lemma unions_from_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) pairs U w :
  (forall a, In a U -> key_bound E w a) ->
  Forall (fun xy => In (fst xy) U /\ In (snd xy) U) pairs ->
  forall uf, UnionFindRank.rank_size_inv E uf -> within E uf U ->
  Cost.ticks (UnionFind.unions_from_c E pairs uf) <=
    N.of_nat (length pairs) * uf_k * N.of_nat (S (Nat.log2 (length U))) * (1 + w).
Proof.
  intros Hkeys Hpairs.
  induction Hpairs as [|[x y] pairs [Hx Hy] Htail IH]; intros uf Hinv Hwithin.
  - reflexivity.
  - pose proof (UnionFindRank.forest_wf E uf Hinv) as Hwf.
    assert (Hbudget : support_budget E w uf) by (intros a Ha; apply Hkeys, Hwithin, Ha).
    pose proof (union_cost_sharp E HE laws x y uf w Hinv Hbudget
      (Hkeys x Hx) (Hkeys y Hy)) as Hhead.
    pose proof (within_size E HE uf U Hwf Hwithin) as Hsize.
    pose proof (Nat.log2_le_mono _ _ Hsize) as Hlog.
    pose proof (UnionFindRank.union_rank_size_inv E HE uf x y Hinv) as Hinv'.
    specialize (IH _ Hinv' (within_union E HE uf x y U Hwf Hwithin Hx Hy)).
    cbn [UnionFind.unions_from_c]. autorewrite with galois_cost.
    fold (UnionFind.union E x y uf).
    assert (HlogN : N.of_nat (Nat.log2 (length (UnionFind.keys E uf))) <=
      N.of_nat (Nat.log2 (length U))) by lia.
    unfold uf_k in *. cbn [length]. rewrite Nat2N.inj_succ in *. nia.
Qed.

(** Pair-list initialization is linear in the number of unions times the finite-universe bound. *)
Theorem of_unions_cost {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) pairs U w :
  (forall a, In a U -> key_bound E w a) ->
  Forall (fun xy => In (fst xy) U /\ In (snd xy) U) pairs ->
  Cost.ticks (UnionFind.of_unions_c E pairs) <=
    N.of_nat (length pairs) * uf_k * N.of_nat (S (Nat.log2 (length U))) * (1 + w).
Proof.
  intros Hkeys Hpairs.
  unfold UnionFind.of_unions_c. rewrite Cost.ticks_bind, UnionFind.make_cost.
  change (0 + Cost.ticks (UnionFind.unions_from_c E pairs UnionFind.make) <=
    N.of_nat (length pairs) * uf_k * N.of_nat (S (Nat.log2 (length U))) * (1 + w)).
  rewrite N.add_0_l. apply (unions_from_cost E HE laws pairs U w Hkeys Hpairs).
  - apply UnionFindRank.rank_size_inv_make.
  - intros a Ha. unfold UnionFind.support in Ha.
    rewrite UnionFind.make_equation in Ha. cbn [UnionFind.parents UnionFind.ranks] in Ha.
    rewrite !Map.get_empty in Ha. destruct Ha; contradiction.
Qed.

(** The numeric find bound also exposes the requested binary logarithm of known-key count. *)
Theorem find_cost_logN {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf -> key_bound E w x ->
  Cost.ticks (UnionFind.find_c E x uf) <=
    uf_k * (1 + N.log2 (N.of_nat (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hsupport Hx.
  pose proof (find_cost E HE laws x uf w Hinv Hsupport Hx) as Hcost.
  rewrite Nat2N.inj_succ, HeapLoop.log2_nat_N in Hcost. nia.
Qed.

(** Union uses the same binary-logarithm budget and retains both unknown-query duties. *)
Theorem union_cost_logN {K} (E : encoding K) (HE : encoding_laws E)
    (laws : Map.cost_laws) x y uf w :
  UnionFindRank.rank_size_inv E uf -> support_budget E w uf ->
  key_bound E w x -> key_bound E w y ->
  Cost.ticks (UnionFind.union_c E x y uf) <=
    uf_k * (1 + N.log2 (N.of_nat (length (UnionFind.keys E uf)))) * (1 + w).
Proof.
  intros Hinv Hsupport Hx Hy.
  pose proof (union_cost E HE laws x y uf w Hinv Hsupport Hx Hy) as Hcost.
  rewrite Nat2N.inj_succ, HeapLoop.log2_nat_N in Hcost. nia.
Qed.

End UnionFindCost.
