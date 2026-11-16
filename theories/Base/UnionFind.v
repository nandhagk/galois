(** * Union-find implementation

    Union by size maintains a forest and compresses paths during lookup.
    For example, union links the smaller class under the larger root.
    Builds on: trie code and Argent fuelled loops. *)

From Stdlib Require Import List PArith NArith Arith Lia Sorting.Permutation.
From Argent Require Import Time Loop Std BigO Tactics.
From Galois.Base Require Import Trie UnionFindSig.
Import ListNotations.

Record uf : Type := UF { parents : PTrieCode.t positive; sizes : PTrieCode.t N; count : N }.

TimeFun parents.
TimeFun sizes.
TimeFun count.

Module UnionFindCode <: UNION_FIND_OPS.
  Definition t := uf.
  Definition empty : t := UF PTrieCode.empty PTrieCode.empty 0.
  Definition parent_of (x : positive) (u : t) : positive :=
    match PTrieCode.get x (parents u) with Some p => p | None => x end.
  TimeFun parent_of.
  Definition size_at (r : positive) (u : t) : N :=
    match PTrieCode.get r (sizes u) with Some n => n | None => 1%N end.
  Definition add (x : positive) (u : t) : t :=
    match PTrieCode.get x (parents u) with
    | Some _ => u
    | None => UF (PTrieCode.set x x (parents u)) (PTrieCode.set x 1%N (sizes u)) (N.succ (count u))
    end.
  Definition walk_step (u : t) (s : positive * list positive)
      : positive * list positive + positive * list positive :=
    let p := parent_of (fst s) u in
    if Pos.eqb p (fst s) then inr s else inl (p, fst s :: snd s).
  TimeFun walk_step.
  Definition walk (x : positive) (u : t) : positive * list positive :=
    match loop_fuel (walk_step u) (S (N.size_nat (count u))) (x, []) with inl s => s | inr s => s end.
  TimeFun walk.
  (** A read-only lookup walks to the root and leaves the forest as it is. *)
  Definition root_of (x : positive) (u : t) : positive := fst (walk x u).
  TimeFun root_of.
  Definition compress (root : positive) (path : list positive) (u : t) : t :=
    UF (fold_left (fun m y => PTrieCode.set y root m) path (parents u)) (sizes u) (count u).
  TimeFun compress.
  Definition find (x : positive) (u : t) : positive * t :=
    let r := walk x u in (fst r, compress (fst r) (snd r) u).
  TimeFun find.
  Definition link (w l : positive) (u : t) : t :=
    UF (PTrieCode.set l w (parents u)) (PTrieCode.set w (size_at w u + size_at l u)%N (sizes u)) (count u).
  Definition union (x y : positive) (u : t) : option (positive * positive) * t :=
    let fx := find x (add y (add x u)) in
    let fy := find y (snd fx) in
    let rx := fst fx in
    let ry := fst fy in
    let u2 := snd fy in
    if Pos.eqb rx ry then (None, u2)
    else if N.leb (size_at ry u2) (size_at rx u2) then (Some (rx, ry), link rx ry u2)
    else (Some (ry, rx), link ry rx u2).
End UnionFindCode.
Module UnionFind <: UNION_FIND.
  Include UnionFindCode.
  Definition support (u : t) : list positive := map fst (PTrieCode.elements (parents u)).
  Definition mem (u : t) (x : positive) : Prop := PTrieCode.get x (parents u) <> None.
  Definition card (u : t) : nat := N.to_nat (count u).
  Definition repr (u : t) (x : positive) : positive := Nat.iter (card u) (fun y => parent_of y u) x.
  Definition size_of (u : t) (x : positive) : nat :=
    match PTrieCode.get x (parents u) with
    | None => 1
    | Some _ => length (filter (fun y => Pos.eqb (repr u y) (repr u x)) (support u))
    end.
  Definition width (u : t) : nat := fold_right (fun y w => Nat.max (Pos.size_nat y) w) 0 (support u).
  Definition is_root (u : t) (x : positive) : Prop := parent_of x u = x.
  Definition ranked (u : t) (rk : positive -> nat) : Prop :=
    (forall x, mem u x -> ~ is_root u x -> rk x < rk (parent_of x u)) /\
    (forall r, mem u r -> is_root u r -> 2 ^ rk r <= size_of u r).
  Definition wf (u : t) : Prop :=
    card u = length (support u) /\
    (forall x p, PTrieCode.get x (parents u) = Some p -> mem u p) /\
    (forall r, mem u r -> is_root u r -> N.to_nat (size_at r u) = size_of u r) /\
    (forall r n, PTrieCode.get r (sizes u) = Some n -> N.to_nat n <= card u) /\
    exists rk, ranked u rk.

  (** ** Forest and walk foundations *)

  (** Support enumerates exactly the stored parent keys. *)
  Lemma support_spec u x : In x (support u) <-> mem u x.
  Proof.
    unfold support, mem. rewrite in_map_iff. split.
    - intros [[y p] [Heq Hin]]. cbn [fst] in Heq. subst y.
      apply PTrie.elements_spec in Hin. rewrite Hin. discriminate.
    - intro Hmem. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget;
        [|contradiction].
      exists (x, p). split; [reflexivity|]. apply PTrie.elements_spec. exact Hget.
  Qed.

  (** Parent support contains each key once. *)
  Lemma support_nodup u : NoDup (support u).
  Proof.
    apply PTrie.elements_nodup.
  Qed.

  (** Following a stored parent remains within support. *)
  Lemma parent_mem u x : wf u -> mem u x -> mem u (parent_of x u).
  Proof.
    intros [_ [Hparent _]] Hmem. unfold parent_of.
    destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget.
    - exact (Hparent x p Hget).
    - exact Hmem.
  Qed.

  (** An absent key is its own parent. *)
  Lemma parent_fresh u x : ~ mem u x -> parent_of x u = x.
  Proof.
    unfold mem, parent_of. destruct (PTrieCode.get x (parents u));
      [intros H; exfalso; apply H; discriminate|reflexivity].
  Qed.

  (** Every nonroot key has a stored parent binding. *)
  Lemma nonroot_mem u x : ~ is_root u x -> mem u x.
  Proof.
    unfold is_root, parent_of, mem.
    destruct (PTrieCode.get x (parents u)); congruence.
  Qed.

  (** Iterating the parent of a root keeps that root. *)
  Lemma iter_root u r n : is_root u r -> Nat.iter n (fun y => parent_of y u) r = r.
  Proof.
    intro Hroot. induction n as [|n IH]; [reflexivity|].
    rewrite Nat.iter_succ, IH. exact Hroot.
  Qed.

  (** Every parent iterate of a member remains a member. *)
  Lemma iter_mem u x n : wf u -> mem u x ->
    mem u (Nat.iter n (fun y => parent_of y u) x).
  Proof.
    intros Hwf Hmem. induction n as [|n IH]; [exact Hmem|].
    rewrite Nat.iter_succ. apply parent_mem; assumption.
  Qed.

  (** Representatives of members remain in support. *)
  Lemma repr_mem u x : wf u -> mem u x -> mem u (repr u x).
  Proof.
    apply iter_mem.
  Qed.

  (** A root represents itself for every stored cardinality. *)
  Lemma repr_of_root u x : is_root u x -> repr u x = x.
  Proof.
    apply iter_root.
  Qed.

  (** An absent key represents its own singleton. *)
  Lemma repr_fresh u x : wf u -> ~ mem u x -> repr u x = x.
  Proof.
    intros _ Hfresh. apply repr_of_root. apply parent_fresh. exact Hfresh.
  Qed.

  (** Filtering support cannot enlarge a member's class beyond the cardinality. *)
  Lemma size_member_bound u x : wf u -> mem u x -> size_of u x <= card u.
  Proof.
    intros [Hcard _] Hmem. unfold size_of.
    destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget.
    - rewrite Hcard. generalize (support u) as xs.
      intro xs. induction xs as [|y ys IH]; cbn [filter length]; [lia|].
      destruct (Pos.eqb (repr u y) (repr u x)); cbn [length]; lia.
    - unfold mem in Hmem. contradiction.
  Qed.

  (** The maximum of member widths covers every support entry. *)
  Lemma support_width u x : mem u x -> Pos.size_nat x <= width u.
  Proof.
    intro Hmem. apply support_spec in Hmem. unfold width.
    induction (support u) as [|y ys IH]; [contradiction|].
    cbn [In] in Hmem. cbn [fold_right]. destruct Hmem as [Heq|Hin].
    - subst y. apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.

  (** The maximum rank over support bounds every member's rank. *)
  Lemma support_rank_bound u rk x : mem u x ->
    rk x <= fold_right (fun y n => Nat.max (rk y) n) 0 (support u).
  Proof.
    intro Hmem. apply support_spec in Hmem.
    induction (support u) as [|y ys IH]; [contradiction|].
    cbn [In] in Hmem. cbn [fold_right]. destruct Hmem as [Heq|Hin].
    - subst y. apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.

  (** A rank bounded above must stop increasing once the available rank gap is spent. *)
  Lemma iter_root_rank u rk bound :
    (forall y, mem u y -> rk y <= bound) ->
    (forall y, mem u y -> mem u (parent_of y u)) ->
    (forall y, mem u y -> ~ is_root u y -> rk y < rk (parent_of y u)) ->
    forall n x, bound <= n + rk x -> mem u x ->
      is_root u (Nat.iter n (fun y => parent_of y u) x).
  Proof.
    intros Hbound Hclosed Hstep. induction n as [|n IH]; intros x Hfuel Hmem.
    - change (is_root u x). destruct (Pos.eq_dec (parent_of x u) x) as [Hroot|Hnon].
      + exact Hroot.
      + exfalso. pose proof (Hstep x Hmem Hnon) as Hrise.
        pose proof (Hbound _ (Hclosed x Hmem)) as Hcap. lia.
    - rewrite Nat.iter_succ_r.
      destruct (Pos.eq_dec (parent_of x u) x) as [Hroot|Hnon].
      + rewrite Hroot, (iter_root u x n Hroot). exact Hroot.
      + apply IH; [|apply Hclosed; exact Hmem].
        pose proof (Hstep x Hmem Hnon). lia.
  Qed.

  (** A parent step never lowers a member's ghost rank. *)
  Lemma rank_parent_le u rk x : ranked u rk -> mem u x -> rk x <= rk (parent_of x u).
  Proof.
    intros [Hstep _] Hmem. destruct (Pos.eq_dec (parent_of x u) x) as [Heq|Hne].
    - rewrite Heq. lia.
    - pose proof (Hstep x Hmem Hne). lia.
  Qed.

  (** Parent iteration never lowers a member's ghost rank. *)
  Lemma rank_iter_le u rk x n : wf u -> ranked u rk -> mem u x ->
    rk x <= rk (Nat.iter n (fun y => parent_of y u) x).
  Proof.
    intros Hwf Hrank Hmem. induction n as [|n IH]; [reflexivity|].
    rewrite Nat.iter_succ.
    pose proof (rank_parent_le u rk _ Hrank (iter_mem u x n Hwf Hmem)). lia.
  Qed.

  (** Finite support and the root size condition bound every member rank logarithmically. *)
  Lemma rank_log u rk x : wf u -> ranked u rk -> mem u x ->
    rk x <= Nat.log2 (card u).
  Proof.
    intros Hwf Hrank Hmem.
    set (bound := fold_right (fun y n => Nat.max (rk y) n) 0 (support u)).
    assert (Hroot : is_root u (Nat.iter bound (fun y => parent_of y u) x)).
    { eapply iter_root_rank with (rk := rk) (bound := bound).
      - intros y Hy. apply support_rank_bound. exact Hy.
      - intros y Hy. apply parent_mem; assumption.
      - exact (proj1 Hrank).
      - lia.
      - exact Hmem. }
    pose proof (iter_mem u x bound Hwf Hmem) as Hrmem.
    pose proof (proj2 Hrank _ Hrmem Hroot) as Hpow.
    pose proof (size_member_bound u _ Hwf Hrmem) as Hsize.
    pose proof (rank_iter_le u rk x bound Hwf Hrank Hmem) as Hrankle.
    assert (Hcard : 0 < card u).
    { pose proof (Nat.pow_nonzero 2 (rk (Nat.iter bound (fun y => parent_of y u) x))
        ltac:(lia)). lia. }
    pose proof (proj1 (Nat.log2_le_pow2 (card u)
      (rk (Nat.iter bound (fun y => parent_of y u) x)) Hcard) ltac:(lia)) as Hlog.
    lia.
  Qed.

  (** Once an iteration reaches a root, every later iteration has the same value. *)
  Lemma iter_stable u x n m :
    is_root u (Nat.iter n (fun y => parent_of y u) x) -> n <= m ->
    Nat.iter m (fun y => parent_of y u) x = Nat.iter n (fun y => parent_of y u) x.
  Proof.
    intros Hroot Hle. replace m with ((m - n) + n) by lia.
    rewrite Nat.iter_add. apply iter_root. exact Hroot.
  Qed.

  (** The logarithmic rank budget suffices for every query, including absent keys. *)
  Lemma iter_root_log u x n : wf u -> Nat.log2 (card u) <= n ->
    is_root u (Nat.iter n (fun y => parent_of y u) x).
  Proof.
    intros Hwf Hfuel. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget.
    - destruct (proj2 (proj2 (proj2 (proj2 Hwf)))) as [rk Hrank].
      eapply iter_root_rank with (rk := rk) (bound := Nat.log2 (card u)).
      + intros y Hy. exact (rank_log u rk y Hwf Hrank Hy).
      + intros y Hy. apply parent_mem; assumption.
      + exact (proj1 Hrank).
      + lia.
      + unfold mem. rewrite Hget. discriminate.
    - assert (Hroot : is_root u x).
      { apply parent_fresh. unfold mem. rewrite Hget. tauto. }
      rewrite (iter_root u x n Hroot). exact Hroot.
  Qed.

  (** The specified representative is a root. *)
  Lemma repr_root u x : wf u -> is_root u (repr u x).
  Proof.
    intro Hwf. apply iter_root_log; [exact Hwf|]. apply Nat.log2_le_lin. lia.
  Qed.

  (** Every sufficiently long parent iteration returns the specified representative. *)
  Lemma iter_repr_ge u x n : wf u -> Nat.log2 (card u) <= n ->
    Nat.iter n (fun y => parent_of y u) x = repr u x.
  Proof.
    intros Hwf Hn.
    pose proof (iter_root_log u x (Nat.log2 (card u)) Hwf (Nat.le_refl _)) as Hroot.
    rewrite (iter_stable u x (Nat.log2 (card u)) n Hroot Hn).
    unfold repr. symmetry. apply iter_stable; [exact Hroot|].
    apply Nat.log2_le_lin. lia.
  Qed.

  (** A parent step leaves the representative unchanged. *)
  Lemma repr_parent u x : wf u -> repr u (parent_of x u) = repr u x.
  Proof.
    intro Hwf. unfold repr.
    rewrite (@Nat.iter_swap (card u) positive (fun y => parent_of y u) x).
    exact (repr_root u x Hwf).
  Qed.

  (** Iterating parents leaves the representative unchanged. *)
  Lemma repr_iter u x n : wf u ->
    repr u (Nat.iter n (fun y => parent_of y u) x) = repr u x.
  Proof.
    intro Hwf. induction n as [|n IH]; [reflexivity|].
    rewrite Nat.iter_succ, repr_parent by exact Hwf. exact IH.
  Qed.

  (** A member's representative has at least its original ghost rank. *)
  Lemma rank_le_repr u rk x : wf u -> ranked u rk -> mem u x ->
    rk x <= rk (repr u x).
  Proof.
    apply rank_iter_le.
  Qed.

  (** The binary count width covers the logarithmic parent-depth budget. *)
  Lemma card_log_size u : Nat.log2 (card u) <= N.size_nat (count u).
  Proof.
    unfold card. destruct (count u) as [|p]; [reflexivity|].
    change (Nat.log2 (Pos.to_nat p) <= Pos.size_nat p).
    pose proof (proj1 (Nat.log2_lt_pow2 (Pos.to_nat p) (Pos.size_nat p)
      (Pos2Nat.is_pos p)) (Pos.size_nat_upper p)). lia.
  Qed.

  (** A member walk spends one increasing rank per recorded nonroot key. *)
  Lemma walk_fuel_correct u rk : wf u -> ranked u rk ->
    forall fuel x path, mem u x -> Nat.log2 (card u) < fuel + rk x ->
    let result :=
      match loop_fuel (walk_step u) fuel (x, path) with inl s => s | inr s => s end in
    fst result = repr u x /\
    length (snd result) <= length path + (Nat.log2 (card u) - rk x) /\
    forall y, In y (snd result) -> In y path \/
      (mem u y /\ repr u y = repr u x /\ y <> repr u x).
  Proof.
    intros Hwf Hrank. induction fuel as [|fuel IH]; intros x path Hmem Hfuel.
    - pose proof (rank_log u rk x Hwf Hrank Hmem). lia.
    - cbn [loop_fuel]. unfold walk_step. cbn [fst snd].
      destruct (Pos.eqb (parent_of x u) x) eqn:Hstop.
      + apply Pos.eqb_eq in Hstop. cbn [fst snd]. split.
        * symmetry. apply repr_of_root. exact Hstop.
        * split; [lia|]. intros y Hy. left. exact Hy.
      + apply Pos.eqb_neq in Hstop.
        pose proof (parent_mem u x Hwf Hmem) as Hp.
        pose proof (proj1 Hrank x Hmem Hstop) as Hrise.
        destruct (IH (parent_of x u) (x :: path) Hp ltac:(lia))
          as [Hresult [Hlength Hpath]].
        rewrite repr_parent in Hresult, Hpath by exact Hwf.
        split; [exact Hresult|]. split.
        * unfold walk_step in Hlength. cbn [length fst snd] in Hlength.
          pose proof (rank_log u rk (parent_of x u) Hwf Hrank Hp). lia.
        * intros y Hy. destruct (Hpath y Hy) as [[Heq|Hin]|Hnew].
          -- subst y. right. split; [exact Hmem|]. split; [reflexivity|].
             intro Heq. pose proof (repr_root u x Hwf) as Hroot.
             unfold is_root in Hroot. congruence.
          -- left. exact Hin.
          -- right. exact Hnew.
  Qed.

  (** Walking returns the representative and records a logarithmic path within its class. *)
  Lemma walk_correct x u : wf u ->
    fst (walk x u) = repr u x /\
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) ->
      mem u y /\ repr u y = repr u x /\ y <> repr u x.
  Proof.
    intro Hwf. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget.
    - assert (Hmem : mem u x) by (unfold mem; rewrite Hget; discriminate).
      destruct (proj2 (proj2 (proj2 (proj2 Hwf)))) as [rk Hrank].
      pose proof (card_log_size u) as Hfuel.
      destruct (walk_fuel_correct u rk Hwf Hrank (S (N.size_nat (count u)))
        x nil Hmem ltac:(lia)) as [Hroot [Hlength Hpath]].
      change (fst (walk x u) = repr u x) in Hroot.
      change (length (snd (walk x u)) <= 0 + (Nat.log2 (card u) - rk x)) in Hlength.
      split; [exact Hroot|]. split; [lia|].
      intros y Hy. destruct (Hpath y Hy) as [Hnil|Hnew]; [contradiction|exact Hnew].
    - assert (Hfresh : ~ mem u x) by (unfold mem; rewrite Hget; tauto).
      pose proof (parent_fresh u x Hfresh) as Hparent.
      pose proof (repr_fresh u x Hwf Hfresh) as Hrepr.
      unfold walk. cbn [loop_fuel]. unfold walk_step. cbn [fst snd].
      rewrite Hparent, Pos.eqb_refl. cbn [fst snd length].
      split; [symmetry; exact Hrepr|]. split; [lia|]. intros y Hy. contradiction.
  Qed.

  (** The executable walk returns the specified representative. *)
  Lemma walk_root x u : wf u -> fst (walk x u) = repr u x.
  Proof.
    intro Hwf. exact (proj1 (walk_correct x u Hwf)).
  Qed.

  (** Every recorded path key is a member of the queried class. *)
  Lemma walk_path x u : wf u ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  Proof.
    intro Hwf. destruct (walk_correct x u Hwf) as [_ [Hlength Hpath]].
    split; [exact Hlength|]. intros y Hy.
    destruct (Hpath y Hy) as [Hmem [Hrepr _]]. split; assumption.
  Qed.

  (** The recorded path excludes the returned root. *)
  Lemma walk_path_nonroot x u : wf u ->
    forall y, In y (snd (walk x u)) -> y <> fst (walk x u).
  Proof.
    intro Hwf. destruct (walk_correct x u Hwf) as [Hroot [_ Hpath]].
    intros y Hy. rewrite Hroot. exact (proj2 (proj2 (Hpath y Hy))).
  Qed.

  (** ** End forest and walk foundations *)

  (** Adding a singleton extends the lookup domain on every raw forest. *)
  Lemma mem_add_raw x u y : mem (add x u) y <-> mem u y \/ y = x.
  Proof.
    unfold add. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hx.
    - split; [auto|]. intros [Hy|Hy]; [exact Hy|].
      subst y. unfold mem. rewrite Hx. discriminate.
    - unfold mem. cbn [parents]. destruct (Pos.eq_dec y x) as [Heq|Hne].
      + subst y. rewrite PTrie.get_set_same. intuition discriminate.
      + rewrite PTrie.get_set_other by exact Hne. tauto.
  Qed.

  (** Registering an absent self-parent leaves the total parent function unchanged. *)
  Lemma parent_of_add x u y : parent_of y (add x u) = parent_of y u.
  Proof.
    unfold add. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hx;
      [reflexivity|].
    unfold parent_of. cbn [parents]. destruct (Pos.eq_dec y x) as [Heq|Hne].
    - subst y. rewrite PTrie.get_set_same, Hx. reflexivity.
    - rewrite PTrie.get_set_other by exact Hne. reflexivity.
  Qed.

  (** Equal membership predicates give permutations of the finite support lists. *)
  Lemma support_perm u v : (forall x, mem u x <-> mem v x) ->
    Permutation (support u) (support v).
  Proof.
    intro Hmem. apply NoDup_Permutation; try apply support_nodup.
    intro x. rewrite !support_spec. apply Hmem.
  Qed.

  (** Filtering a permutation preserves its selected cardinality. *)
  Lemma filter_length_perm {A} (f : A -> bool) xs ys :
    Permutation xs ys -> length (filter f xs) = length (filter f ys).
  Proof.
    intro Hperm. induction Hperm as [|a xs ys Hperm IH|a b xs|xs ys zs Hxy IHxy Hyz IHyz].
    - reflexivity.
    - cbn [filter]. destruct (f a); cbn [length]; lia.
    - cbn [filter]. destruct (f a), (f b); reflexivity.
    - congruence.
  Qed.

  (** Membership and representatives determine every class size. *)
  Lemma size_of_transport u v x :
    (forall y, mem u y <-> mem v y) ->
    (forall y, repr u y = repr v y) -> size_of u x = size_of v x.
  Proof.
    intros Hmem Hrepr. unfold size_of.
    destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hu;
      destruct (PTrieCode.get x (parents v)) as [q|] eqn:Hv.
    - assert (Hfilter :
        filter (fun y => Pos.eqb (repr u y) (repr u x)) (support u) =
        filter (fun y => Pos.eqb (repr v y) (repr v x)) (support u)).
      { apply filter_ext. intro y. now rewrite (Hrepr y), (Hrepr x). }
      rewrite Hfilter. apply filter_length_perm. apply support_perm. exact Hmem.
    - exfalso. assert (Hknown : mem v x).
      { apply Hmem. unfold mem. rewrite Hu. discriminate. }
      apply Hknown. exact Hv.
    - exfalso. assert (Hknown : mem u x).
      { apply Hmem. unfold mem. rewrite Hv. discriminate. }
      apply Hknown. exact Hu.
    - reflexivity.
  Qed.

  (** A uniform bound on all members bounds the stored width. *)
  Lemma width_le_members u bound :
    (forall x, mem u x -> Pos.size_nat x <= bound) -> width u <= bound.
  Proof.
    intro Hbound. unfold width.
    assert (Hall : Forall (fun x => Pos.size_nat x <= bound) (support u)).
    { apply Forall_forall. intros x Hin. apply Hbound, support_spec. exact Hin. }
    induction Hall as [|x xs Hx Hxs IH]; cbn [fold_right]; lia.
  Qed.

  (** Adding an absent key adds exactly one support entry. *)
  Lemma support_add_fresh x u : ~ mem u x ->
    Permutation (support (add x u)) (x :: support u).
  Proof.
    intro Hfresh. apply NoDup_Permutation.
    - apply support_nodup.
    - constructor; [intro Hin; apply Hfresh, support_spec; exact Hin|apply support_nodup].
    - intro y. rewrite support_spec, mem_add_raw. cbn [In].
      rewrite support_spec. intuition congruence.
  Qed.

  (** Singleton registration preserves every fixed number of parent iterations. *)
  Lemma iter_add_same x u y n :
    Nat.iter n (fun z => parent_of z (add x u)) y =
    Nat.iter n (fun z => parent_of z u) y.
  Proof.
    induction n as [|n IH]; [reflexivity|].
    rewrite !Nat.iter_succ, parent_of_add, IH. reflexivity.
  Qed.

  (** The extra cardinality step after registration repeats an existing root. *)
  Lemma repr_add_same x u y : wf u -> repr (add x u) y = repr u y.
  Proof.
    intro Hwf. unfold repr at 1. rewrite iter_add_same.
    unfold add. destruct (PTrieCode.get x (parents u)); [reflexivity|].
    unfold card at 1. cbn [count]. rewrite N2Nat.inj_succ, Nat.iter_succ.
    exact (repr_root u y Hwf).
  Qed.

  (** A stored member's class size is its filtered support count. *)
  Lemma size_of_member u y : mem u y -> size_of u y =
    length (filter (fun z => Pos.eqb (repr u z) (repr u y)) (support u)).
  Proof.
    intro Hmem. unfold size_of.
    destruct (PTrieCode.get y (parents u)) eqn:Hy; [reflexivity|].
    exfalso. apply Hmem. exact Hy.
  Qed.

  (** No stored member is represented by an absent key. *)
  Lemma class_filter_fresh u x : wf u -> ~ mem u x ->
    filter (fun z => Pos.eqb (repr u z) x) (support u) = [].
  Proof.
    intros Hwf Hfresh. transitivity (filter (fun _ => false) (support u)).
    - apply filter_ext_in. intros y Hy. apply Pos.eqb_neq. intro Heq.
      apply Hfresh. rewrite <- Heq. apply repr_mem; [exact Hwf|].
      apply support_spec. exact Hy.
    - apply filter_false.
  Qed.

  (** A fresh registration adds only its singleton to the selected class count. *)
  Lemma class_filter_add x u y : wf u -> ~ mem u x ->
    length (filter (fun z => Pos.eqb (repr (add x u) z) (repr (add x u) y))
      (support (add x u))) =
    (if Pos.eqb x (repr u y) then 1 else 0) +
      length (filter (fun z => Pos.eqb (repr u z) (repr u y)) (support u)).
  Proof.
    intros Hwf Hfresh.
    assert (Hfilter :
      filter (fun z => Pos.eqb (repr (add x u) z) (repr (add x u) y))
        (support (add x u)) =
      filter (fun z => Pos.eqb (repr u z) (repr u y)) (support (add x u))).
    { apply filter_ext. intro z. now rewrite !repr_add_same by exact Hwf. }
    rewrite Hfilter.
    rewrite (filter_length_perm _ _ _ (support_add_fresh x u Hfresh)).
    cbn [filter]. rewrite (repr_fresh u x Hwf Hfresh).
    destruct (Pos.eqb x (repr u y)); reflexivity.
  Qed.

  (** Registration preserves singleton and stored class sizes uniformly. *)
  Lemma size_add_same x u y : wf u -> size_of (add x u) y = size_of u y.
  Proof.
    intro Hwf. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hx.
    - unfold add. rewrite Hx. reflexivity.
    - assert (Hfresh : ~ mem u x) by (unfold mem; rewrite Hx; tauto).
      destruct (Pos.eq_dec y x) as [Heq|Hne].
      + subst y. rewrite size_of_member by (apply mem_add_raw; auto).
        rewrite class_filter_add by assumption.
        rewrite (repr_fresh u x Hwf Hfresh), Pos.eqb_refl.
        rewrite class_filter_fresh by assumption.
        unfold size_of. rewrite Hx. reflexivity.
      + destruct (PTrieCode.get y (parents u)) as [q|] eqn:Hy.
        * assert (Hmem : mem u y) by (unfold mem; rewrite Hy; discriminate).
          rewrite (size_of_member (add x u) y) by (apply mem_add_raw; auto).
          rewrite (size_of_member u y Hmem), class_filter_add by assumption.
          assert (Hother : Pos.eqb x (repr u y) = false).
          { apply Pos.eqb_neq. intro Heq. apply Hfresh.
            rewrite Heq. apply repr_mem; assumption. }
          rewrite Hother. reflexivity.
        * unfold size_of, add. rewrite Hx. cbn [parents].
          rewrite PTrie.get_set_other by exact Hne. rewrite Hy. reflexivity.
  Qed.

  (** Collapsing one distinct root selects exactly the two old root classes. *)
  Lemma filter_collapse_count {A} (f : A -> positive) w l xs : w <> l ->
    length (filter (fun z => Pos.eqb (if Pos.eqb (f z) l then w else f z) w) xs) =
    length (filter (fun z => Pos.eqb (f z) w) xs) +
    length (filter (fun z => Pos.eqb (f z) l) xs).
  Proof.
    intro Hne. induction xs as [|a xs IH]; [reflexivity|].
    cbn [filter]. destruct (Pos.eqb (f a) w) eqn:Haw;
      destruct (Pos.eqb (f a) l) eqn:Hal.
    - apply Pos.eqb_eq in Haw, Hal. congruence.
    - rewrite Haw. cbn [length]. lia.
    - rewrite Pos.eqb_refl. cbn [length]. lia.
    - rewrite Haw. cbn [length]. lia.
  Qed.

  (** A collapse leaves equality with every other representative unchanged. *)
  Lemma collapse_eqb_other w l r z : r <> w -> r <> l ->
    Pos.eqb (if Pos.eqb z l then w else z) r = Pos.eqb z r.
  Proof.
    intros Hrw Hrl. destruct (Pos.eqb z l) eqn:Hz; [|reflexivity].
    apply Pos.eqb_eq in Hz. subst z.
    rewrite (proj2 (Pos.eqb_neq w r) ltac:(congruence)),
      (proj2 (Pos.eqb_neq l r) ltac:(congruence)). reflexivity.
  Qed.

  (** Equal support and a representative collapse add the two root class sizes. *)
  Lemma size_of_collapse u v w l :
    mem u w -> mem u l -> repr u w = w -> repr u l = l -> w <> l ->
    (forall z, mem v z <-> mem u z) ->
    (forall z, repr v z = if Pos.eqb (repr u z) l then w else repr u z) ->
    size_of v w = size_of u w + size_of u l.
  Proof.
    intros Hmw Hml Hrw Hrl Hne Hmem Hrepr.
    rewrite (size_of_member v w) by (apply Hmem; exact Hmw).
    rewrite (size_of_member u w Hmw), (size_of_member u l Hml), Hrw, Hrl.
    assert (Hvw : repr v w = w).
    { rewrite Hrepr, Hrw, (proj2 (Pos.eqb_neq w l) Hne). reflexivity. }
    rewrite Hvw.
    assert (Hfilter : filter (fun z => Pos.eqb (repr v z) w) (support v) =
      filter (fun z => Pos.eqb (if Pos.eqb (repr u z) l then w else repr u z) w)
        (support v)).
    { apply filter_ext. intro z. now rewrite Hrepr. }
    rewrite Hfilter.
    rewrite (filter_length_perm _ _ _ (support_perm v u Hmem)).
    apply filter_collapse_count. exact Hne.
  Qed.

  (** Every class outside the two collapsed representatives keeps its size. *)
  Lemma size_of_collapse_other u v w l x :
    (forall z, mem v z <-> mem u z) ->
    (forall z, repr v z = if Pos.eqb (repr u z) l then w else repr u z) ->
    repr u x <> w -> repr u x <> l -> size_of v x = size_of u x.
  Proof.
    intros Hmem Hrepr Hxw Hxl. unfold size_of.
    destruct (PTrieCode.get x (parents v)) as [p|] eqn:Hv;
      destruct (PTrieCode.get x (parents u)) as [q|] eqn:Hu.
    - assert (Hvx : repr v x = repr u x).
      { rewrite Hrepr, (proj2 (Pos.eqb_neq (repr u x) l) Hxl). reflexivity. }
      rewrite Hvx.
      assert (Hfilter :
        filter (fun z => Pos.eqb (repr v z) (repr u x)) (support v) =
        filter (fun z => Pos.eqb (repr u z) (repr u x)) (support v)).
      { apply filter_ext. intro z. rewrite Hrepr. apply collapse_eqb_other; assumption. }
      rewrite Hfilter. apply filter_length_perm, support_perm. exact Hmem.
    - exfalso. assert (Hknown : mem u x).
      { apply Hmem. unfold mem. rewrite Hv. discriminate. }
      apply Hknown. exact Hu.
    - exfalso. assert (Hknown : mem v x).
      { apply Hmem. unfold mem. rewrite Hu. discriminate. }
      apply Hknown. exact Hv.
    - reflexivity.
  Qed.

  (** ** Root-link structure *)

  (** Linking changes only the losing root's parent. *)
  Lemma parent_link w l u z : parent_of z (link w l u) =
    if Pos.eqb z l then w else parent_of z u.
  Proof.
    unfold parent_of, link. cbn [parents].
    destruct (Pos.eqb z l) eqn:Heq.
    - apply Pos.eqb_eq in Heq. subst z. rewrite PTrie.get_set_same. reflexivity.
    - apply Pos.eqb_neq in Heq. rewrite PTrie.get_set_other by exact Heq. reflexivity.
  Qed.

  (** The stored cardinality is unchanged by a link. *)
  Lemma card_link w l u : card (link w l u) = card u.
  Proof.
    reflexivity.
  Qed.

  (** Overwriting an existing root preserves the parent support. *)
  Lemma mem_link w l u z : mem u l -> (mem (link w l u) z <-> mem u z).
  Proof.
    intro Hmem. unfold mem, link. cbn [parents].
    destruct (Pos.eq_dec z l) as [Heq|Hne].
    - subst z. rewrite PTrie.get_set_same. split; [intros _; exact Hmem|discriminate].
    - rewrite PTrie.get_set_other by exact Hne. reflexivity.
  Qed.

  (** Distinct-root linking removes exactly the losing root from the roots. *)
  Lemma is_root_link w l u z : w <> l ->
    (is_root (link w l u) z <-> is_root u z /\ z <> l).
  Proof.
    intro Hwl. unfold is_root. rewrite parent_link.
    destruct (Pos.eqb z l) eqn:Heq.
    - apply Pos.eqb_eq in Heq. subst z. split; [contradiction|tauto].
    - apply Pos.eqb_neq in Heq. tauto.
  Qed.

  (** Raising the winning root's rank preserves strict increases on parent edges. *)
  Lemma link_rank_step w l u rk : ranked u rk -> mem u l ->
    is_root u w -> w <> l ->
    forall z, mem (link w l u) z -> ~ is_root (link w l u) z ->
      (if Pos.eqb z w then Nat.max (rk w) (S (rk l)) else rk z) <
      (if Pos.eqb (parent_of z (link w l u)) w
       then Nat.max (rk w) (S (rk l)) else rk (parent_of z (link w l u))).
  Proof.
    intros Hrank Hml Hrw Hwl z Hmz Hnz.
    assert (Hzw : z <> w).
    { intro Heq. subst z. apply Hnz. apply is_root_link; [exact Hwl|]. split; assumption. }
    assert (Hzwe : Pos.eqb z w = false) by (apply Pos.eqb_neq; exact Hzw).
    rewrite Hzwe, parent_link.
    destruct (Pos.eqb z l) eqn:Hzl.
    - apply Pos.eqb_eq in Hzl. subst z. rewrite Pos.eqb_refl.
      pose proof (Nat.le_max_r (rk w) (S (rk l))). lia.
    - apply Pos.eqb_neq in Hzl.
      assert (Hmzold : mem u z) by (apply (mem_link w l u z Hml); exact Hmz).
      assert (Hnzold : ~ is_root u z).
      { intro Hroot. apply Hnz. apply is_root_link; [exact Hwl|]. split; assumption. }
      pose proof (proj1 Hrank z Hmzold Hnzold) as Hrise.
      destruct (Pos.eqb (parent_of z u) w) eqn:Hpw.
      + apply Pos.eqb_eq in Hpw. rewrite Hpw in Hrise.
        pose proof (Nat.le_max_l (rk w) (S (rk l))). lia.
      + exact Hrise.
  Qed.

  (** Linking two stored keys preserves closure under parents. *)
  Lemma link_parent_closed w l u : wf u -> mem u w -> mem u l ->
    forall z, mem (link w l u) z -> mem (link w l u) (parent_of z (link w l u)).
  Proof.
    intros Hwf Hmw Hml z Hmz. apply (mem_link w l u _ Hml).
    rewrite parent_link. destruct (Pos.eqb z l); [exact Hmw|].
    apply parent_mem; [exact Hwf|]. apply (mem_link w l u z Hml). exact Hmz.
  Qed.

  (** The raised rank remains at most one above the old logarithmic bound. *)
  Lemma link_rank_bound w l u rk z : wf u -> ranked u rk ->
    mem u w -> mem u l -> mem (link w l u) z ->
    (if Pos.eqb z w then Nat.max (rk w) (S (rk l)) else rk z) <=
      S (Nat.log2 (card u)).
  Proof.
    intros Hwf Hrank Hmw Hml Hmz. destruct (Pos.eqb z w).
    - apply Nat.max_lub.
      + pose proof (rank_log u rk w Hwf Hrank Hmw). lia.
      + pose proof (rank_log u rk l Hwf Hrank Hml). lia.
    - pose proof (rank_log u rk z Hwf Hrank
        (proj1 (mem_link w l u z Hml) Hmz)). lia.
  Qed.

  (** The stored cardinality still provides enough parent iterations after linking. *)
  Lemma link_repr_root w l u z : wf u -> mem u w -> mem u l ->
    is_root u w -> w <> l -> is_root (link w l u) (repr (link w l u) z).
  Proof.
    intros Hwf Hmw Hml Hrw Hwl.
    destruct (Pos.eq_dec (parent_of z (link w l u)) z) as [Hroot|Hnon].
    - rewrite (repr_of_root (link w l u) z Hroot). exact Hroot.
    - pose proof (nonroot_mem (link w l u) z Hnon) as Hmz.
      pose proof Hwf as [_ [_ [_ [_ [rk Hrank]]]]].
      assert (Hpositive : 0 < card u).
      { pose proof (proj1 Hwf) as Hcard.
        pose proof (proj2 (support_spec u w) Hmw) as Hin.
        destruct (support u); cbn [length In] in *; [contradiction|lia]. }
      pose proof (Nat.log2_lt_lin (card u) Hpositive) as Hlog.
      unfold repr. rewrite card_link.
      eapply iter_root_rank with
        (rk := fun y => if Pos.eqb y w then Nat.max (rk w) (S (rk l)) else rk y)
        (bound := S (Nat.log2 (card u))).
      + intros y Hy. apply link_rank_bound; assumption.
      + apply link_parent_closed; assumption.
      + apply link_rank_step; assumption.
      + lia.
      + exact Hmz.
  Qed.

  (** Collapsing the losing representative is invariant under one new parent step. *)
  Lemma link_collapse_parent w l u z : wf u -> is_root u w -> is_root u l -> w <> l ->
    (if Pos.eqb (repr u (parent_of z (link w l u))) l
     then w else repr u (parent_of z (link w l u))) =
    (if Pos.eqb (repr u z) l then w else repr u z).
  Proof.
    intros Hwf Hrw Hrl Hwl. rewrite parent_link.
    destruct (Pos.eqb z l) eqn:Hzl.
    - apply Pos.eqb_eq in Hzl. subst z.
      rewrite (repr_of_root u w Hrw), (repr_of_root u l Hrl), Pos.eqb_refl.
      assert (Hwe : Pos.eqb w l = false) by (apply Pos.eqb_neq; exact Hwl).
      rewrite Hwe. reflexivity.
    - rewrite (repr_parent u z Hwf). reflexivity.
  Qed.

  (** The collapsed old representative is constant throughout the new parent walk. *)
  Lemma link_collapse_iter w l u n z : wf u -> is_root u w -> is_root u l -> w <> l ->
    (if Pos.eqb (repr u (Nat.iter n (fun y => parent_of y (link w l u)) z)) l
     then w else repr u (Nat.iter n (fun y => parent_of y (link w l u)) z)) =
    (if Pos.eqb (repr u z) l then w else repr u z).
  Proof.
    intros Hwf Hrw Hrl Hwl. induction n as [|n IH]; [reflexivity|].
    rewrite Nat.iter_succ, link_collapse_parent by assumption. exact IH.
  Qed.

  (** Linking two roots replaces exactly the losing representative by the winner. *)
  Lemma repr_link w l u z : wf u -> mem u w -> mem u l ->
    is_root u w -> is_root u l -> w <> l ->
    repr (link w l u) z = if Pos.eqb (repr u z) l then w else repr u z.
  Proof.
    intros Hwf Hmw Hml Hrw Hrl Hwl.
    pose proof (link_repr_root w l u z Hwf Hmw Hml Hrw Hwl) as Hroot.
    apply (is_root_link w l u _ Hwl) in Hroot. destruct Hroot as [Hold Hneq].
    pose proof (link_collapse_iter w l u (card (link w l u)) z Hwf Hrw Hrl Hwl) as Hcollapse.
    change ((if Pos.eqb (repr u (repr (link w l u) z)) l
      then w else repr u (repr (link w l u) z)) =
      (if Pos.eqb (repr u z) l then w else repr u z)) in Hcollapse.
    rewrite (repr_of_root u _ Hold) in Hcollapse.
    assert (Hother : Pos.eqb (repr (link w l u) z) l = false)
      by (apply Pos.eqb_neq; exact Hneq).
    rewrite Hother in Hcollapse. exact Hcollapse.
  Qed.

  (** ** End root-link structure *)

  (** The linked winning class contains precisely both old root classes. *)
  Lemma size_of_link w l u : wf u -> mem u w -> mem u l ->
    is_root u w -> is_root u l -> w <> l ->
    size_of (link w l u) w = size_of u w + size_of u l.
  Proof.
    intros Hwf Hmw Hml Hrw Hrl Hwl.
    apply (size_of_collapse u (link w l u) w l Hmw Hml
      (repr_of_root u w Hrw) (repr_of_root u l Hrl) Hwl).
    - intro z. apply mem_link. exact Hml.
    - intro z. apply repr_link; assumption.
  Qed.

  (** Linking preserves every class outside the two selected roots. *)
  Lemma size_of_link_other w l u z : wf u -> mem u w -> mem u l ->
    is_root u w -> is_root u l -> w <> l ->
    repr u z <> w -> repr u z <> l -> size_of (link w l u) z = size_of u z.
  Proof.
    intros Hwf Hmw Hml Hrw Hrl Hwl Hzw Hzl.
    apply (size_of_collapse_other u (link w l u) w l z).
    - intro y. apply mem_link. exact Hml.
    - intro y. apply repr_link; assumption.
    - exact Hzw.
    - exact Hzl.
  Qed.

  (** Root linking updates only the winning root's cached size. *)
  Lemma size_at_link w l u r :
    size_at r (link w l u) =
      if Pos.eqb r w then (size_at w u + size_at l u)%N else size_at r u.
  Proof.
    unfold size_at, link. cbn [sizes].
    destruct (Pos.eqb r w) eqn:Hr.
    - apply Pos.eqb_eq in Hr. subst r. rewrite PTrie.get_set_same. reflexivity.
    - apply Pos.eqb_neq in Hr. rewrite PTrie.get_set_other by exact Hr. reflexivity.
  Qed.

  (** ** Link rank preservation *)

  (** Membership makes the union-by-size rank update sound for the linked roots. *)
  Lemma ranked_link_members w l u rk : wf u -> ranked u rk ->
    mem u w -> mem u l -> is_root u w -> is_root u l -> w <> l ->
    size_of u l <= size_of u w ->
    ranked (link w l u)
      (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  Proof.
    intros Hwf Hrank Hmw Hml Hrw Hrl Hwl Hsize. split.
    - exact (link_rank_step w l u rk Hrank Hml Hrw Hwl).
    - intros r Hmr Hroot.
      apply (mem_link w l u r Hml) in Hmr.
      apply (is_root_link w l u r Hwl) in Hroot.
      destruct Hroot as [Hroot Hrlne].
      destruct (Pos.eqb r w) eqn:Hrwtest.
      + apply Pos.eqb_eq in Hrwtest. subst r.
        rewrite (size_of_link w l u Hwf Hmw Hml Hrw Hrl Hwl).
        pose proof (proj2 Hrank w Hmw Hrw) as Hpoww.
        pose proof (proj2 Hrank l Hml Hrl) as Hpowl.
        destruct (le_dec (rk w) (S (rk l))) as [Hmax|Hmax].
        * rewrite Nat.max_r by exact Hmax.
          rewrite Nat.pow_succ_r by lia. lia.
        * rewrite Nat.max_l by lia. lia.
      + apply Pos.eqb_neq in Hrwtest.
        rewrite (size_of_link_other w l u r Hwf Hmw Hml Hrw Hrl Hwl).
        * exact (proj2 Hrank r Hmr Hroot).
        * rewrite (repr_of_root u r Hroot). exact Hrwtest.
        * rewrite (repr_of_root u r Hroot). exact Hrlne.
  Qed.

  (** ** End link rank preservation *)

  (** Linking roots preserves the cardinality, parent closure and both size-cache duties. *)
  Lemma link_wf_fields w l u : wf u -> mem u w -> mem u l ->
    is_root u w -> is_root u l -> w <> l ->
    card (link w l u) = length (support (link w l u)) /\
    (forall x p, PTrieCode.get x (parents (link w l u)) = Some p ->
      mem (link w l u) p) /\
    (forall r, mem (link w l u) r -> is_root (link w l u) r ->
      N.to_nat (size_at r (link w l u)) = size_of (link w l u) r) /\
    (forall r n, PTrieCode.get r (sizes (link w l u)) = Some n ->
      N.to_nat n <= card (link w l u)).
  Proof.
    intros Hwf Hmw Hml Hrw Hrl Hwl.
    pose proof Hwf as [Hcard [Hparent [Hsize [Hsizes Hrank]]]].
    assert (Hsupport : Permutation (support (link w l u)) (support u)).
    { apply support_perm. intro z. apply mem_link. exact Hml. }
    assert (Hsum : size_of u w + size_of u l <= card u).
    { rewrite <- (size_of_link w l u Hwf Hmw Hml Hrw Hrl Hwl).
      rewrite size_of_member by (apply mem_link; assumption).
      eapply Nat.le_trans; [apply filter_length_le|].
      rewrite (Permutation_length Hsupport), <- Hcard. reflexivity. }
    split.
    - rewrite card_link, (Permutation_length Hsupport). exact Hcard.
    - split.
      + intros z p Hget.
        assert (Hmem : mem (link w l u) z) by (unfold mem; rewrite Hget; discriminate).
        pose proof (link_parent_closed w l u Hwf Hmw Hml z Hmem) as Hclosed.
        unfold parent_of in Hclosed. rewrite Hget in Hclosed. exact Hclosed.
      + split.
        * intros r Hmem Hroot. apply (is_root_link w l u r Hwl) in Hroot.
          destruct Hroot as [Hroot Hrlne]. rewrite size_at_link.
          destruct (Pos.eqb r w) eqn:Hrwtest.
          -- apply Pos.eqb_eq in Hrwtest. subst r. rewrite N2Nat.inj_add.
             rewrite (Hsize w Hmw Hrw), (Hsize l Hml Hrl).
             symmetry. apply size_of_link; assumption.
          -- apply Pos.eqb_neq in Hrwtest.
             assert (Hmemold : mem u r) by (apply (mem_link w l u r Hml); exact Hmem).
             rewrite (Hsize r Hmemold Hroot). symmetry.
             apply size_of_link_other; try assumption;
               rewrite (repr_of_root u r Hroot); assumption.
        * intros r n Hget. unfold link in Hget. cbn [sizes] in Hget.
          rewrite card_link. destruct (Pos.eq_dec r w) as [Heq|Hne].
          -- subst r. rewrite PTrie.get_set_same in Hget. injection Hget as Hn. subst n.
             rewrite N2Nat.inj_add, (Hsize w Hmw Hrw), (Hsize l Hml Hrl). exact Hsum.
          -- rewrite PTrie.get_set_other in Hget by exact Hne. eapply Hsizes. exact Hget.
  Qed.

  (** Linking stored roots by class size preserves the complete forest invariant. *)
  Lemma wf_link w l u : wf u -> mem u w -> mem u l ->
    is_root u w -> is_root u l -> w <> l -> size_of u l <= size_of u w ->
    wf (link w l u).
  Proof.
    intros Hwf Hmw Hml Hrw Hrl Hwl Horder.
    destruct (link_wf_fields w l u Hwf Hmw Hml Hrw Hrl Hwl)
      as [Hcard [Hparent [Hsize Hsizes]]].
    unfold wf. refine (conj Hcard (conj Hparent (conj Hsize (conj Hsizes _)))).
    pose proof Hwf as [_ [_ [_ [_ [rk Hrank]]]]].
    exists (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
    apply ranked_link_members; assumption.
  Qed.

  Lemma wf_empty : wf empty.
  Proof.
    unfold wf. split; [reflexivity|]. split.
    - intros x p Hget. change (PTrieCode.get x PTrieCode.empty = Some p) in Hget.
      rewrite PTrie.get_empty in Hget. discriminate.
    - split.
      + intros r Hmem Hroot. exfalso. apply Hmem. apply PTrie.get_empty.
      + split.
        * intros r n Hget. change (PTrieCode.get r PTrieCode.empty = Some n) in Hget.
          rewrite PTrie.get_empty in Hget. discriminate.
        * exists (fun _ => 0). split; intros r Hmem; exfalso;
            apply Hmem; apply PTrie.get_empty.
  Qed.
  Lemma wf_add   : forall x u, wf u -> wf (add x u).
  Proof.
    intros x u Hwf. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hx.
    - unfold add. rewrite Hx. exact Hwf.
    - assert (Hfresh : ~ mem u x) by (unfold mem; rewrite Hx; tauto).
      assert (Hshape : add x u = UF (PTrieCode.set x x (parents u))
        (PTrieCode.set x 1%N (sizes u)) (N.succ (count u))).
      { unfold add. now rewrite Hx. }
      assert (Hcardnew : card (add x u) = S (card u)).
      { rewrite Hshape. unfold card. cbn [count]. apply N2Nat.inj_succ. }
      pose proof Hwf as [Hcard [Hparent [Hsize [Hsizes [rk Hrank]]]]].
      unfold wf. split.
      + rewrite Hcardnew.
        pose proof (Permutation_length (support_add_fresh x u Hfresh)) as Hlength.
        cbn [length] in Hlength. lia.
      + split.
        * intros y q Hy. rewrite Hshape in Hy. cbn [parents] in Hy.
          destruct (Pos.eq_dec y x) as [Heq|Hne].
          -- subst y. rewrite PTrie.get_set_same in Hy. injection Hy as Hq. subst q.
             apply mem_add_raw. auto.
          -- rewrite PTrie.get_set_other in Hy by exact Hne.
             apply mem_add_raw. left. eapply Hparent. exact Hy.
        * split.
          -- intros r Hmem Hroot. rewrite size_add_same by exact Hwf.
             assert (Hrootold : is_root u r).
             { unfold is_root in *. now rewrite parent_of_add in Hroot. }
             destruct (Pos.eq_dec r x) as [Heq|Hne].
             ++ subst r. unfold size_at. rewrite Hshape. cbn [sizes].
                rewrite PTrie.get_set_same. unfold size_of. rewrite Hx. reflexivity.
             ++ unfold size_at at 1. rewrite Hshape. cbn [sizes].
                rewrite PTrie.get_set_other by exact Hne.
                change (N.to_nat (size_at r u) = size_of u r).
                apply Hsize; [apply mem_add_raw in Hmem; tauto|exact Hrootold].
          -- split.
             ++ intros r n Hget. rewrite Hshape in Hget. cbn [sizes] in Hget.
                destruct (Pos.eq_dec r x) as [Heq|Hne].
                ** subst r. rewrite PTrie.get_set_same in Hget.
                   injection Hget as Hn. subst n. rewrite Hcardnew. cbn [N.to_nat]. lia.
                ** rewrite PTrie.get_set_other in Hget by exact Hne.
                   specialize (Hsizes r n Hget). rewrite Hcardnew. lia.
             ++ exists (fun r => if Pos.eqb r x then 0 else rk r). split.
                ** intros r Hmem Hnonroot. rewrite parent_of_add.
                   assert (Hne : r <> x).
                   { intro Heq. subst r. apply Hnonroot. unfold is_root.
                     rewrite parent_of_add. apply parent_fresh. exact Hfresh. }
                   assert (Hmemold : mem u r) by (apply mem_add_raw in Hmem; tauto).
                   assert (Hparentne : parent_of r u <> x).
                   { intro Heq. apply Hfresh. rewrite <- Heq. apply parent_mem; assumption. }
                   rewrite (proj2 (Pos.eqb_neq r x) Hne),
                     (proj2 (Pos.eqb_neq (parent_of r u) x) Hparentne).
                   apply (proj1 Hrank r Hmemold). unfold is_root in *.
                   now rewrite parent_of_add in Hnonroot.
                ** intros r Hmem Hroot. rewrite size_add_same by exact Hwf.
                   destruct (Pos.eq_dec r x) as [Heq|Hne].
                   --- subst r. rewrite Pos.eqb_refl. unfold size_of. rewrite Hx. reflexivity.
                   --- rewrite (proj2 (Pos.eqb_neq r x) Hne). apply (proj2 Hrank).
                       +++ apply mem_add_raw in Hmem. tauto.
                       +++ unfold is_root in *. now rewrite parent_of_add in Hroot.
  Qed.
  (** ** Compression and find helpers *)

  (** Repeated updates replace exactly the keys listed in the compression path. *)
  Lemma fold_compress_get (r : positive) (path : list positive) (z : positive) :
    forall m : PTrieCode.t positive,
    PTrieCode.get z (fold_left (fun m y => PTrieCode.set y r m) path m) =
      if in_dec Pos.eq_dec z path then Some r else PTrieCode.get z m.
  Proof.
    induction path as [|y path IH]; intro m; [reflexivity|].
    cbn [fold_left]. rewrite IH.
    destruct (in_dec Pos.eq_dec z path) as [Hin | Hout].
    - destruct (in_dec Pos.eq_dec z (y :: path)) as [Hyes | Hno]; [reflexivity|].
      exfalso. apply Hno. right; exact Hin.
    - destruct (Pos.eq_dec z y) as [Heq | Hne].
      + subst z. rewrite PTrie.get_set_same.
        destruct (in_dec Pos.eq_dec y (y :: path)) as [Hyes | Hno]; [reflexivity|].
        exfalso. apply Hno. left; reflexivity.
      + rewrite PTrie.get_set_other by exact Hne.
        destruct (in_dec Pos.eq_dec z (y :: path)) as [Hin | Hno]; [|reflexivity].
        destruct Hin as [Heq | Hin]; [congruence | contradiction].
  Qed.

  (** Compression redirects the listed parent bindings and preserves every other lookup. *)
  Lemma compress_get r path u z :
    PTrieCode.get z (parents (compress r path u)) =
      if in_dec Pos.eq_dec z path then Some r else PTrieCode.get z (parents u).
  Proof.
    apply fold_compress_get.
  Qed.

  (** Updating existing path members preserves the parent-map domain. *)
  Lemma mem_compress r path u z :
    (forall y, In y path -> mem u y) -> (mem (compress r path u) z <-> mem u z).
  Proof.
    intro Hpath. unfold mem. rewrite compress_get.
    destruct (in_dec Pos.eq_dec z path) as [Hin | Hout]; [|reflexivity].
    split; [intros _; apply Hpath; exact Hin | intros _; discriminate].
  Qed.

  (** Compression leaves the stored membership count unchanged. *)
  Lemma card_compress r path u : card (compress r path u) = card u.
  Proof.
    reflexivity.
  Qed.

  (** A compressed parent is the selected root exactly on the supplied path. *)
  Lemma parent_compress r path u z :
    parent_of z (compress r path u) =
      if in_dec Pos.eq_dec z path then r else parent_of z u.
  Proof.
    unfold parent_of. rewrite compress_get.
    destruct (in_dec Pos.eq_dec z path); reflexivity.
  Qed.

  (** Redirecting nonroot members of one class leaves precisely the old roots fixed. *)
  Lemma root_compress r path u z :
    (forall y, In y path -> repr u y = r /\ y <> r) ->
    (is_root (compress r path u) z <-> is_root u z).
  Proof.
    intro Hpath. unfold is_root at 1. rewrite parent_compress.
    destruct (in_dec Pos.eq_dec z path) as [Hin | Hout]; [|reflexivity].
    destruct (Hpath z Hin) as [Hrepr Hne]. split; [congruence|].
    intro Hroot. pose proof (repr_of_root u z Hroot). congruence.
  Qed.

  (** Every old path to a root still reaches that root after taking compression shortcuts. *)
  Lemma compress_iter r path u n : wf u ->
    (forall y, In y path -> repr u y = r /\ y <> r) ->
    forall x q, is_root u q -> Nat.iter n (fun y => parent_of y u) x = q ->
      Nat.iter n (fun y => parent_of y (compress r path u)) x = q.
  Proof.
    intros Hwf Hpath. induction n as [|n IH]; intros x q Hroot Hsteps;
      [exact Hsteps|].
    pose proof (repr_iter u x (S n) Hwf) as Hrepr.
    rewrite Hsteps, (repr_of_root u q Hroot) in Hrepr.
    rewrite Nat.iter_succ_r in Hsteps |- *. rewrite parent_compress.
    destruct (in_dec Pos.eq_dec x path) as [Hin | Hout].
    - destruct (Hpath x Hin) as [Hclass Hne].
      assert (Hqr : q = r) by congruence. rewrite Hqr in Hroot |- *.
      apply iter_root. apply (proj2 (root_compress r path u r Hpath)). exact Hroot.
    - apply IH; assumption.
  Qed.

  (** Compression preserves every representative without assuming the resulting invariant. *)
  Lemma repr_compress r path u x : wf u ->
    (forall y, In y path -> repr u y = r /\ y <> r) ->
    repr (compress r path u) x = repr u x.
  Proof.
    intros Hwf Hpath. unfold repr at 1. rewrite card_compress.
    apply compress_iter; [exact Hwf | exact Hpath | apply repr_root; exact Hwf | reflexivity].
  Qed.

  (** Compression preserves class cardinalities, including absent singleton queries. *)
  Lemma size_of_compress r path u x : wf u ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    size_of (compress r path u) x = size_of u x.
  Proof.
    intros Hwf Hpath. apply size_of_transport.
    - intro y. apply mem_compress. intros z Hz. exact (proj1 (Hpath z Hz)).
    - intro y. apply repr_compress; [exact Hwf|].
      intros z Hz. exact (proj2 (Hpath z Hz)).
  Qed.

  (** Ghost ranks still increase along shortcuts and retain their root-size certificates. *)
  Lemma ranked_compress r path u rk : wf u -> ranked u rk ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    ranked (compress r path u) rk.
  Proof.
    intros Hwf Hrank Hpath.
    assert (Hmembers : forall y, In y path -> mem u y).
    { intros y Hy. exact (proj1 (Hpath y Hy)). }
    assert (Hclasses : forall y, In y path -> repr u y = r /\ y <> r).
    { intros y Hy. exact (proj2 (Hpath y Hy)). }
    split.
    - intros x Hmem Hnonroot. apply (proj1 (mem_compress r path u x Hmembers)) in Hmem.
      assert (Hold : ~ is_root u x).
      { intro Hroot. apply Hnonroot. apply (proj2 (root_compress r path u x Hclasses)).
        exact Hroot. }
      rewrite parent_compress. destruct (in_dec Pos.eq_dec x path) as [Hin | Hout].
      + pose proof (proj1 Hrank x Hmem Hold) as Hstep.
        pose proof (rank_le_repr u rk (parent_of x u) Hwf Hrank
          (parent_mem u x Hwf Hmem)) as Htop.
        rewrite repr_parent, (proj1 (Hclasses x Hin)) in Htop by exact Hwf. lia.
      + exact (proj1 Hrank x Hmem Hold).
    - intros q Hmem Hroot. rewrite size_of_compress by assumption.
      apply (proj2 Hrank).
      + apply (proj1 (mem_compress r path u q Hmembers)); exact Hmem.
      + apply (proj1 (root_compress r path u q Hclasses)); exact Hroot.
  Qed.

  (** Compression preserves the full forest invariant when every path entry is a nonroot member. *)
  Lemma wf_compress r path u : wf u ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    wf (compress r path u).
  Proof.
    intros Hwf Hpath. pose proof Hwf as [Hcard [Hparents [Hsizes [Hbounds [rk Hrank]]]]].
    assert (Hmembers : forall y, In y path -> mem u y).
    { intros y Hy. exact (proj1 (Hpath y Hy)). }
    assert (Hclasses : forall y, In y path -> repr u y = r /\ y <> r).
    { intros y Hy. exact (proj2 (Hpath y Hy)). }
    split.
    - rewrite card_compress, Hcard. apply Permutation_length.
      apply support_perm. intro y. symmetry. apply mem_compress; exact Hmembers.
    - split.
      + intros x p Hget. apply (proj2 (mem_compress r path u p Hmembers)).
        rewrite compress_get in Hget.
        destruct (in_dec Pos.eq_dec x path) as [Hin | Hout].
        * injection Hget as Heq. subst p. rewrite <- (proj1 (Hclasses x Hin)).
          apply repr_mem; [exact Hwf | apply Hmembers; exact Hin].
        * apply (Hparents x p Hget).
      + split.
        * intros q Hmem Hroot. change (N.to_nat (size_at q u) = size_of (compress r path u) q).
          rewrite size_of_compress by assumption. apply Hsizes.
          -- apply (proj1 (mem_compress r path u q Hmembers)); exact Hmem.
          -- apply (proj1 (root_compress r path u q Hclasses)); exact Hroot.
        * split.
          -- intros q n Hget. apply (Hbounds q n Hget).
          -- exists rk. apply ranked_compress; assumption.
  Qed.

  (** Finding returns the old representative and preserves the forest, classes, and roots. *)
  Lemma find_correct x u : wf u ->
    fst (find x u) = repr u x /\ wf (snd (find x u)) /\
    (forall z, mem (snd (find x u)) z <-> mem u z) /\
    (forall z, repr (snd (find x u)) z = repr u z) /\
    (forall z, size_of (snd (find x u)) z = size_of u z) /\
    (forall z, is_root (snd (find x u)) z <-> is_root u z).
  Proof.
    intro Hwf. pose proof (walk_root x u Hwf) as Hroot.
    pose proof (proj2 (walk_path x u Hwf)) as Hmembers.
    pose proof (walk_path_nonroot x u Hwf) as Hnonroot.
    unfold find. destruct (walk x u) as [r path] eqn:Hwalk. cbn [fst snd] in *.
    assert (Hpath : forall y, In y path -> mem u y /\ repr u y = r /\ y <> r).
    { intros y Hy. destruct (Hmembers y Hy) as [Hmem Hrepr].
      split; [exact Hmem|]. split; [congruence | apply Hnonroot; exact Hy]. }
    split; [exact Hroot|]. split; [apply wf_compress; assumption|].
    split.
    - intro z. apply mem_compress. intros y Hy. exact (proj1 (Hpath y Hy)).
    - split.
      + intro z. apply repr_compress; [exact Hwf|].
        intros y Hy. exact (proj2 (Hpath y Hy)).
      + split.
        * intro z. apply size_of_compress; assumption.
        * intro z. apply root_compress. intros y Hy. exact (proj2 (Hpath y Hy)).
  Qed.

  (** The two lookups before linking preserve old classes and expose both stored roots. *)
  Lemma union_find_correct x y u : wf u -> forall rx v ry w,
    find x (add y (add x u)) = (rx, v) -> find y v = (ry, w) ->
    rx = repr u x /\ ry = repr u y /\ wf w /\
    (forall z, mem w z <-> mem u z \/ z = x \/ z = y) /\
    (forall z, repr w z = repr u z) /\
    (forall z, size_of w z = size_of u z) /\
    (mem w rx /\ is_root w rx) /\ (mem w ry /\ is_root w ry).
  Proof.
    intros Hwf rx v ry w Hx Hy.
    pose proof (wf_add x u Hwf) as Hax.
    pose proof (wf_add y (add x u) Hax) as Haxy.
    pose proof (find_correct x (add y (add x u)) Haxy) as Hfx.
    rewrite Hx in Hfx. cbn [fst snd] in Hfx.
    destruct Hfx as [Hrx [Hv [Hv_mem [Hv_repr [Hv_size Hv_root]]]]].
    pose proof (find_correct y v Hv) as Hfy.
    rewrite Hy in Hfy. cbn [fst snd] in Hfy.
    destruct Hfy as [Hry [Hw [Hw_mem [Hw_repr [Hw_size Hw_root]]]]].
    assert (Hrepr : forall z, repr (add y (add x u)) z = repr u z).
    { intro z. rewrite !repr_add_same by assumption. reflexivity. }
    assert (Hsize : forall z, size_of (add y (add x u)) z = size_of u z).
    { intro z. rewrite !size_add_same by assumption. reflexivity. }
    assert (Hxmem : mem (add y (add x u)) x).
    { apply mem_add_raw. left. apply mem_add_raw. right; reflexivity. }
    assert (Hymem : mem (add y (add x u)) y).
    { apply mem_add_raw. right; reflexivity. }
    split; [rewrite Hrx; apply Hrepr|].
    split; [rewrite Hry, Hv_repr; apply Hrepr|].
    split; [exact Hw|]. split.
    - intro z. rewrite Hw_mem, Hv_mem, !mem_add_raw. tauto.
    - split.
      + intro z. rewrite Hw_repr, Hv_repr. apply Hrepr.
      + split.
        * intro z. rewrite Hw_size, Hv_size. apply Hsize.
        * split; split.
          -- apply (proj2 (Hw_mem rx)), (proj2 (Hv_mem rx)).
             rewrite Hrx. apply repr_mem; assumption.
          -- apply (proj2 (Hw_root rx)), (proj2 (Hv_root rx)).
             rewrite Hrx. apply repr_root; exact Haxy.
          -- apply (proj2 (Hw_mem ry)). rewrite Hry. apply repr_mem; [exact Hv|].
             apply (proj2 (Hv_mem y)); exact Hymem.
          -- apply (proj2 (Hw_root ry)). rewrite Hry. apply repr_root; exact Hv.
  Qed.

  (** ** End compression and find helpers *)

  Lemma wf_find  : forall x u, wf u -> wf (snd (find x u)).
  Proof.
    intros x u Hwf. exact (proj1 (proj2 (find_correct x u Hwf))).
  Qed.
  Lemma wf_union : forall x y u, wf u -> wf (snd (union x y u)).
  Proof.
    intros x y u Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    destruct (Pos.eqb rx ry) eqn:Heq; cbn [snd]; [exact Hw|].
    apply Pos.eqb_neq in Heq.
    pose proof (proj1 (proj2 (proj2 Hw)) rx Hmx Hrootx) as Hsx.
    pose proof (proj1 (proj2 (proj2 Hw)) ry Hmy Hrooty) as Hsy.
    destruct (N.leb (size_at ry w) (size_at rx w)) eqn:Hle; cbn [snd].
    - apply (wf_link rx ry w Hw Hmx Hmy Hrootx Hrooty Heq).
      apply N.leb_le in Hle. lia.
    - apply (wf_link ry rx w Hw Hmy Hmx Hrooty Hrootx ltac:(congruence)).
      apply N.leb_gt in Hle. lia.
  Qed.
  Lemma mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x).
  Proof.
    intros x u y Hwf. apply mem_add_raw.
  Qed.
  Lemma mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y).
  Proof.
    intros x u y Hwf. exact (proj1 (proj2 (proj2 (find_correct x u Hwf))) y).
  Qed.
  Lemma mem_union : forall x y u z, wf u -> (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  Proof.
    intros x y u z Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    destruct (Pos.eqb rx ry); cbn [snd]; [apply Hmem|].
    destruct (N.leb (size_at ry w) (size_at rx w)); cbn [snd].
    - rewrite mem_link by exact Hmy. apply Hmem.
    - rewrite mem_link by exact Hmx. apply Hmem.
  Qed.
  Lemma repr_empty : forall x, repr empty x = x. Proof. reflexivity. Qed.
  Lemma repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x.
  Proof.
    intros u x Hwf. apply repr_of_root. apply repr_root. exact Hwf.
  Qed.
  Lemma repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y.
  Proof.
    exact repr_add_same.
  Qed.
  Lemma find_repr  : forall x u, wf u -> fst (find x u) = repr u x.
  Proof.
    intros x u Hwf. exact (proj1 (find_correct x u Hwf)).
  Qed.
  (** The read-only root is the root that find returns. *)
  Lemma root_of_find : forall x u, root_of x u = fst (find x u).
  Proof.
    intros x u. reflexivity.
  Qed.
  (** On a well-formed forest the read-only root is the representative. *)
  Lemma root_of_repr : forall x u, wf u -> root_of x u = repr u x.
  Proof.
    intros x u Hwf. exact (walk_root x u Hwf).
  Qed.
  Lemma find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y.
  Proof.
    intros x u y Hwf.
    exact (proj1 (proj2 (proj2 (proj2 (find_correct x u Hwf)))) y).
  Qed.
  Lemma union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z.
  Proof.
    intros x y u u1 Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr Hrest]]]]].
    destruct (Pos.eqb rx ry) eqn:Heq.
    - intro Hresult. injection Hresult as Hstate. subst u1.
      apply Pos.eqb_eq in Heq. split; [congruence|exact Hrepr].
    - destruct (N.leb (size_at ry w) (size_at rx w)); discriminate.
  Qed.
  Lemma union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z.
  Proof.
    intros x y u win lose u1 Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    destruct (Pos.eqb rx ry) eqn:Heq; [discriminate|].
    apply Pos.eqb_neq in Heq.
    destruct (N.leb (size_at ry w) (size_at rx w)); intro Hresult;
      injection Hresult as Hwin Hlose Hstate; subst win lose u1.
    - split; [congruence|]. split; [left; split; assumption|].
      intro z. rewrite (repr_link rx ry w z Hw Hmx Hmy Hrootx Hrooty Heq), Hrepr.
      reflexivity.
    - split; [congruence|]. split; [right; split; assumption|].
      intro z. rewrite (repr_link ry rx w z Hw Hmy Hmx Hrooty Hrootx ltac:(congruence)).
      rewrite Hrepr. reflexivity.
  Qed.
  Lemma union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w.
  Proof.
    intros x y u win lose u1 Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    pose proof (proj1 (proj2 (proj2 Hw)) rx Hmx Hrootx) as Hsx.
    pose proof (proj1 (proj2 (proj2 Hw)) ry Hmy Hrooty) as Hsy.
    rewrite Hsize in Hsx, Hsy.
    destruct (Pos.eqb rx ry); [discriminate|].
    destruct (N.leb (size_at ry w) (size_at rx w)) eqn:Hle; intro Hresult;
      injection Hresult as Hwin Hlose Hstate; subst win lose.
    - apply N.leb_le in Hle. lia.
    - apply N.leb_gt in Hle. lia.
  Qed.
  Lemma size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l.
  Proof.
    intros x y u win lose u1 Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    destruct (Pos.eqb rx ry) eqn:Heq; [discriminate|].
    apply Pos.eqb_neq in Heq.
    destruct (N.leb (size_at ry w) (size_at rx w)); intro Hresult;
      injection Hresult as Hwin Hlose Hstate; subst win lose u1.
    - rewrite (size_of_link rx ry w Hw Hmx Hmy Hrootx Hrooty Heq), !Hsize.
      reflexivity.
    - rewrite (size_of_link ry rx w Hw Hmy Hmx Hrooty Hrootx ltac:(congruence)).
      rewrite !Hsize. reflexivity.
  Qed.
  Lemma size_of_le_card : forall u x, wf u -> mem u x -> size_of u x <= card u.
  Proof.
    exact size_member_bound.
  Qed.
  Lemma card_empty : card empty = 0. Proof. reflexivity. Qed.
  Lemma card_add   : forall x u, wf u -> card (add x u) <= card u + 1.
  Proof.
    intros x u Hwf. unfold add.
    destruct (PTrieCode.get x (parents u)); [lia|].
    unfold card. cbn [count]. rewrite N2Nat.inj_succ. lia.
  Qed.
  Lemma card_find  : forall x u, wf u -> card (snd (find x u)) = card u. Proof. reflexivity. Qed.
  Lemma card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2.
  Proof.
    intros x y u Hwf.
    pose proof (card_add x u Hwf) as Hxcard.
    pose proof (card_add y (add x u) (wf_add x u Hwf)) as Hycard.
    unfold union. destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    assert (Hvcard : card v = card (add y (add x u))).
    { change (card (snd (rx, v)) = card (add y (add x u))).
      rewrite <- Hx. reflexivity. }
    assert (Hwcard : card w = card v).
    { change (card (snd (ry, w)) = card v). rewrite <- Hy. reflexivity. }
    destruct (Pos.eqb rx ry); cbn [snd]; [lia|].
    destruct (N.leb (size_at ry w) (size_at rx w));
      change (card w <= card u + 2); lia.
  Qed.
  Lemma width_mem  : forall u x, wf u -> mem u x -> Pos.size_nat x <= width u.
  Proof.
    intros u x _ Hmem. apply support_width. exact Hmem.
  Qed.
  Lemma size_of_fresh : forall u x, wf u -> ~ mem u x -> size_of u x = 1.
  Proof.
    intros u x Hwf Hfresh. unfold size_of.
    destruct (PTrieCode.get x (parents u)) eqn:Hx; [|reflexivity].
    exfalso. apply Hfresh. unfold mem. rewrite Hx. discriminate.
  Qed.
  Lemma size_of_repr : forall u x, wf u -> size_of u x = size_of u (repr u x).
  Proof.
    intros u x Hwf. destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hx.
    - assert (Hmem : mem u x) by (unfold mem; rewrite Hx; discriminate).
      rewrite (size_of_member u x Hmem), size_of_member by (apply repr_mem; assumption).
      rewrite repr_idem by exact Hwf. reflexivity.
    - rewrite repr_fresh; [reflexivity|exact Hwf|]. unfold mem. rewrite Hx. tauto.
  Qed.
  Lemma size_of_add : forall x u y, wf u -> size_of (add x u) y = size_of u y.
  Proof.
    exact size_add_same.
  Qed.
  Lemma size_of_find : forall x u y, wf u -> size_of (snd (find x u)) y = size_of u y.
  Proof.
    intros x u y Hwf.
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (find_correct x u Hwf))))) y).
  Qed.
  Lemma size_of_union_other : forall x y u o u1 z, wf u -> union x y u = (o, u1) ->
  (forall w l, o = Some (w, l) -> repr u z <> w /\ repr u z <> l) ->
  size_of u1 z = size_of u z.
  Proof.
    intros x y u o u1 z Hwf. unfold union.
    destruct (find x (add y (add x u))) as [rx v] eqn:Hx. cbn [fst snd].
    destruct (find y v) as [ry w] eqn:Hy. cbn [fst snd].
    destruct (union_find_correct x y u Hwf rx v ry w Hx Hy)
      as [Hrx [Hry [Hw [Hmem [Hrepr [Hsize [[Hmx Hrootx] [Hmy Hrooty]]]]]]]].
    destruct (Pos.eqb rx ry) eqn:Heq.
    - intros Hresult Hother. injection Hresult as Ho Hstate. subst o u1. apply Hsize.
    - apply Pos.eqb_neq in Heq.
      destruct (N.leb (size_at ry w) (size_at rx w)); intros Hresult Hother;
        injection Hresult as Ho Hstate; subst o u1.
      + destruct (Hother rx ry eq_refl) as [Hnotx Hnoty].
        rewrite (size_of_link_other rx ry w z Hw Hmx Hmy Hrootx Hrooty Heq).
        * apply Hsize.
        * rewrite Hrepr. exact Hnotx.
        * rewrite Hrepr. exact Hnoty.
      + destruct (Hother ry rx eq_refl) as [Hnoty Hnotx].
        rewrite (size_of_link_other ry rx w z Hw Hmy Hmx Hrooty Hrootx ltac:(congruence)).
        * apply Hsize.
        * rewrite Hrepr. exact Hnoty.
        * rewrite Hrepr. exact Hnotx.
  Qed.

  Lemma width_empty : width empty = 0.
  Proof.
    reflexivity.
  Qed.
  Lemma width_add : forall x u, wf u ->
  width (add x u) <= Nat.max (width u) (Pos.size_nat x).
  Proof.
    intros x u Hwf. apply width_le_members. intros y Hy.
    apply mem_add_raw in Hy. destruct Hy as [Hy|Hy].
    - eapply Nat.le_trans; [apply support_width; exact Hy|apply Nat.le_max_l].
    - subst y. apply Nat.le_max_r.
  Qed.
  Lemma width_find : forall x u, wf u -> width (snd (find x u)) <= width u.
  Proof.
    intros x u Hwf. apply width_le_members. intros y Hy.
    apply support_width. apply (proj1 (mem_find x u y Hwf)); exact Hy.
  Qed.
  Lemma width_union : forall x y u, wf u ->
  width (snd (union x y u)) <= Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)).
  Proof.
    intros x y u Hwf. apply width_le_members. intros z Hz.
    apply (proj1 (mem_union x y u z Hwf)) in Hz. destruct Hz as [Hz | [Hz | Hz]].
    - eapply Nat.le_trans; [apply support_width; exact Hz | apply Nat.le_max_l].
    - subst z. eapply Nat.le_trans; [apply Nat.le_max_l | apply Nat.le_max_r].
    - subst z. eapply Nat.le_trans; [apply Nat.le_max_r | apply Nat.le_max_r].
  Qed.
End UnionFind.

Module UnionFindT <: UNION_FIND_ALL.
  Include UnionFind.

  TimeFun add.
  TimeFun size_at.
  TimeFun link.
  TimeFun union.

  Definition c_uf : N := 131072.

  Definition k_get : N := 2048.
  Definition k_step : N := 4096.
  Definition k_walk : N := 16384.
  Definition k_comp : N := 2048.
  Definition k_link : N := 8192.

  (** Binary counters fit the logarithm of any natural upper bound. *)
  Local Lemma counter_width (n : N) (P : nat) :
    N.to_nat n <= P -> N.size_nat n <= Nat.log2 P + 1.
  Proof.
    destruct n as [|p]; intro Hbound; [cbn [N.size_nat]; lia |].
    change (Pos.to_nat p <= P) in Hbound.
    change (Pos.size_nat p <= Nat.log2 P + 1). apply Pos.size_nat_least.
    pose proof (Pos2Nat.is_pos p) as Hpositive.
    pose proof (proj2 (Nat.log2_spec P ltac:(lia))) as Hpower.
    replace (Nat.log2 P + 1) with (S (Nat.log2 P)) by lia. lia.
  Qed.

  (** Default singleton sizes and stored sizes share the count's width budget. *)
  Local Lemma size_at_width (u : t) (r : positive) : wf u ->
    N.size_nat (size_at r u) <= Nat.log2 (card u) + 1.
  Proof.
    intros [_ [_ [_ [Hsizes _]]]]. unfold size_at.
    destruct (PTrieCode.get r (sizes u)) as [n|] eqn:Hget.
    - apply counter_width. exact (Hsizes r n Hget).
    - cbn [N.size_nat Pos.size_nat]. lia.
  Qed.

  (** A reached parent is either the queried key or a stored member. *)
  Local Lemma parent_width (u : t) (x : positive) W :
    wf u -> Pos.size_nat x <= W -> width u <= W ->
    Pos.size_nat (parent_of x u) <= W.
  Proof.
    intros Hwf Hx Hu. unfold parent_of.
    destruct (PTrieCode.get x (parents u)) as [p|] eqn:Hget; [|exact Hx].
    pose proof (proj1 (proj2 Hwf) x p Hget) as Hp.
    pose proof (width_mem u p Hwf Hp). lia.
  Qed.

  Local Lemma size_at_clock (r : positive) (u : t) :
    (T_size_at r u <= k_get * N.of_nat (Pos.size_nat r + 1))%N.
  Proof.
    pose proof (PTrieT.T_get_le N r (sizes u)) as Hget.
    change (@PTrieCode.T_get N r (sizes u) <=
      1024 * N.of_nat (Pos.size_nat r + 1))%N in Hget.
    time_unfold T_size_at. time_unfold T_sizes.
    destruct (PTrieCode.get r (sizes u)); unfold k_get;
      rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; lia.
  Qed.

  (** Retain slack in the public constant for union's two singleton insertions. *)
  Local Lemma add_clock (x : positive) (u : t) : wf u ->
    (T_add x u <= 4096 *
      N.of_nat (Pos.size_nat x + Nat.log2 (card u) + 2))%N.
  Proof.
    intro Hwf.
    pose proof (PTrieT.T_get_le positive x (parents u)) as Hget.
    pose proof (PTrieT.T_set_le positive x x (parents u)) as Hparent.
    pose proof (PTrieT.T_set_le N x 1%N (sizes u)) as Hsize.
    change (PTrieCode.T_get x (parents u) <=
      1024 * N.of_nat (Pos.size_nat x + 1))%N in Hget.
    change (PTrieCode.T_set x x (parents u) <=
      1024 * N.of_nat (Pos.size_nat x + 1))%N in Hparent.
    change (PTrieCode.T_set x 1%N (sizes u) <=
      1024 * N.of_nat (Pos.size_nat x + 1))%N in Hsize.
    pose proof (N.T_succ_le (count u)) as Hsucc.
    pose proof (counter_width (count u) (card u) (Nat.le_refl _)) as Hbits.
    apply time_of_nat_le in Hbits.
    time_unfold T_add. time_unfold T_parents.
    time_unfold T_sizes. time_unfold T_count.
    destruct (PTrieCode.get x (parents u));
      repeat rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; lia.
  Qed.

  Lemma T_add_le : forall x u, (wf u ->
    T_add x u <= c_uf * N.of_nat (Pos.size_nat x + Nat.log2 (card u) + 2))%N.
  Proof.
    intros x u Hwf. eapply N.le_trans; [exact (add_clock x u Hwf)|].
    apply N.mul_le_mono_r. unfold c_uf. lia.
  Qed.

  Lemma F1_ranked : forall u, wf u -> exists rk, ranked u rk.
  Proof.
    intros u [_ [_ [_ [_ Hranks]]]]. exact Hranks.
  Qed.
  Lemma F2_rank_log : forall u rk x, wf u -> ranked u rk -> mem u x ->
    rk x <= Nat.log2 (card u).
  Proof.
    exact rank_log.
  Qed.
  Lemma F3_walk_root : forall x u, wf u -> fst (walk x u) = repr u x.
  Proof.
    exact walk_root.
  Qed.
  Lemma F4_walk_path : forall x u, wf u ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  Proof.
    exact walk_path.
  Qed.
  Lemma F5_compress : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    ranked (compress r path u) rk.
  Proof.
    intros u rk r path Hwf Hrank Hroot Hpath. apply ranked_compress; assumption.
  Qed.
  Lemma F6_link : forall u rk w l, wf u -> ranked u rk ->
    mem u w -> mem u l -> is_root u w -> is_root u l -> w <> l ->
    size_of u l <= size_of u w ->
    ranked (link w l u)
      (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  Proof.
    intros u rk w l Hwf Hrank Hmw Hml Hrw Hrl Hwl Hsize.
    apply ranked_link_members; assumption.
  Qed.

  Lemma T1_parent_of : forall x u,
    (T_parent_of x u <= k_get * N.of_nat (Pos.size_nat x + 1))%N.
  Proof.
    intros x u. pose proof (PTrieT.T_get_le positive x (parents u)) as Hget.
    change (@PTrieCode.T_get positive x (parents u) <=
      1024 * N.of_nat (Pos.size_nat x + 1))%N in Hget.
    time_unfold T_parent_of. time_unfold T_parents.
    destruct (PTrieCode.get x (parents u)); unfold k_get;
      rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; lia.
  Qed.

  Local Lemma walk_step_clock (u : t) (s : positive * list positive) W :
    wf u -> Pos.size_nat (fst s) <= W -> width u <= W ->
    (T_walk_step u s <= k_step * N.of_nat (W + 1))%N.
  Proof.
    intros Hwf Hs Hu.
    pose proof (T1_parent_of (fst s) u) as Hparent.
    pose proof (Pos.T_eqb_le (parent_of (fst s) u) (fst s)) as Heq.
    pose proof (parent_width u (fst s) W Hwf Hs Hu) as Hp.
    apply time_of_nat_le in Hs. apply time_of_nat_le in Hp.
    time_unfold T_walk_step. time_unfold @Datatypes.T_fst.
    time_unfold @Datatypes.T_snd.
    destruct (Pos.eqb (parent_of (fst s) u) (fst s)); unfold k_get, k_step in *;
      repeat rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; lia.
  Qed.

  Lemma T2_walk_step : forall u s, (wf u -> mem u (fst s) ->
    T_walk_step u s <= k_step * N.of_nat (width u + 1))%N.
  Proof.
    intros u s Hwf Hmem. apply walk_step_clock; [exact Hwf| |lia].
    exact (width_mem u (fst s) Hwf Hmem).
  Qed.

  (** The actual unary fuel pays each reached step and the loop call. *)
  Local Lemma walk_fuel_clock (u : t) W fuel :
    wf u -> width u <= W -> forall s,
    Pos.size_nat (fst s) <= W ->
    (T_loop_fuel (walk_step u) (fun s0 => T_walk_step u s0) fuel s <=
      (k_step * N.of_nat (W + 1) + 1) * N.of_nat fuel + 1)%N.
  Proof.
    intros Hwf Hu. induction fuel as [|fuel IH]; intros s Hs.
    - time_unfold @T_loop_fuel. lia.
    - pose proof (walk_step_clock u s W Hwf Hs Hu) as Hclock.
      time_unfold @T_loop_fuel.
      destruct (walk_step u s) as [s1|r] eqn:Hstep.
      + assert (Hs1 : Pos.size_nat (fst s1) <= W).
        { unfold walk_step in Hstep.
          destruct (Pos.eqb (parent_of (fst s) u) (fst s)); [discriminate|].
          inversion Hstep; subst s1. cbn [fst].
          exact (parent_width u (fst s) W Hwf Hs Hu). }
        specialize (IH s1 Hs1). rewrite Nat2N.inj_succ, N.mul_succ_r. lia.
      + rewrite Nat2N.inj_succ, N.mul_succ_r. lia.
  Qed.

  Lemma T3_walk : forall x u, (wf u ->
    T_walk x u <= k_walk * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof.
    intros x u Hwf.
    pose proof (walk_fuel_clock u (Nat.max (width u) (Pos.size_nat x))
      (S (N.size_nat (count u))) Hwf (Nat.le_max_l _ _)
      (x, []) (Nat.le_max_r _ _)) as Hloop.
    pose proof (counter_width (count u) (card u) (Nat.le_refl _)) as Hbits.
    pose proof (N.T_size_nat_le (count u)) as Hsize.
    apply time_of_nat_le in Hbits.
    time_unfold T_walk. time_unfold T_count.
    unfold k_step, k_walk in *.
    repeat rewrite Nat2N.inj_add in *. rewrite Nat2N.inj_succ in Hloop.
    cbn [N.of_nat] in *. nia.
  Qed.

  (** The compression callback is bounded only on the path's actual keys. *)
  Local Lemma compress_fold_clock (r : positive) (path : list positive) W :
    (forall y, In y path -> Pos.size_nat y <= W) -> forall m,
    (List.T_fold_left (fun m0 y => PTrieCode.set y r m0)
      (fun m0 y => 1 + PTrieCode.T_set y r m0)%N path m <=
      (1024 * N.of_nat (W + 1) + 2) * N.of_nat (length path) + 1)%N.
  Proof.
    induction path as [|y path IH]; intros Hkeys m.
    - time_unfold @List.T_fold_left. cbn [length]. lia.
    - pose proof (PTrieT.T_set_le positive y r m) as Hset.
      change (PTrieCode.T_set y r m <=
        1024 * N.of_nat (Pos.size_nat y + 1))%N in Hset.
      pose proof (Hkeys y (or_introl eq_refl)) as Hy.
      apply time_of_nat_le in Hy.
      specialize (IH ltac:(intros z Hz; apply Hkeys; now right)
        (PTrieCode.set y r m)).
      time_unfold @List.T_fold_left. cbn [length].
      repeat rewrite Nat2N.inj_add in *. rewrite Nat2N.inj_succ.
      cbn [N.of_nat] in *. nia.
  Qed.

  Lemma T4_compress : forall r path u, (wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * N.of_nat (length path + 1) *
      N.of_nat (width u + 1))%N.
  Proof.
    intros r path u Hwf Hpath.
    pose proof (compress_fold_clock r path (width u)
      ltac:(intros y Hy; exact (width_mem u y Hwf (Hpath y Hy)))
      (parents u)) as Hfold.
    time_unfold T_compress. time_unfold T_parents.
    time_unfold T_sizes. time_unfold T_count.
    unfold k_comp. repeat rewrite Nat2N.inj_add in *.
    cbn [N.of_nat] in *. nia.
  Qed.
  Lemma T5_link : forall w l u, (wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * N.of_nat (width u + Nat.log2 (card u) + 2))%N.
  Proof.
    intros w l u Hwf Hw Hl.
    pose proof (width_mem u w Hwf Hw) as Hwidthw.
    pose proof (width_mem u l Hwf Hl) as Hwidthl.
    pose proof (size_at_width u w Hwf) as Hbitsw.
    pose proof (size_at_width u l Hwf) as Hbitsl.
    apply time_of_nat_le in Hwidthw. apply time_of_nat_le in Hwidthl.
    apply time_of_nat_le in Hbitsw. apply time_of_nat_le in Hbitsl.
    pose proof (size_at_clock w u) as Hsizew.
    pose proof (size_at_clock l u) as Hsizel.
    pose proof (PTrieT.T_set_le positive l w (parents u)) as Hparent.
    pose proof (PTrieT.T_set_le N w (size_at w u + size_at l u)%N (sizes u)) as Hsizes.
    change (PTrieCode.T_set l w (parents u) <=
      1024 * N.of_nat (Pos.size_nat l + 1))%N in Hparent.
    change (PTrieCode.T_set w (size_at w u + size_at l u)%N (sizes u) <=
      1024 * N.of_nat (Pos.size_nat w + 1))%N in Hsizes.
    pose proof (N.T_add_le (size_at w u) (size_at l u)) as Hadd.
    time_unfold T_link. time_unfold T_parents.
    time_unfold T_sizes. time_unfold T_count.
    unfold k_get, k_link in *. repeat rewrite Nat2N.inj_add in *.
    cbn [N.of_nat] in *. lia.
  Qed.
  (** Keep the two find charges below the common public union constant. *)
  Local Lemma find_clock (x : positive) (u : t) : wf u ->
    (T_find x u <= 32768 * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof.
    intro Hwf. pose proof (T3_walk x u Hwf) as Hwalk.
    destruct (F4_walk_path x u Hwf) as [Hlength Hmembers].
    pose proof (T4_compress (fst (walk x u)) (snd (walk x u)) u Hwf
      ltac:(intros y Hy; exact (proj1 (Hmembers y Hy)))) as Hcompress.
    pose proof (Nat.le_max_l (width u) (Pos.size_nat x)) as Hwidth.
    apply time_of_nat_le in Hlength. apply time_of_nat_le in Hwidth.
    time_unfold T_find. time_unfold @Datatypes.T_fst.
    time_unfold @Datatypes.T_snd.
    unfold k_walk, k_comp in *.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  Lemma T_find_le : forall x u, (wf u ->
    T_find x u <= c_uf * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof.
    intros x u Hwf. eapply N.le_trans; [exact (find_clock x u Hwf)|].
    apply N.mul_le_mono_r, N.mul_le_mono_r. unfold c_uf. lia.
  Qed.

  (** A read-only root lookup pays one walk, within the bound of find. *)
  Lemma T_root_of_le : forall x u, (wf u ->
    T_root_of x u <= c_uf * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof.
    intros x u Hwf. pose proof (T3_walk x u Hwf) as Hwalk.
    assert (Hunit : (1 <= N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N) by nia.
    time_unfold T_root_of. time_unfold @Datatypes.T_fst.
    unfold k_walk, c_uf in *. nia.
  Qed.

  Local Lemma add_clock_cap x u Q W :
    wf u -> card u <= Q -> Pos.size_nat x <= W ->
    (T_add x u <= 8192 *
      (N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1)))%N.
  Proof.
    intros Hwf Hcard Hwidth. pose proof (add_clock x u Hwf) as Hclock.
    pose proof (Nat.log2_le_mono _ _ Hcard) as Hlog.
    apply time_of_nat_le in Hwidth. apply time_of_nat_le in Hlog.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  Local Lemma find_clock_cap x u Q W :
    wf u -> card u <= Q -> width u <= W -> Pos.size_nat x <= W ->
    (T_find x u <= 32768 *
      (N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1)))%N.
  Proof.
    intros Hwf Hcard Hwidth Hx. eapply N.le_trans; [exact (find_clock x u Hwf)|].
    replace (32768 * (N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1)))%N
      with (32768 * N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1))%N by ring.
    apply N.mul_le_mono.
    - apply N.mul_le_mono_l, time_of_nat_le.
      pose proof (Nat.log2_le_mono _ _ Hcard). lia.
    - apply time_of_nat_le. pose proof (Nat.max_lub _ _ _ Hwidth Hx). lia.
  Qed.

  Local Lemma link_clock_cap w l u Q W :
    wf u -> mem u w -> mem u l -> card u <= Q -> width u <= W ->
    (T_link w l u <= 16384 *
      (N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1)))%N.
  Proof.
    intros Hwf Hw Hl Hcard Hwidth. pose proof (T5_link w l u Hwf Hw Hl) as Hclock.
    pose proof (Nat.log2_le_mono _ _ Hcard) as Hlog.
    apply time_of_nat_le in Hwidth. apply time_of_nat_le in Hlog.
    unfold k_link in Hclock.
    repeat rewrite Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  Lemma T_union_le : forall x y u, (wf u ->
    T_union x y u <= c_uf * N.of_nat (Nat.log2 (card u + 2) + 1) *
      N.of_nat (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1))%N.
  Proof.
    intros x y u Hwf.
    set (Q := card u + 2).
    set (W := Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y))).
    assert (HuW : width u <= W) by (unfold W; lia).
    assert (HxW : Pos.size_nat x <= W) by (unfold W; lia).
    assert (HyW : Pos.size_nat y <= W) by (unfold W; lia).
    pose proof (add_clock_cap x u Q W Hwf ltac:(unfold Q; lia) HxW) as Haddx.
    remember (add x u) as ua eqn:Ea.
    assert (Hwfa : wf ua) by (subst ua; apply wf_add; exact Hwf).
    assert (Hcarda : card ua <= card u + 1).
    { subst ua. apply card_add. exact Hwf. }
    assert (Hwa : width ua <= W).
    { subst ua. pose proof (width_add x u Hwf). lia. }
    pose proof (add_clock_cap y ua Q W Hwfa ltac:(unfold Q; lia) HyW) as Haddy.
    remember (add y ua) as ub eqn:Eb.
    assert (Hwfb : wf ub) by (subst ub; apply wf_add; exact Hwfa).
    assert (Hcardb : card ub <= Q).
    { subst ub. pose proof (card_add y ua Hwfa). unfold Q. lia. }
    assert (Hwb : width ub <= W).
    { subst ub. pose proof (width_add y ua Hwfa). lia. }
    assert (Hxb : mem ub x).
    { subst ub. apply (proj2 (mem_add y ua x Hwfa)). left.
      subst ua. apply (proj2 (mem_add x u x Hwf)). now right. }
    assert (Hyb : mem ub y).
    { subst ub. apply (proj2 (mem_add y ua y Hwfa)). now right. }
    pose proof (find_clock_cap x ub Q W Hwfb Hcardb Hwb HxW) as Hfindx.
    destruct (find x ub) as [rx uc] eqn:Ex.
    pose proof (wf_find x ub Hwfb) as Hwfc.
    pose proof (card_find x ub Hwfb) as Hcardc.
    pose proof (width_find x ub Hwfb) as Hwc.
    rewrite Ex in Hwfc, Hcardc, Hwc. cbn [snd] in Hwfc, Hcardc, Hwc.
    assert (Hyc : mem uc y).
    { pose proof (proj2 (mem_find x ub y Hwfb) Hyb) as H.
      rewrite Ex in H. exact H. }
    assert (Hrxc : mem uc rx).
    { pose proof (find_repr x ub Hwfb) as Hrepr. rewrite Ex in Hrepr. cbn [fst] in Hrepr.
      pose proof (repr_mem ub x Hwfb Hxb) as Hmem. rewrite <- Hrepr in Hmem.
      pose proof (proj2 (mem_find x ub rx Hwfb) Hmem) as H. rewrite Ex in H. exact H. }
    pose proof (find_clock_cap y uc Q W Hwfc ltac:(lia) ltac:(lia) HyW) as Hfindy.
    destruct (find y uc) as [ry ud] eqn:Ey.
    pose proof (wf_find y uc Hwfc) as Hwfd.
    pose proof (card_find y uc Hwfc) as Hcardd.
    pose proof (width_find y uc Hwfc) as Hwd.
    rewrite Ey in Hwfd, Hcardd, Hwd. cbn [snd] in Hwfd, Hcardd, Hwd.
    assert (Hrxd : mem ud rx).
    { pose proof (proj2 (mem_find y uc rx Hwfc) Hrxc) as H.
      rewrite Ey in H. exact H. }
    assert (Hryd : mem ud ry).
    { pose proof (find_repr y uc Hwfc) as Hrepr. rewrite Ey in Hrepr. cbn [fst] in Hrepr.
      pose proof (repr_mem uc y Hwfc Hyc) as Hmem. rewrite <- Hrepr in Hmem.
      pose proof (proj2 (mem_find y uc ry Hwfc) Hmem) as H. rewrite Ey in H. exact H. }
    assert (HrxW : Pos.size_nat rx <= W).
    { pose proof (width_mem ud rx Hwfd Hrxd). lia. }
    assert (HryW : Pos.size_nat ry <= W).
    { pose proof (width_mem ud ry Hwfd Hryd). lia. }
    pose proof (link_clock_cap rx ry ud Q W Hwfd Hrxd Hryd ltac:(lia) ltac:(lia)) as Hlinkxy.
    pose proof (link_clock_cap ry rx ud Q W Hwfd Hryd Hrxd ltac:(lia) ltac:(lia)) as Hlinkyx.
    assert (Hsizex : (T_size_at rx ud <= 2048 * N.of_nat (W + 1))%N).
    { eapply N.le_trans; [exact (size_at_clock rx ud)|]. unfold k_get.
      apply N.mul_le_mono_l, time_of_nat_le. lia. }
    assert (Hsizey : (T_size_at ry ud <= 2048 * N.of_nat (W + 1))%N).
    { eapply N.le_trans; [exact (size_at_clock ry ud)|]. unfold k_get.
      apply N.mul_le_mono_l, time_of_nat_le. lia. }
    pose proof (Pos.T_eqb_le rx ry) as Heq.
    pose proof (N.T_leb_le (size_at ry ud) (size_at rx ud)) as Hcompare.
    pose proof (size_at_width ud ry Hwfd) as Hbits.
    pose proof (Nat.log2_le_mono (card ud) Q ltac:(lia)) as Hlog.
    assert (HbitsQ : N.size_nat (size_at ry ud) <= Nat.log2 Q + 1) by lia.
    apply time_of_nat_le in HbitsQ. apply time_of_nat_le in HrxW.
    set (budget := (N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1))%N) in *.
    assert (HWbudget : (N.of_nat (W + 1) <= budget)%N).
    { unfold budget. repeat rewrite Nat2N.inj_add. cbn [N.of_nat]. nia. }
    assert (HLbudget : (N.of_nat (Nat.log2 Q + 1) <= budget)%N).
    { unfold budget. repeat rewrite Nat2N.inj_add. cbn [N.of_nat]. nia. }
    assert (Hbudget : (1 <= budget)%N).
    { pose proof (time_of_nat_le 1 (W + 1) ltac:(lia)). cbn [N.of_nat] in H. lia. }
    change (T_union x y u <= c_uf * N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1))%N.
    replace (c_uf * N.of_nat (Nat.log2 Q + 1) * N.of_nat (W + 1))%N
      with (c_uf * budget)%N by (unfold budget; ring).
    time_unfold T_union.
    rewrite <- Ea, <- Eb, Ex. cbn [fst snd]. rewrite Ey. cbn [fst snd].
    time_unfold @Datatypes.T_fst. time_unfold @Datatypes.T_snd.
    destruct (Pos.eqb rx ry); [|destruct (N.leb (size_at ry ud) (size_at rx ud))];
      unfold c_uf; repeat rewrite Nat2N.inj_add in *; cbn [N.of_nat] in *; lia.
  Qed.

  Lemma find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => N.of_nat ((Nat.log2 (card (snd xu)) + 1) *
      (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1)))
    (fun xu => T_find (fst xu) (snd xu)).
  Proof.
    exists c_uf. intros [x u] Hwf. cbn [fst snd] in *.
    pose proof (T_find_le x u Hwf) as Hfind.
    rewrite Nat2N.inj_mul. nia.
  Qed.
End UnionFindT.
