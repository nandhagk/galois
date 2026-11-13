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
  Lemma wf_add   : forall x u, wf u -> wf (add x u). Proof. Admitted. (* STUB *)
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

  (** ** End compression and find helpers *)

  Lemma wf_find  : forall x u, wf u -> wf (snd (find x u)). Proof. Admitted. (* STUB *)
  Lemma wf_union : forall x y u, wf u -> wf (snd (union x y u)). Proof. Admitted. (* STUB *)
  Lemma mem_add   : forall x u y, wf u -> (mem (add x u) y <-> mem u y \/ y = x).
  Proof.
    intros x u y Hwf. apply mem_add_raw.
  Qed.
  Lemma mem_find  : forall x u y, wf u -> (mem (snd (find x u)) y <-> mem u y). Proof. Admitted. (* STUB *)
  Lemma mem_union : forall x y u z, wf u -> (mem (snd (union x y u)) z <-> mem u z \/ z = x \/ z = y).
  Proof. Admitted. (* STUB *)
  Lemma repr_empty : forall x, repr empty x = x. Proof. reflexivity. Qed.
  Lemma repr_idem  : forall u x, wf u -> repr u (repr u x) = repr u x.
  Proof.
    intros u x Hwf. apply repr_of_root. apply repr_root. exact Hwf.
  Qed.
  Lemma repr_add   : forall x u y, wf u -> repr (add x u) y = repr u y. Proof. Admitted. (* STUB *)
  Lemma find_repr  : forall x u, wf u -> fst (find x u) = repr u x. Proof. Admitted. (* STUB *)
  Lemma find_same  : forall x u y, wf u -> repr (snd (find x u)) y = repr u y. Proof. Admitted. (* STUB *)
  Lemma union_none : forall x y u u1, wf u -> union x y u = (None, u1) ->
    repr u x = repr u y /\ forall z, repr u1 z = repr u z. Proof. Admitted. (* STUB *)
  Lemma union_some : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    repr u x <> repr u y /\
    ((w = repr u x /\ l = repr u y) \/ (w = repr u y /\ l = repr u x)) /\
    forall z, repr u1 z = if Pos.eqb (repr u z) l then w else repr u z. Proof. Admitted. (* STUB *)
  Lemma union_by_size : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u l <= size_of u w. Proof. Admitted. (* STUB *)
  Lemma size_of_union : forall x y u w l u1, wf u -> union x y u = (Some (w, l), u1) ->
    size_of u1 w = size_of u w + size_of u l. Proof. Admitted. (* STUB *)
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
  Lemma card_union : forall x y u, wf u -> card (snd (union x y u)) <= card u + 2. Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Lemma size_of_add : forall x u y, wf u -> size_of (add x u) y = size_of u y.
  Proof. Admitted. (* STUB *)
  Lemma size_of_find : forall x u y, wf u -> size_of (snd (find x u)) y = size_of u y.
  Proof. Admitted. (* STUB *)
  Lemma size_of_union_other : forall x y u o u1 z, wf u -> union x y u = (o, u1) ->
  (forall w l, o = Some (w, l) -> repr u z <> w /\ repr u z <> l) ->
  size_of u1 z = size_of u z.
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)
  Lemma width_union : forall x y u, wf u ->
  width (snd (union x y u)) <= Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)).
  Proof. Admitted. (* STUB *)
End UnionFind.

Module UnionFindT <: UNION_FIND_ALL.
  Include UnionFind.

  TimeFun add.
  TimeFun size_at.
  TimeFun link.
  TimeFun union.

  Definition c_uf : N := 1. (* STUB *)

  Definition k_get : N := 1. (* STUB *)
  Definition k_step : N := 1. (* STUB *)
  Definition k_walk : N := 1. (* STUB *)
  Definition k_comp : N := 1. (* STUB *)
  Definition k_link : N := 1. (* STUB *)

  Lemma T_add_le : forall x u, (wf u ->
    T_add x u <= c_uf * N.of_nat (Pos.size_nat x + Nat.log2 (card u) + 2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_find_le : forall x u, (wf u ->
    T_find x u <= c_uf * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_union_le : forall x y u, (wf u ->
    T_union x y u <= c_uf * N.of_nat (Nat.log2 (card u + 2) + 1) *
      N.of_nat (Nat.max (width u) (Nat.max (Pos.size_nat x) (Pos.size_nat y)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma find_bigO : bigO (fun xu : positive * t => wf (snd xu))
    (fun xu => N.of_nat ((Nat.log2 (card (snd xu)) + 1) *
      (Nat.max (width (snd xu)) (Pos.size_nat (fst xu)) + 1)))
    (fun xu => T_find (fst xu) (snd xu)).
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)
  Lemma F4_walk_path : forall x u, wf u ->
    length (snd (walk x u)) <= Nat.log2 (card u) /\
    forall y, In y (snd (walk x u)) -> mem u y /\ repr u y = repr u x.
  Proof. Admitted. (* STUB *)
  Lemma F5_compress : forall u rk r path, wf u -> ranked u rk -> is_root u r ->
    (forall y, In y path -> mem u y /\ repr u y = r /\ y <> r) ->
    ranked (compress r path u) rk.
  Proof. Admitted. (* STUB *)
  Lemma F6_link : forall u rk w l, wf u -> ranked u rk ->
    is_root u w -> is_root u l -> w <> l -> size_of u l <= size_of u w ->
    ranked (link w l u)
      (fun x => if Pos.eqb x w then Nat.max (rk w) (S (rk l)) else rk x).
  Proof. Admitted. (* PLAN-DEFECT: singleton member/root w=1, absent root l=2, rk 2=1 and other ranks 0 satisfy the premises; linking requires 4 <= 2. Root membership premises are missing. *)

  Lemma T1_parent_of : forall x u,
    (T_parent_of x u <= k_get * N.of_nat (Pos.size_nat x + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_walk_step : forall u s, (wf u -> mem u (fst s) ->
    T_walk_step u s <= k_step * N.of_nat (width u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_walk : forall x u, (wf u ->
    T_walk x u <= k_walk * N.of_nat (Nat.log2 (card u) + 1) *
      N.of_nat (Nat.max (width u) (Pos.size_nat x) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T4_compress : forall r path u, (wf u -> (forall y, In y path -> mem u y) ->
    T_compress r path u <= k_comp * N.of_nat (length path + 1) *
      N.of_nat (width u + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T5_link : forall w l u, (wf u -> mem u w -> mem u l ->
    T_link w l u <= k_link * N.of_nat (width u + Nat.log2 (card u) + 2))%N.
  Proof. Admitted. (* STUB *)
End UnionFindT.
