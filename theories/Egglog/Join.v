(** * Generic joins over live index prefixes

    Joins bind one variable at a time and probe every participating index.
    For example, two binary indexes can share their middle variable.
    Builds on: JoinSig and the index operations. *)

From Stdlib Require Import List PArith NArith Arith Sorting.Sorted Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Egglog Require Import ValueSig IndexSig Syntax JoinSig Index.

Import List.ListNotations.

(** Folding disjoint branches preserves the absence of duplicate results. *)
Lemma fold_left_nodup_disjoint {A B : Type} (f : list B -> A -> list B)
    (P : A -> B -> Prop) : forall cs acc,
  NoDup cs -> NoDup acc ->
  (forall x b, In x cs -> P x b -> ~ In b acc) ->
  (forall x y b, P x b -> P y b -> x = y) ->
  (forall x out b, In x cs -> In b (f out x) -> In b out \/ P x b) ->
  (forall x out, In x cs -> NoDup out ->
    (forall b, P x b -> ~ In b out) -> NoDup (f out x)) ->
  NoDup (fold_left f cs acc).
Proof.
  intros cs. induction cs as [| x cs IH]; intros acc Hcs Hacc Hdisjoint Hunique
    Hsound Hstep; cbn [fold_left]; [exact Hacc |].
  inversion Hcs as [| x' cs' Habsent Htail]; subst.
  apply IH.
  - exact Htail.
  - apply Hstep; [now left | exact Hacc |].
    intros b Hb. apply (Hdisjoint x b); [now left | exact Hb].
  - intros y b Hy Hbranch Hin.
    destruct (Hsound x acc b (or_introl eq_refl) Hin) as [Hprevious | Hcurrent].
    + exact (Hdisjoint y b (or_intror Hy) Hbranch Hprevious).
    + assert (Heq : x = y) by exact (Hunique x y b Hcurrent Hbranch).
      subst y. exact (Habsent Hy).
  - exact Hunique.
  - intros y out b Hy Hin. apply (Hsound y out b); [now right | exact Hin].
  - intros y out Hy Hout Hfresh. apply (Hstep y out);
      [now right | exact Hout | exact Hfresh].
Qed.

(** Each fold call pays its branch bound and one traversal step. *)
Lemma T_fold_left_sum_le {A B : Type} (f : A -> B -> A) (T_f : A -> B -> N)
    (cost : B -> N) : forall xs acc,
  (forall a b, In b xs -> (T_f a b <= cost b)%N) ->
  (List.T_fold_left f T_f xs acc <=
    N.of_nat (length xs + 1) + fold_right N.add 0 (map cost xs))%N.
Proof.
  intros xs. induction xs as [| x xs IH]; intros acc Hcost.
  - time_step fold_left.
  - pose proof (Hcost acc x (or_introl eq_refl)) as Hhead.
    assert (Htail : (List.T_fold_left f T_f xs (f acc x) <=
      N.of_nat (length xs + 1) + fold_right N.add 0 (map cost xs))%N).
    { apply IH. intros a b Hin. exact (Hcost a b (or_intror Hin)). }
    time_step fold_left.
Qed.

(** Branch lower bounds and traversal steps also give a lower bound for a fold. *)
Lemma T_fold_left_sum_ge {A B : Type} (f : A -> B -> A) (T_f : A -> B -> N)
    (cost : B -> N) : forall xs acc,
  (forall a b, In b xs -> (cost b <= T_f a b)%N) ->
  (N.of_nat (length xs + 1) + fold_right N.add 0 (map cost xs) <=
    List.T_fold_left f T_f xs acc)%N.
Proof.
  intros xs. induction xs as [| x xs IH]; intros acc Hcost.
  - time_step fold_left.
  - pose proof (Hcost acc x (or_introl eq_refl)) as Hhead.
    assert (Htail : (N.of_nat (length xs + 1) + fold_right N.add 0 (map cost xs) <=
      List.T_fold_left f T_f xs (f acc x))%N).
    { apply IH. intros a b Hin. exact (Hcost a b (or_intror Hin)). }
    time_step fold_left.
Qed.

(** Inspecting a Boolean list predicate always pays its first traversal call. *)
Lemma T_existsb_ge_one {A : Type} (p : A -> bool) (T_p : A -> N) : forall xs,
  (1 <= List.T_existsb p T_p xs)%N.
Proof.
  intros [| x xs]; time_step existsb.
Qed.

Module ListDef.
  TimeFun List.nth.

  (** Selecting a list position pays at most one call for each traversed cell. *)
  Lemma T_nth_le : forall (A : Type) n (xs : list A) d,
    (T_nth n xs d <= N.of_nat (n + 1))%N.
  Proof.
    intros A n. induction n as [|n IH]; intros [|x xs] d; time_step List.nth.
  Qed.
End ListDef.
Import ListDef.

(** Reversing a list pays at least one call for every element and the empty tail. *)
Lemma T_rev_ge {A : Type} : forall (xs : list A),
  (N.of_nat (length xs + 1) <= List.T_rev xs)%N.
Proof.
  intro xs. induction xs as [| x xs IH].
  - change (1 <= 1)%N. reflexivity.
  - change (N.of_nat (S (length xs) + 1) <=
      1 + (List.T_rev xs + Datatypes.T_app (rev xs) [x]))%N.
    rewrite Nat.add_succ_l, Nat2N.inj_succ. lia.
Qed.

(** A sum of fixed branch charges separates from the natural-number subtree work. *)
Lemma fold_sum_nat_affine {A : Type} : forall (xs : list A) (a k : N) (work : A -> nat),
  fold_right N.add 0%N (map (fun x => (a + k * N.of_nat (work x))%N) xs) =
    (a * N.of_nat (length xs) + k * N.of_nat (fold_right Nat.add 0%nat (map work xs)))%N.
Proof.
  intros xs a k work. induction xs as [| x xs IH]; cbn [map fold_right length].
  - now rewrite !N.mul_0_r.
  - rewrite IH, Nat2N.inj_succ, Nat2N.inj_add, N.mul_succ_r, N.mul_add_distr_l.
    lia.
Qed.

(** A fold pays the fixed per-child work and all surviving recursive work. *)
Lemma T_fold_left_work_ge {A B : Type} (f : A -> B -> A) (T_f : A -> B -> N)
    (step : nat) (work : B -> nat) : forall xs acc,
  (forall a b, In b xs -> (N.of_nat (step + work b) <= T_f a b)%N) ->
  (N.of_nat (step * length xs + fold_right Nat.add 0%nat (map work xs)) <=
    List.T_fold_left f T_f xs acc)%N.
Proof.
  intro xs. induction xs as [| x xs IH]; intros acc Hcost.
  - time_step fold_left.
  - pose proof (Hcost acc x (or_introl eq_refl)) as Hhead.
    assert (Htail : (N.of_nat
      (step * length xs + fold_right Nat.add 0%nat (map work xs)) <=
      List.T_fold_left f T_f xs (f acc x))%N).
    { apply IH. intros a b Hin. exact (Hcost a b (or_intror Hin)). }
    time_step fold_left.
Qed.

Module JoinCode (V : VALUE_OPS) (I : INDEX_OPS V) <: JOIN_OPS V I.
  Definition level_count (p : jplan) : nat :=
    let '(JPlan n _) := p in n.

  Definition columns (p : jplan) : list (list nat) :=
    let '(JPlan _ cs) := p in cs.

  (** The suffix is examined first so an equal degree selects the earlier position. *)
  Fixpoint choose_columns (cs : list (list nat)) (ixs : list I.t)
      (ns : list positive) (lvl pos : nat) : option (nat * N) :=
    match cs, ixs, ns with
    | lv :: rest, ix :: tail, n :: nodes =>
      let later := choose_columns rest tail nodes lvl (S pos) in
      if existsb (Nat.eqb lvl) lv then
        let d := I.degree ix n in
        match later with
        | None => Some (pos, d)
        | Some (j, e) => if N.leb d e then Some (pos, d) else Some (j, e)
        end
      else later
    | _, _, _ => None
    end.

  Definition choose_index (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) : option nat :=
    match choose_columns (columns p) ixs ns lvl 0 with
    | Some (j, _) => Some j
    | None => None
    end.

  (** Probes stop at the first missing child before examining later columns. *)
  Fixpoint advance_columns (cs : list (list nat)) (ixs : list I.t) (lvl : nat)
      (ns : list positive) (c : cell V.t) : option (list positive) :=
    match cs, ixs, ns with
    | [], [], [] => Some []
    | lv :: rest, ix :: tail, n :: nodes =>
      match (if existsb (Nat.eqb lvl) lv then I.child ix n c else Some n) with
      | None => None
      | Some m =>
        match advance_columns rest tail lvl nodes c with
        | Some ms => Some (m :: ms)
        | None => None
        end
      end
    | _, _, _ => None
    end.

  Definition advance_nodes (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) (c : cell V.t) : option (list positive) :=
    if Nat.leb (S lvl) (level_count p) then advance_columns (columns p) ixs lvl ns c
    else None.

  Fixpoint enumerate (fuel : nat) (p : jplan) (ixs : list I.t)
      (ns : list positive) (pre : list (cell V.t))
      (acc : list (list (cell V.t))) {struct fuel} : list (list (cell V.t)) :=
    match fuel with
    | 0 => rev pre :: acc
    | S rest =>
      let lvl := length pre in
      match choose_index p ixs lvl ns with
      | None => acc
      | Some j =>
        fold_left (fun out c =>
          match advance_nodes p ixs lvl ns c with
          | None => out
          | Some nodes => enumerate rest p ixs nodes (c :: pre) out
          end) (I.children (nth j ixs I.empty) (nth j ns 1%positive)) acc
      end
    end.

  Definition run (p : jplan) (ixs : list I.t) : list (list (cell V.t)) :=
    enumerate (level_count p) p ixs (map I.root ixs) [] [].
End JoinCode.

Module Join (V : VALUE) (I : INDEX V) <: JOIN V I.
  Include JoinCode V I.
  Include JOIN_SPEC V I.

  Definition nodes_ok (p : jplan) (ixs : list I.t) (lvl : nat)
      (pre : list (cell V.t)) (ns : list positive) : Prop :=
    wf_plan p ixs /\ length pre = lvl /\ lvl <= nvars p /\
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) (rev pre) = Some u /\
      I.node (snd lvix) n u) (combine (cols p) ixs) ns.

  Definition participants (p : jplan) (lvl : nat) : list nat :=
    filter (fun j => existsb (Nat.eqb lvl) (nth j (cols p) []))
      (seq 0 (length (cols p))).

  Module IF := IndexFacts V I.

  (** A missing pivot means that no aligned column contains the current level. *)
  Lemma choose_columns_none : forall cs ixs ns lvl pos,
    length cs = length ixs -> length cs = length ns ->
    choose_columns cs ixs ns lvl pos = None ->
    forall lv, In lv cs -> existsb (Nat.eqb lvl) lv = false.
  Proof.
    induction cs as [|head cs IH]; intros [|ix ixs] [|n ns] lvl pos Hix Hns Hnone lv Hin;
      cbn [length] in Hix, Hns; try discriminate; try contradiction.
    cbn [choose_columns] in Hnone.
    destruct (existsb (Nat.eqb lvl) head) eqn:Hhead.
    - destruct (choose_columns cs ixs ns lvl (S pos)) as [[j d]|];
        [destruct (N.leb (I.degree ix n) d)|]; discriminate.
    - destruct Hin as [<-|Hin].
      + exact Hhead.
      + eapply (IH ixs ns lvl (S pos)); [lia|lia|exact Hnone|exact Hin].
  Qed.

  (** A chosen pivot names an aligned participating column and its stored degree. *)
  Lemma choose_columns_member : forall cs ixs ns lvl pos j d,
    choose_columns cs ixs ns lvl pos = Some (j, d) ->
    exists k lv ix n,
      j = pos + k /\ nth_error cs k = Some lv /\ nth_error ixs k = Some ix /\
      nth_error ns k = Some n /\ existsb (Nat.eqb lvl) lv = true /\ d = I.degree ix n.
  Proof.
    induction cs as [|head cs IH]; intros [|ix ixs] [|n ns] lvl pos j d Hchoose;
      cbn [choose_columns] in Hchoose; try discriminate.
    destruct (choose_columns cs ixs ns lvl (S pos)) as [[later degree]|] eqn:Hlater.
    - destruct (existsb (Nat.eqb lvl) head) eqn:Hhead.
      + destruct (N.leb (I.degree ix n) degree).
        * injection Hchoose as <- <-.
          exists 0, head, ix, n. cbn. repeat split; auto; lia.
        * injection Hchoose as <- <-.
          destruct (IH _ _ _ _ _ _ Hlater) as [k [lv [ix' [n' H]]]].
          exists (S k), lv, ix', n'. cbn. intuition lia.
      + injection Hchoose as <- <-.
        destruct (IH _ _ _ _ _ _ Hlater) as [k [lv [ix' [n' H]]]].
        exists (S k), lv, ix', n'. cbn. intuition lia.
    - destruct (existsb (Nat.eqb lvl) head) eqn:Hhead; [|discriminate].
      injection Hchoose as <- <-.
      exists 0, head, ix, n. cbn. repeat split; auto; lia.
  Qed.

  (** Every aligned participant has at least the selected degree, with stable ties. *)
  Lemma choose_columns_minimal : forall cs ixs ns lvl pos j d,
    length cs = length ixs -> length cs = length ns ->
    choose_columns cs ixs ns lvl pos = Some (j, d) ->
    forall k lv ix n, nth_error cs k = Some lv -> nth_error ixs k = Some ix ->
      nth_error ns k = Some n -> existsb (Nat.eqb lvl) lv = true ->
      (d <= I.degree ix n)%N /\ (d = I.degree ix n -> j <= pos + k).
  Proof.
    induction cs as [|head cs IH]; intros [|ix ixs] [|n ns] lvl pos j d Hix Hns Hchoose;
      cbn [length] in Hix, Hns; cbn [choose_columns] in Hchoose; try discriminate.
    destruct (choose_columns cs ixs ns lvl (S pos)) as [[later degree]|] eqn:Hlater.
    - destruct (existsb (Nat.eqb lvl) head) eqn:Hhead.
      + destruct (N.leb (I.degree ix n) degree) eqn:Hdegree.
        * injection Hchoose as <- <-. apply N.leb_le in Hdegree.
          intros [|k] lv ix' n' Hlv Hix' Hn' Hpart.
          -- cbn in Hlv, Hix', Hn'. injection Hlv as <-.
             injection Hix' as <-. injection Hn' as <-. split; [lia|lia].
          -- cbn in Hlv, Hix', Hn'.
             destruct (IH ixs ns lvl (S pos) later degree ltac:(lia) ltac:(lia) Hlater
               k lv ix' n' Hlv Hix' Hn' Hpart) as [Hmin _].
             split; [lia|lia].
        * injection Hchoose as <- <-. apply N.leb_gt in Hdegree.
          intros [|k] lv ix' n' Hlv Hix' Hn' Hpart.
          -- cbn in Hlv, Hix', Hn'. injection Hlv as <-.
             injection Hix' as <-. injection Hn' as <-. split; [lia|lia].
          -- cbn in Hlv, Hix', Hn'.
             destruct (IH ixs ns lvl (S pos) later degree ltac:(lia) ltac:(lia) Hlater
               k lv ix' n' Hlv Hix' Hn' Hpart) as [Hmin Htie].
             split; [exact Hmin|intro Heq; specialize (Htie Heq); lia].
      + injection Hchoose as <- <-.
        intros [|k] lv ix' n' Hlv Hix' Hn' Hpart.
        * cbn in Hlv. injection Hlv as <-. congruence.
        * cbn in Hlv, Hix', Hn'.
          destruct (IH ixs ns lvl (S pos) later degree ltac:(lia) ltac:(lia) Hlater
            k lv ix' n' Hlv Hix' Hn' Hpart) as [Hmin Htie].
          split; [exact Hmin|intro Heq; specialize (Htie Heq); lia].
    - destruct (existsb (Nat.eqb lvl) head) eqn:Hhead; [|discriminate].
      injection Hchoose as <- <-.
      intros [|k] lv ix' n' Hlv Hix' Hn' Hpart.
      + cbn in Hlv, Hix', Hn'. injection Hlv as <-.
        injection Hix' as <-. injection Hn' as <-. split; [lia|lia].
      + cbn in Hlv.
        pose proof (choose_columns_none cs ixs ns lvl (S pos) ltac:(lia) ltac:(lia)
          Hlater lv (nth_error_In _ _ Hlv)) as Hnone. congruence.
  Qed.

  (** The column, index and node lists stay aligned at every represented prefix. *)
  Lemma nodes_ok_lengths : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    length (cols p) = length ixs /\ length (cols p) = length ns.
  Proof.
    intros p ixs lvl pre ns [[Hix _] [_ [_ Hnodes]]].
    apply Forall2_length in Hnodes.
    rewrite length_combine, Hix, Nat.min_id in Hnodes. split; lia.
  Qed.

  (** The chosen index is a participant of minimum degree, with position breaking ties. *)
  Lemma choose_index_min : forall p ixs lvl pre ns j, nodes_ok p ixs lvl pre ns ->
    choose_index p ixs lvl ns = Some j ->
    In j (participants p lvl) /\ forall k, In k (participants p lvl) ->
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) <=
       I.degree (nth k ixs I.empty) (nth k ns 1%positive))%N /\
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) =
       I.degree (nth k ixs I.empty) (nth k ns 1%positive) -> j <= k).
  Proof.
    intros p ixs lvl pre ns j Hnodes Hchoose.
    destruct (nodes_ok_lengths _ _ _ _ _ Hnodes) as [Hix Hns].
    unfold choose_index in Hchoose.
    destruct (choose_columns (columns p) ixs ns lvl 0) as [[selected d]|] eqn:Hselected;
      [|discriminate].
    injection Hchoose as <-.
    destruct (choose_columns_member _ _ _ _ _ _ _ Hselected)
      as [k [lv [ix [n [Hpos [Hlv [Hread_ix [Hread_n [Hpart Hd]]]]]]]]].
    cbn in Hpos. subst k.
    change (nth_error (cols p) selected = Some lv) in Hlv.
    assert (Hbound : selected < length (cols p)).
    { apply nth_error_Some. rewrite Hlv. discriminate. }
    assert (Hix_value : nth selected ixs I.empty = ix).
    { eapply nth_error_nth. exact Hread_ix. }
    assert (Hn_value : nth selected ns 1%positive = n).
    { eapply nth_error_nth. exact Hread_n. }
    split.
    - apply filter_In. split; [apply in_seq; lia|].
      erewrite nth_error_nth; [exact Hpart|exact Hlv].
    - intros k Hk. apply filter_In in Hk as [Hrange Hpartk]. apply in_seq in Hrange.
      pose proof (choose_columns_minimal (columns p) ixs ns lvl 0 selected d Hix Hns
        Hselected k (nth k (cols p) []) (nth k ixs I.empty) (nth k ns 1%positive)
        (@nth_error_nth' (list nat) (cols p) k [] ltac:(lia))
        (@nth_error_nth' I.t ixs k I.empty ltac:(lia))
        (@nth_error_nth' positive ns k 1%positive ltac:(lia)) Hpartk) as Hmin.
      rewrite Hix_value, Hn_value, <- Hd. exact Hmin.
  Qed.

  (** Coverage supplies at least one participant before all variables have been bound. *)
  Lemma choose_index_some : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    lvl < nvars p -> exists j, choose_index p ixs lvl ns = Some j.
  Proof.
    intros p ixs lvl pre ns Hnodes Hlevel.
    destruct (nodes_ok_lengths _ _ _ _ _ Hnodes) as [Hix Hns].
    destruct Hnodes as [[_ [_ Hcover]] _].
    destruct (Hcover lvl Hlevel) as [lv [Hlv Hin]].
    unfold choose_index.
    destruct (choose_columns (columns p) ixs ns lvl 0) as [[j d]|] eqn:Hchoose.
    - exists j. reflexivity.
    - pose proof (choose_columns_none _ _ _ _ _ Hix Hns Hchoose lv Hlv) as Hnone.
      assert (Hpart : existsb (Nat.eqb lvl) lv = true).
      { apply existsb_exists. exists lvl. split; [exact Hin|apply Nat.eqb_refl]. }
      congruence.
  Qed.

  (** No variable position precedes level zero. *)
  Lemma filter_before_zero : forall lv, filter (fun i => Nat.ltb i 0) lv = [].
  Proof.
    induction lv as [|i lv IH]; cbn [filter Nat.ltb Nat.leb]; assumption || reflexivity.
  Qed.

  (** Root nodes represent empty projections in every aligned well-formed index. *)
  Lemma roots_nodes : forall cs ixs,
    Forall2 (fun lv ix => I.wf (length lv) ix) cs ixs ->
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i 0) (fst lvix)) [] = Some u /\
      I.node (snd lvix) n u) (combine cs ixs) (map I.root ixs).
  Proof.
    intros cs ixs Hcols. induction Hcols as [|lv ix cs ixs Hwf Hcols IH].
    - constructor.
    - cbn [combine map]. constructor; [|exact IH].
      exists []. split.
      + cbn [fst]. rewrite filter_before_zero. reflexivity.
      + cbn [snd]. apply I.node_root with (a := length lv). exact Hwf.
  Qed.

  (** Every well-formed plan starts with its indexes at the empty prefix. *)
  Lemma nodes_ok_initial : forall p ixs, wf_plan p ixs ->
    nodes_ok p ixs 0 [] (map I.root ixs).
  Proof.
    intros p ixs Hwf. split; [exact Hwf|]. split; [reflexivity|]. split; [lia|].
    apply roots_nodes. destruct Hwf as [_ [Hcols _]].
    induction Hcols as [|lv ix cs ixs Hwf Hcols IH]; constructor; [tauto|exact IH].
  Qed.

  (** Projection reads the selected head before the remaining positions. *)
  Lemma project_cons : forall i lv b,
    project (i :: lv) b =
      match nth_error b i, project lv b with
      | Some c, Some cs => Some (c :: cs)
      | _, _ => None
      end.
  Proof.
    reflexivity.
  Qed.

  (** Successful projection returns one cell for each selected position. *)
  Lemma project_length : forall lv b u, project lv b = Some u -> length u = length lv.
  Proof.
    induction lv as [|i lv IH]; intros b u Hproject.
    - injection Hproject as <-. reflexivity.
    - rewrite project_cons in Hproject.
      destruct (nth_error b i), (project lv b) as [tail|] eqn:Htail; try discriminate.
      injection Hproject as <-. cbn [length]. f_equal. eapply IH. exact Htail.
  Qed.

  (** Concatenating column lists concatenates their successful projections. *)
  Lemma project_append : forall lv rest b,
    project (lv ++ rest) b =
      match project lv b, project rest b with
      | Some u, Some v => Some (u ++ v)
      | _, _ => None
      end.
  Proof.
    induction lv as [|i lv IH]; intros rest b.
    - cbn [app]. destruct (project rest b); reflexivity.
    - cbn [app]. rewrite !project_cons, IH.
      destruct (nth_error b i), (project lv b), (project rest b); reflexivity.
  Qed.

  (** Equal reads on the selected positions give equal projections. *)
  Lemma project_ext : forall lv b d,
    (forall i, In i lv -> nth_error b i = nth_error d i) -> project lv b = project lv d.
  Proof.
    induction lv as [|i lv IH]; intros b d Hread; [reflexivity|].
    rewrite !project_cons, (Hread i (or_introl eq_refl)).
    rewrite (IH b d); [reflexivity|]. intros j Hj. apply Hread. right. exact Hj.
  Qed.

  (** Taking an assignment prefix preserves every selected position below its length. *)
  Lemma project_firstn : forall lv b lvl, Forall (fun i => i < lvl) lv ->
    project lv (firstn lvl b) = project lv b.
  Proof.
    intros lv b lvl Hrange. apply project_ext. intros i Hi.
    rewrite nth_error_firstn. apply Forall_forall with (x := i) in Hrange; [|exact Hi].
    assert (Hlt : Nat.ltb i lvl = true) by (apply Nat.ltb_lt; exact Hrange).
    now rewrite Hlt.
  Qed.

  (** Appending cells leaves all existing selected positions unchanged. *)
  Lemma project_extend : forall lv b d, Forall (fun i => i < length b) lv ->
    project lv (b ++ d) = project lv b.
  Proof.
    intros lv b d Hrange. apply project_ext. intros i Hi.
    rewrite nth_error_app1; [reflexivity|]. rewrite Forall_forall in Hrange.
    exact (Hrange i Hi).
  Qed.

  (** A suffix strictly after a level contributes neither a prefix cell nor a participant. *)
  Lemma later_columns : forall lv lvl, Forall (fun i => lvl < i) lv ->
    filter (fun i => Nat.ltb i lvl) lv = [] /\
    filter (fun i => Nat.ltb i (S lvl)) lv = [] /\
    existsb (Nat.eqb lvl) lv = false.
  Proof.
    intros lv lvl Hrange. induction Hrange as [|i lv Hlt Hrange [IHlow [IHnext IHeq]]].
    - repeat split; reflexivity.
    - assert (Hlow : Nat.ltb i lvl = false) by (apply Nat.ltb_ge; lia).
      assert (Hnext : Nat.ltb i (S lvl) = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb lvl i = false) by (apply Nat.eqb_neq; lia).
      cbn [filter existsb]. rewrite Hlow, Hnext, Heq, IHlow, IHnext, IHeq.
      repeat split; reflexivity.
  Qed.

  (** Increasing columns add the current level at the end of their bound prefix. *)
  Lemma filter_level_succ : forall lv, StronglySorted lt lv -> forall lvl,
    filter (fun i => Nat.ltb i (S lvl)) lv =
      filter (fun i => Nat.ltb i lvl) lv ++
        if existsb (Nat.eqb lvl) lv then [lvl] else [].
  Proof.
    intros lv Hsorted. induction Hsorted as [|i lv Hsorted IH Hafter]; intro lvl.
    - reflexivity.
    - destruct (Nat.lt_trichotomy i lvl) as [Hlt|[Heq|Hgt]].
      + assert (Hlow : Nat.ltb i lvl = true) by (apply Nat.ltb_lt; lia).
        assert (Hnext : Nat.ltb i (S lvl) = true) by (apply Nat.ltb_lt; lia).
        assert (Heq : Nat.eqb lvl i = false) by (apply Nat.eqb_neq; lia).
        cbn [filter existsb]. rewrite Hlow, Hnext, Heq, IH. reflexivity.
      + subst i. destruct (later_columns lv lvl Hafter) as [Hlow [Hnext Heq]].
        assert (Hsucc : Nat.ltb lvl (S lvl) = true) by (apply Nat.ltb_lt; lia).
        cbn [filter existsb]. rewrite Nat.ltb_irrefl, Nat.eqb_refl, Hsucc, Hlow, Hnext.
        reflexivity.
      + assert (Hlater : Forall (fun j => lvl < j) (i :: lv)).
        { constructor; [exact Hgt|]. eapply Forall_impl; [|exact Hafter]. intros j Hj. lia. }
        destruct (later_columns _ _ Hlater) as [Hlow [Hnext Heq]].
        rewrite Hlow, Hnext, Heq. reflexivity.
  Qed.

  (** Extending the assignment appends its cell exactly in participating columns. *)
  Lemma project_next : forall lv lvl b c u, StronglySorted lt lv -> length b = lvl ->
    project (filter (fun i => Nat.ltb i lvl) lv) b = Some u ->
    project (filter (fun i => Nat.ltb i (S lvl)) lv) (b ++ [c]) =
      Some (if existsb (Nat.eqb lvl) lv then u ++ [c] else u).
  Proof.
    intros lv lvl b c u Hsorted Hlength Hproject.
    rewrite filter_level_succ by exact Hsorted. rewrite project_append.
    rewrite project_extend.
    - rewrite Hproject. destruct (existsb (Nat.eqb lvl) lv).
      + rewrite project_cons, nth_error_app2 by lia.
        rewrite Hlength, Nat.sub_diag. reflexivity.
      + change (Some (u ++ []) = Some u). now rewrite app_nil_r.
    - apply Forall_forall. intros i Hi. apply filter_In in Hi as [_ Hlt].
      apply Nat.ltb_lt in Hlt. lia.
  Qed.

  (** Each plan column is increasing and has an index of the matching arity. *)
  Lemma plan_columns_wf : forall p ixs, wf_plan p ixs ->
    Forall2 (fun lv ix => StronglySorted lt lv /\ I.wf (length lv) ix) (cols p) ixs.
  Proof.
    intros p ixs [_ [Hcols _]].
    induction Hcols as [|lv ix cs ixs Hwf Hcols IH]; constructor; [tauto|exact IH].
  Qed.

  (** Successful column probes preserve the represented projections of the extended prefix. *)
  Lemma advance_columns_preserves : forall cs ixs lvl ns c ns' b,
    length b = lvl ->
    Forall2 (fun lv ix => StronglySorted lt lv /\ I.wf (length lv) ix) cs ixs ->
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) b = Some u /\
      I.node (snd lvix) n u) (combine cs ixs) ns ->
    advance_columns cs ixs lvl ns c = Some ns' ->
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i (S lvl)) (fst lvix)) (b ++ [c]) = Some u /\
      I.node (snd lvix) n u) (combine cs ixs) ns'.
  Proof.
    intros cs ixs lvl ns c ns' b Hlength Hcols. revert ns ns'.
    induction Hcols as [|lv ix cs ixs [Hsorted Hwf] Hcols IH];
      intros [|n ns] ns' Hnodes Hstep; cbn [advance_columns] in Hstep; try discriminate.
    - injection Hstep as <-. constructor.
    - apply Forall2_cons_iff in Hnodes as [[u [Hproject Hnode]] Hnodes].
      cbn [fst snd] in Hproject, Hnode.
      destruct (if existsb (Nat.eqb lvl) lv then I.child ix n c else Some n)
        as [m|] eqn:Hhead;
        destruct (advance_columns cs ixs lvl ns c) as [ms|] eqn:Htail; try discriminate.
      injection Hstep as <-. cbn [combine]. constructor.
      + exists (if existsb (Nat.eqb lvl) lv then u ++ [c] else u). split.
        * cbn [fst]. apply project_next; assumption.
        * cbn [snd]. destruct (existsb (Nat.eqb lvl) lv) eqn:Hpart.
          -- apply (proj1 (proj1 (I.child_spec (length lv) ix n u c Hwf Hnode) m)).
             exact Hhead.
          -- injection Hhead as <-. exact Hnode.
      + exact (IH ns ms Hnodes Htail).
  Qed.

  (** A successful full probe advances a represented assignment by one variable. *)
  Lemma advance_nodes_ok : forall p ixs lvl pre ns c ns', nodes_ok p ixs lvl pre ns ->
    advance_nodes p ixs lvl ns c = Some ns' ->
    nodes_ok p ixs (S lvl) (c :: pre) ns'.
  Proof.
    intros p ixs lvl pre ns c ns' [Hwf [Hlength [Hlevel Hnodes]]] Hstep.
    unfold advance_nodes in Hstep.
    destruct (Nat.leb (S lvl) (level_count p)) eqn:Hbound; [|discriminate].
    apply Nat.leb_le in Hbound. change (S lvl <= nvars p) in Hbound.
    split; [exact Hwf|]. split; [cbn [length]; lia|]. split; [exact Hbound|].
    change (Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i (S lvl)) (fst lvix))
        (rev pre ++ [c]) = Some u /\ I.node (snd lvix) n u)
      (combine (cols p) ixs) ns').
    eapply advance_columns_preserves.
    - rewrite length_rev. exact Hlength.
    - apply plan_columns_wf. exact Hwf.
    - exact Hnodes.
    - exact Hstep.
  Qed.

  (** Positions before a level form an initial segment of an increasing column. *)
  Lemma filter_before_prefix : forall lv, StronglySorted lt lv -> forall lvl,
    exists rest, lv = filter (fun i => Nat.ltb i lvl) lv ++ rest.
  Proof.
    intros lv Hsorted. induction Hsorted as [|i lv Hsorted IH Hafter]; intro lvl.
    - exists []. reflexivity.
    - destruct (Nat.ltb i lvl) eqn:Hlow.
      + destruct (IH lvl) as [rest Hrest]. exists rest.
        cbn [filter]. rewrite Hlow. cbn [app]. now rewrite <- Hrest.
      + apply Nat.ltb_ge in Hlow.
        assert (Hlater : Forall (fun j => lvl < j) lv).
        { eapply Forall_impl; [|exact Hafter]. intros j Hj. lia. }
        destruct (later_columns lv lvl Hlater) as [Htail _].
        exists (i :: lv). cbn [filter].
        assert (Hfalse : Nat.ltb i lvl = false) by (apply Nat.ltb_ge; exact Hlow).
        now rewrite Hfalse, Htail.
  Qed.

  (** A projected column prefix is an initial segment of its full projection. *)
  Lemma project_prefix : forall lv b lvl full pre, StronglySorted lt lv ->
    project lv b = Some full ->
    project (filter (fun i => Nat.ltb i lvl) lv) b = Some pre ->
    exists suf, full = pre ++ suf.
  Proof.
    intros lv b lvl full pre Hsorted Hfull Hpre.
    destruct (filter_before_prefix lv Hsorted lvl) as [rest Hrest].
    rewrite Hrest, project_append, Hpre in Hfull.
    destruct (project rest b) as [suf|]; [|discriminate].
    injection Hfull as <-. exists suf. reflexivity.
  Qed.

  (** Filtering to a level leaves only positions inside that prefix. *)
  Lemma filter_positions : forall lv lvl,
    Forall (fun i => i < lvl) (filter (fun i => Nat.ltb i lvl) lv).
  Proof.
    intros lv lvl. apply Forall_forall. intros i Hi.
    apply filter_In in Hi as [_ Hlt]. now apply Nat.ltb_lt in Hlt.
  Qed.

  (** A participating column in a full answer extends its current projection by the next cell. *)
  Lemma project_next_answer : forall lv lvl b c u full v, StronglySorted lt lv ->
    length b = lvl -> project (filter (fun i => Nat.ltb i lvl) lv) b = Some u ->
    existsb (Nat.eqb lvl) lv = true -> firstn (S lvl) full = b ++ [c] ->
    project lv full = Some v -> exists suf, v = u ++ c :: suf.
  Proof.
    intros lv lvl b c u full v Hsorted Hlength Hproject Hpart Hprefix Hfull.
    pose proof (project_next lv lvl b c u Hsorted Hlength Hproject) as Hnext.
    rewrite Hpart in Hnext.
    assert (Hproject_full :
      project (filter (fun i => Nat.ltb i (S lvl)) lv) full = Some (u ++ [c])).
    { rewrite <- (project_firstn _ full (S lvl) (filter_positions lv (S lvl))).
      now rewrite Hprefix. }
    destruct (project_prefix lv full (S lvl) v (u ++ [c]) Hsorted Hfull Hproject_full)
      as [suf Hsuf].
    exists suf. rewrite Hsuf, <- app_assoc. reflexivity.
  Qed.

  (** Every column probe succeeds for a cell belonging to a full extending answer. *)
  Lemma advance_columns_complete : forall cs ixs lvl ns c b full,
    length b = lvl ->
    Forall2 (fun lv ix => StronglySorted lt lv /\ I.wf (length lv) ix) cs ixs ->
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) b = Some u /\
      I.node (snd lvix) n u) (combine cs ixs) ns ->
    Forall2 (fun lv ix => exists u, project lv full = Some u /\ I.mem ix u) cs ixs ->
    firstn (S lvl) full = b ++ [c] ->
    exists ns', advance_columns cs ixs lvl ns c = Some ns'.
  Proof.
    intros cs ixs lvl ns c b full Hlength Hcols. revert ns.
    induction Hcols as [|lv ix cs ixs [Hsorted Hwf] Hcols IH];
      intros [|n ns] Hnodes Hanswer Hprefix.
    - exists []. reflexivity.
    - inversion Hnodes.
    - inversion Hnodes.
    - apply Forall2_cons_iff in Hnodes as [[u [Hproject Hnode]] Hnodes].
      apply Forall2_cons_iff in Hanswer as [[v [Hfull Hmem]] Hanswer].
      cbn [fst snd] in Hproject, Hnode.
      destruct (IH ns Hnodes Hanswer Hprefix) as [ms Htail].
      cbn [advance_columns]. rewrite Htail.
      destruct (existsb (Nat.eqb lvl) lv) eqn:Hpart.
      + destruct (project_next_answer lv lvl b c u full v Hsorted Hlength Hproject
          Hpart Hprefix Hfull) as [suf Hsuf].
        rewrite Hsuf in Hmem.
        destruct (IF.child_of_member (length lv) ix n u c suf Hwf Hnode Hmem)
          as [m Hchild].
        rewrite Hchild. exists (m :: ms). reflexivity.
      + exists (n :: ms). reflexivity.
  Qed.

  (** An answer extending the next cell supplies a successful full probe. *)
  Lemma advance_nodes_complete : forall p ixs lvl pre ns c full,
    nodes_ok p ixs lvl pre ns -> answer p ixs full ->
    firstn (S lvl) full = rev (c :: pre) ->
    exists ns', advance_nodes p ixs lvl ns c = Some ns'.
  Proof.
    intros p ixs lvl pre ns c full [Hwf [Hlength [Hlevel Hnodes]]]
      [Hfull_length Hanswer] Hprefix.
    assert (Hbound : S lvl <= nvars p).
    { apply (f_equal (@length (cell V.t))) in Hprefix.
      rewrite length_firstn, length_rev in Hprefix. cbn [length] in Hprefix. lia. }
    unfold advance_nodes.
    assert (Hguard : Nat.leb (S lvl) (level_count p) = true).
    { apply Nat.leb_le. exact Hbound. }
    rewrite Hguard.
    eapply advance_columns_complete.
    - rewrite length_rev. exact Hlength.
    - apply plan_columns_wf. exact Hwf.
    - exact Hnodes.
    - exact Hanswer.
    - exact Hprefix.
  Qed.

  (** Filtering keeps an entire column once every one of its positions is bound. *)
  Lemma filter_all_bound : forall lv lvl, Forall (fun i => i < lvl) lv ->
    filter (fun i => Nat.ltb i lvl) lv = lv.
  Proof.
    intros lv lvl Hrange. induction Hrange as [|i lv Hlt Hrange IH]; [reflexivity|].
    assert (Hbound : Nat.ltb i lvl = true) by (apply Nat.ltb_lt; exact Hlt).
    cbn [filter]. now rewrite Hbound, IH.
  Qed.

  (** Full represented projections are members of their nonempty-arity indexes. *)
  Lemma completed_columns_answer : forall lvl cs ixs ns b,
    Forall2 (fun lv ix => lv <> [] /\ StronglySorted lt lv /\
      Forall (fun i => i < lvl) lv /\ I.wf (length lv) ix) cs ixs ->
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) b = Some u /\
      I.node (snd lvix) n u) (combine cs ixs) ns ->
    Forall2 (fun lv ix => exists u, project lv b = Some u /\ I.mem ix u) cs ixs.
  Proof.
    intros lvl cs ixs ns b Hcols. revert ns.
    induction Hcols as [|lv ix cs ixs [Hnonempty [Hsorted [Hrange Hwf]]] Hcols IH];
      intros [|n ns] Hnodes.
    - constructor.
    - inversion Hnodes.
    - inversion Hnodes.
    - apply Forall2_cons_iff in Hnodes as [[u [Hproject Hnode]] Hnodes].
      cbn [fst snd] in Hproject, Hnode.
      rewrite filter_all_bound in Hproject by exact Hrange.
      constructor; [|exact (IH ns Hnodes)]. exists u. split; [exact Hproject|].
      eapply IF.node_full_mem; [exact Hwf|exact Hnode| |].
      + eapply project_length. exact Hproject.
      + intro Hu. apply Hnonempty. apply length_zero_iff_nil.
        pose proof (project_length _ _ _ Hproject) as Hlength. rewrite Hu in Hlength.
        cbn [length] in Hlength. lia.
  Qed.

  (** A represented complete assignment satisfies every input index. *)
  Lemma nodes_ok_answer : forall p ixs pre ns,
    nodes_ok p ixs (nvars p) pre ns -> answer p ixs (rev pre).
  Proof.
    intros p ixs pre ns [[_ [Hcols _]] [Hlength [_ Hnodes]]].
    split; [now rewrite length_rev|]. eapply completed_columns_answer; eassumption.
  Qed.

  (** Forgetting the next cell recovers the preceding assignment prefix. *)
  Lemma prefix_before_next : forall lvl (pre : list (cell V.t)) c b, length pre = lvl ->
    firstn (S lvl) b = rev (c :: pre) -> firstn lvl b = rev pre.
  Proof.
    intros lvl pre c b Hlength Hprefix.
    apply (f_equal (firstn lvl)) in Hprefix.
    rewrite firstn_firstn, Nat.min_l in Hprefix by lia.
    cbn [rev] in Hprefix.
    rewrite firstn_app, length_rev, Hlength, Nat.sub_diag in Hprefix.
    cbn [firstn] in Hprefix. rewrite app_nil_r in Hprefix.
    rewrite (@firstn_all2 (cell V.t) lvl (rev pre)) in Hprefix by (rewrite length_rev; lia).
    exact Hprefix.
  Qed.

  (** A left fold emits only existing accumulator elements or elements justified by a step. *)
  Lemma fold_left_sound : forall (A B : Type) (f : list B -> A -> list B)
      (P : B -> Prop) cs acc,
    (forall x out b, In x cs -> In b (f out x) -> In b out \/ P b) ->
    forall b, In b (fold_left f cs acc) -> In b acc \/ P b.
  Proof.
    intros A B f P cs. induction cs as [|x cs IH]; intros acc Hstep b Hin.
    - left. exact Hin.
    - cbn [fold_left] in Hin.
      destruct (IH (f acc x) (fun y out d Hy => Hstep y out d (or_intror Hy)) b Hin)
        as [Hhead|Hnew]; [|right; exact Hnew].
      exact (Hstep x acc b (or_introl eq_refl) Hhead).
  Qed.

  (** Enumeration preserves the incoming accumulator and justifies every new assignment. *)
  Lemma enumerate_sound : forall fuel p ixs lvl pre ns acc b,
    fuel + lvl = nvars p -> nodes_ok p ixs lvl pre ns ->
    In b (enumerate fuel p ixs ns pre acc) ->
    In b acc \/ (answer p ixs b /\ firstn lvl b = rev pre).
  Proof.
    induction fuel as [|fuel IH]; intros p ixs lvl pre ns acc b Hfuel Hnodes Hin.
    - cbn [enumerate] in Hin. destruct Hin as [<-|Hin]; [right|left; exact Hin].
      assert (Hlevel : lvl = nvars p) by lia. subst lvl.
      split; [eapply nodes_ok_answer; exact Hnodes|].
      apply firstn_all2. rewrite length_rev. pose proof (proj1 (proj2 Hnodes)). lia.
    - pose proof (proj1 (proj2 Hnodes)) as Hlength.
      cbn [enumerate] in Hin. rewrite Hlength in Hin.
      destruct (choose_index p ixs lvl ns) as [j|] eqn:Hchoose; [|left; exact Hin].
      eapply (@fold_left_sound (cell V.t) (list (cell V.t)) _
        (fun d => answer p ixs d /\ firstn lvl d = rev pre) _ acc); [|exact Hin].
      intros c out d _ Hbody. cbn beta in Hbody.
      destruct (advance_nodes p ixs lvl ns c) as [nodes|] eqn:Hstep;
        [|left; exact Hbody].
      pose proof (advance_nodes_ok p ixs lvl pre ns c nodes Hnodes Hstep) as Hnext.
      destruct (IH p ixs (S lvl) (c :: pre) nodes out d ltac:(lia) Hnext Hbody)
        as [Hacc|[Hanswer Hprefix]]; [left; exact Hacc|].
      right. split; [exact Hanswer|]. eapply prefix_before_next; eassumption.
  Qed.

  (** Reading aligned lists preserves both their column relation and their node relation. *)
  Lemma aligned_nth : forall (A B C : Type) (P : A -> B -> Prop)
      (Q : A * B -> C -> Prop) cs ixs ns da db dc,
    Forall2 P cs ixs -> Forall2 Q (combine cs ixs) ns ->
    forall j, j < length cs ->
    P (nth j cs da) (nth j ixs db) /\
    Q (nth j cs da, nth j ixs db) (nth j ns dc).
  Proof.
    intros A B C P Q cs ixs ns da db dc Hcols. revert ns.
    induction Hcols as [|lv ix cs ixs Hcolumn Hcols IH]; intros [|n ns] Hnodes j Hbound.
    - cbn [length] in Hbound. lia.
    - inversion Hnodes.
    - inversion Hnodes.
    - apply Forall2_cons_iff in Hnodes as [Hnode Hnodes].
      destruct j as [|j].
      + exact (conj Hcolumn Hnode).
      + cbn [nth]. apply (IH ns Hnodes j). cbn [length] in Hbound. lia.
  Qed.

  (** Every in-range node keeps the full plan column invariant and its represented prefix. *)
  Lemma nodes_ok_at : forall p ixs lvl pre ns j, nodes_ok p ixs lvl pre ns ->
    j < length (cols p) ->
    let lv := nth j (cols p) [] in
    let ix := nth j ixs I.empty in
    let n := nth j ns 1%positive in
    (lv <> [] /\ StronglySorted lt lv /\ Forall (fun i => i < nvars p) lv /\
      I.wf (length lv) ix) /\
    exists u, project (filter (fun i => Nat.ltb i lvl) lv) (rev pre) = Some u /\
      I.node ix n u.
  Proof.
    intros p ixs lvl pre ns j [[_ [Hcols _]] [_ [_ Hnodes]]] Hbound.
    exact (aligned_nth _ _ _ _ _ _ _ _ [] I.empty 1%positive Hcols Hnodes j Hbound).
  Qed.

  (** A successful full probe contains a successful child lookup at every participant. *)
  Lemma advance_columns_probe : forall cs ixs lvl ns c ns' j,
    advance_columns cs ixs lvl ns c = Some ns' -> j < length cs ->
    existsb (Nat.eqb lvl) (nth j cs []) = true ->
    exists m, I.child (nth j ixs I.empty) (nth j ns 1%positive) c = Some m.
  Proof.
    induction cs as [|lv cs IH]; intros ixs lvl ns c ns' j Hstep Hbound Hpart.
    - cbn [length] in Hbound. lia.
    - destruct ixs as [|ix ixs], ns as [|n ns];
        cbn [advance_columns] in Hstep; try discriminate.
      destruct (if existsb (Nat.eqb lvl) lv then I.child ix n c else Some n)
        as [m|] eqn:Hhead;
        destruct (advance_columns cs ixs lvl ns c) as [ms|] eqn:Htail; try discriminate.
      destruct j as [|j].
      + cbn [nth] in Hpart |- *. rewrite Hpart in Hhead. exists m. exact Hhead.
      + cbn [nth] in Hpart |- *. eapply IH; [exact Htail| |exact Hpart].
        cbn [length] in Hbound. lia.
  Qed.

  (** A successful extension appears in the selected pivot's child enumeration. *)
  Lemma advance_chosen_child : forall p ixs lvl pre ns j c ns',
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    advance_nodes p ixs lvl ns c = Some ns' ->
    In c (I.children (nth j ixs I.empty) (nth j ns 1%positive)).
  Proof.
    intros p ixs lvl pre ns j c ns' Hnodes Hchoose Hstep.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange Hpart]. apply in_seq in Hrange.
    destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    apply (proj2 (proj1 (I.children_spec _ _ _ u c Hwf Hnode))).
    unfold advance_nodes in Hstep.
    destruct (Nat.leb (S lvl) (level_count p)); [|discriminate].
    eapply (advance_columns_probe (cols p) ixs lvl ns c ns' j);
      [exact Hstep|lia|exact Hpart].
  Qed.

  (** The selected pivot enumerates each next cell only once. *)
  Lemma chosen_children_nodup : forall p ixs lvl pre ns j,
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    NoDup (I.children (nth j ixs I.empty) (nth j ns 1%positive)).
  Proof.
    intros p ixs lvl pre ns j Hnodes Hchoose.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange _]. apply in_seq in Hrange.
    destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    exact (proj2 (I.children_spec _ _ _ u (Id 1%positive) Hwf Hnode)).
  Qed.

  (** A fold preserves any accumulator element preserved by each of its steps. *)
  Lemma fold_left_preserves : forall (A B : Type) (f : list B -> A -> list B)
      cs acc b,
    (forall x out, In x cs -> In b out -> In b (f out x)) ->
    In b acc -> In b (fold_left f cs acc).
  Proof.
    intros A B f cs. induction cs as [|x cs IH]; intros acc b Hstep Hin.
    - exact Hin.
    - cbn [fold_left]. apply IH.
      + intros y out Hy Hout. apply Hstep; [right; exact Hy|exact Hout].
      + apply Hstep; [left; reflexivity|exact Hin].
  Qed.

  (** Any selected fold step can supply an element that all subsequent steps preserve. *)
  Lemma fold_left_contains : forall (A B : Type) (f : list B -> A -> list B)
      cs acc x b,
    (forall y out, In y cs -> In b out -> In b (f out y)) ->
    In x cs -> (forall out, In b (f out x)) -> In b (fold_left f cs acc).
  Proof.
    intros A B f cs. induction cs as [|y cs IH]; intros acc x b Hstep Hin Hnew.
    - contradiction.
    - cbn [fold_left]. destruct Hin as [<-|Hin].
      + eapply fold_left_preserves; [|apply Hnew].
        intros z out Hz Hout. apply Hstep; [right; exact Hz|exact Hout].
      + eapply IH; [|exact Hin|exact Hnew].
        intros z out Hz Hout. apply Hstep; [right; exact Hz|exact Hout].
  Qed.

  (** Enumeration never removes an assignment already present in its accumulator. *)
  Lemma enumerate_acc : forall fuel p ixs ns pre acc b, In b acc ->
    In b (enumerate fuel p ixs ns pre acc).
  Proof.
    induction fuel as [|fuel IH]; intros p ixs ns pre acc b Hin; cbn [enumerate].
    - right. exact Hin.
    - destruct (choose_index p ixs (length pre) ns) as [j|]; [|exact Hin].
      eapply fold_left_preserves; [|exact Hin]. intros c out _ Hout. cbn beta.
      destruct (advance_nodes p ixs (length pre) ns c) as [nodes|]; [|exact Hout].
      apply IH. exact Hout.
  Qed.

  (** Reading the next cell extends the assignment prefix by that cell. *)
  Lemma firstn_next : forall lvl (b : list (cell V.t)) c,
    nth_error b lvl = Some c -> firstn (S lvl) b = firstn lvl b ++ [c].
  Proof.
    induction lvl as [|lvl IH]; intros [|d b] c Hread;
      cbn [nth_error firstn app] in Hread |- *; try discriminate.
    - injection Hread as <-. reflexivity.
    - f_equal. apply IH. exact Hread.
  Qed.

  (** Every full answer extending the current prefix is reached by enumeration. *)
  Lemma enumerate_complete : forall fuel p ixs lvl pre ns acc b,
    fuel + lvl = nvars p -> nodes_ok p ixs lvl pre ns -> answer p ixs b ->
    firstn lvl b = rev pre -> In b (enumerate fuel p ixs ns pre acc).
  Proof.
    induction fuel as [|fuel IH]; intros p ixs lvl pre ns acc b Hfuel Hnodes Hanswer Hprefix.
    - assert (Hlevel : lvl = nvars p) by lia. subst lvl.
      rewrite firstn_all2 in Hprefix by (pose proof (proj1 Hanswer); lia).
      cbn [enumerate]. left. symmetry. exact Hprefix.
    - pose proof (proj1 (proj2 Hnodes)) as Hlength.
      destruct (choose_index_some p ixs lvl pre ns Hnodes ltac:(lia)) as [j Hchoose].
      destruct (nth_error b lvl) as [c|] eqn:Hread.
      2: { apply nth_error_None in Hread. pose proof (proj1 Hanswer). lia. }
      assert (Hnext_prefix : firstn (S lvl) b = rev (c :: pre)).
      { rewrite (firstn_next lvl b c Hread), Hprefix. reflexivity. }
      destruct (advance_nodes_complete p ixs lvl pre ns c b Hnodes Hanswer Hnext_prefix)
        as [nodes Hstep].
      pose proof (advance_chosen_child p ixs lvl pre ns j c nodes Hnodes Hchoose Hstep)
        as Hchild.
      cbn [enumerate]. rewrite Hlength, Hchoose.
      eapply (@fold_left_contains (cell V.t) (list (cell V.t)) _ _ acc c b).
      + intros d out _ Hout. cbn beta.
        destruct (advance_nodes p ixs lvl ns d) as [next|]; [|exact Hout].
        apply enumerate_acc. exact Hout.
      + exact Hchild.
      + intros out. cbn beta. rewrite Hstep.
        eapply (IH p ixs (S lvl) (c :: pre) nodes out b).
        * lia.
        * eapply advance_nodes_ok; eassumption.
        * exact Hanswer.
        * exact Hnext_prefix.
  Qed.

  (** Different next cells describe disjoint assignment prefixes. *)
  Lemma next_prefix_unique : forall lvl (pre : list (cell V.t)) c d b,
    firstn (S lvl) b = rev (c :: pre) ->
    firstn (S lvl) b = rev (d :: pre) -> c = d.
  Proof.
    intros lvl pre c d b Hc Hd.
    assert (Heq : rev (c :: pre) = rev (d :: pre)) by congruence.
    apply (f_equal (@rev (cell V.t))) in Heq. rewrite !rev_involutive in Heq.
    now injection Heq.
  Qed.

  (** Disjoint next-cell branches preserve duplicate-free enumeration. *)
  Lemma enumerate_nodup : forall fuel p ixs lvl pre ns acc,
    fuel + lvl = nvars p -> nodes_ok p ixs lvl pre ns -> NoDup acc ->
    (forall b, answer p ixs b -> firstn lvl b = rev pre -> ~ In b acc) ->
    NoDup (enumerate fuel p ixs ns pre acc).
  Proof.
    induction fuel as [|fuel IH]; intros p ixs lvl pre ns acc Hfuel Hnodes Hacc Hfresh.
    - assert (Hlevel : lvl = nvars p) by lia. subst lvl.
      cbn [enumerate]. constructor; [|exact Hacc]. apply Hfresh.
      + eapply nodes_ok_answer. exact Hnodes.
      + apply firstn_all2. rewrite length_rev. pose proof (proj1 (proj2 Hnodes)). lia.
    - pose proof (proj1 (proj2 Hnodes)) as Hlength.
      cbn [enumerate]. rewrite Hlength.
      destruct (choose_index p ixs lvl ns) as [j|] eqn:Hchoose; [|exact Hacc].
      eapply (@fold_left_nodup_disjoint (cell V.t) (list (cell V.t)) _
        (fun c b => answer p ixs b /\ firstn (S lvl) b = rev (c :: pre))).
      + eapply chosen_children_nodup; eassumption.
      + exact Hacc.
      + intros c b _ [Hanswer Hprefix]. apply Hfresh; [exact Hanswer|].
        eapply prefix_before_next; eassumption.
      + intros c d b [_ Hc] [_ Hd]. eapply next_prefix_unique; eassumption.
      + intros c out b _ Hbody. cbn beta in Hbody.
        destruct (advance_nodes p ixs lvl ns c) as [nodes|] eqn:Hstep;
          [|left; exact Hbody].
        eapply enumerate_sound; [| |exact Hbody].
        * lia.
        * eapply advance_nodes_ok; eassumption.
      + intros c out _ Hout Hfresh_cell. cbn beta.
        destruct (advance_nodes p ixs lvl ns c) as [nodes|] eqn:Hstep; [|exact Hout].
        eapply (IH p ixs (S lvl) (c :: pre) nodes out).
        * lia.
        * eapply advance_nodes_ok; eassumption.
        * exact Hout.
        * intros b Hanswer Hprefix. apply Hfresh_cell. split; assumption.
  Qed.

  Lemma run_sound : forall p ixs b, wf_plan p ixs ->
    In b (run p ixs) -> answer p ixs b.
  Proof.
    intros p ixs b Hwf Hin.
    destruct (enumerate_sound (nvars p) p ixs 0 [] (map I.root ixs) [] b
      ltac:(lia) (nodes_ok_initial p ixs Hwf) Hin) as [Hempty|[Hanswer _]].
    - contradiction.
    - exact Hanswer.
  Qed.

  Lemma run_complete : forall p ixs b, wf_plan p ixs ->
    answer p ixs b -> In b (run p ixs).
  Proof.
    intros p ixs b Hwf Hanswer.
    apply (enumerate_complete (nvars p) p ixs 0 [] (map I.root ixs) [] b).
    - lia.
    - apply nodes_ok_initial. exact Hwf.
    - exact Hanswer.
    - reflexivity.
  Qed.

  Lemma run_nodup : forall p ixs, wf_plan p ixs -> NoDup (run p ixs).
  Proof.
    intros p ixs Hwf.
    apply (enumerate_nodup (nvars p) p ixs 0 [] (map I.root ixs) []).
    - lia.
    - apply nodes_ok_initial. exact Hwf.
    - constructor.
    - intros b _ _ Hempty. contradiction.
  Qed.

End Join.

Module JoinT (V : VALUE_T) (I : INDEX_T V) <: JOIN_ALL V I.
  Include Join V I.
  TimeFun level_count.
  TimeFun columns.
  TimeFun choose_columns.
  TimeFun choose_index.
  TimeFun advance_columns.
  TimeFun advance_nodes.
  TimeFun enumerate.
  TimeFun run.

  (** Membership scans fit the square of the plan's column and level bound. *)
  Lemma T_existsb_level_le : forall lvl lv L, lvl <= L -> length lv <= L ->
    (List.T_existsb (Nat.eqb lvl) (Nat.T_eqb lvl) lv <=
      4 * N.of_nat ((L + 1) * (L + 1)))%N.
  Proof.
    intros lvl lv L Hlevel Hlength.
    pose proof (@List.T_existsb_le nat (Nat.eqb lvl) (Nat.T_eqb lvl)
      (N.of_nat lvl + 1)%N lv (fun i => Nat.T_eqb_le lvl i)) as Hscan.
    nia.
  Qed.

  (** A common per-operation budget gives a linear bound for pivot selection. *)
  Lemma T_choose_columns_budget : forall cs ixs ns lvl pos K,
    length cs = length ixs -> length cs = length ns ->
    Forall (fun lv => (List.T_existsb (Nat.eqb lvl) (Nat.T_eqb lvl) lv <= K)%N) cs ->
    Forall2 (fun ix n => (I.T_degree ix n <= K)%N /\
      forall d, (N.T_leb (I.degree ix n) d <= K)%N) ixs ns ->
    (T_choose_columns cs ixs ns lvl pos <= (3 * K + 3) * N.of_nat (length cs + 1))%N.
  Proof.
    induction cs as [| lv cs IH]; intros [| ix ixs] [| n ns] lvl pos K
      Hix Hns Hscans Hoperations;
      cbn [length] in Hix, Hns; try discriminate.
    - time_step choose_columns.
    - apply Forall_cons_iff in Hscans as [Hscan Hscans].
      change (List.T_existsb (Nat.eqb lvl) (fun i => Nat.T_eqb lvl i) lv <= K)%N in Hscan.
      apply Forall2_cons_iff in Hoperations as [[Hdegree Hcompare] Hoperations].
      pose proof (IH ixs ns lvl (S pos) K ltac:(lia) ltac:(lia)
        Hscans Hoperations) as Htail.
      unfold T_choose_columns at 1. time_cbn. fold T_choose_columns.
      destruct (existsb (Nat.eqb lvl) lv).
      + destruct (choose_columns cs ixs ns lvl (S pos)) as [[j d] |].
        * pose proof (Hcompare d). time_cbn. nia.
        * time_cbn. nia.
      + time_cbn. nia.
  Qed.

  (** A common per-operation budget gives a linear bound for all column probes. *)
  Lemma T_advance_columns_budget : forall cs ixs ns lvl c K,
    length cs = length ixs -> length cs = length ns ->
    Forall (fun lv => (List.T_existsb (Nat.eqb lvl) (Nat.T_eqb lvl) lv <= K)%N) cs ->
    (forall ix n, In ix ixs -> (I.T_child ix n c <= K)%N) ->
    (T_advance_columns cs ixs lvl ns c <= (2 * K + 3) * N.of_nat (length cs + 1))%N.
  Proof.
    induction cs as [| lv cs IH]; intros [| ix ixs] [| n ns] lvl c K
      Hix Hns Hscans Hoperations;
      cbn [length] in Hix, Hns; try discriminate.
    - time_step advance_columns.
    - apply Forall_cons_iff in Hscans as [Hscan Hscans].
      change (List.T_existsb (Nat.eqb lvl) (fun i => Nat.T_eqb lvl i) lv <= K)%N in Hscan.
      pose proof (Hoperations ix n (or_introl eq_refl)) as Hchild.
      assert (Hrest : forall ix' n', In ix' ixs -> (I.T_child ix' n' c <= K)%N).
      { intros ix' n' Hin. exact (Hoperations ix' n' (or_intror Hin)). }
      pose proof (IH ixs ns lvl c K ltac:(lia) ltac:(lia) Hscans Hrest) as Htail.
      unfold T_advance_columns at 1. time_cbn. fold T_advance_columns.
      destruct (existsb (Nat.eqb lvl) lv).
      + destruct (I.child ix n c); time_cbn; nia.
      + time_cbn; nia.
  Qed.

  (** The scan factor covers scalar work, membership scans, degree reads and widths. *)
  Lemma scan_factor_bounds : forall L W,
    let unit := ((I.c_ix + 1) * N.of_nat (W + 1) *
      N.of_nat ((L + 1) * (L + 1)))%N in
    (1 <= unit /\ N.of_nat ((L + 1) * (L + 1)) <= unit /\
      I.c_ix * N.of_nat (W + 1) <= unit /\ N.of_nat (W + 1) <= unit)%N.
  Proof.
    intros L W unit.
    assert (Hsquare : (1 <= N.of_nat ((L + 1) * (L + 1)))%N) by nia.
    assert (Hwidth : (1 <= N.of_nat (W + 1))%N) by lia.
    assert (Hproduct : (1 <= (I.c_ix + 1) * N.of_nat (W + 1))%N) by nia.
    assert (Hbase : ((I.c_ix + 1) * N.of_nat (W + 1) <= unit)%N).
    { unfold unit. rewrite <- N.mul_1_r at 1. now apply N.mul_le_mono_l. }
    assert (Hscan : (N.of_nat ((L + 1) * (L + 1)) <= unit)%N).
    { unfold unit. rewrite <- N.mul_1_l at 1. now apply N.mul_le_mono_r. }
    split; [lia |]. split; [exact Hscan |]. split.
    - eapply N.le_trans; [| exact Hbase]. apply N.mul_le_mono_r. lia.
    - eapply N.le_trans; [| exact Hbase]. rewrite <- N.mul_1_l at 1.
      apply N.mul_le_mono_r. lia.
  Qed.

  (** Pivot selection pays once for each aligned column and its degree comparison. *)
  Lemma T_choose_columns_le : forall cs ixs ns lvl pos L W,
    length cs = length ixs -> length cs = length ns ->
    Forall (fun lv => length lv <= L) cs -> lvl <= L ->
    Forall2 (fun ix n => I.width ix [] <= W /\ N.size_nat (I.degree ix n) <= W) ixs ns ->
    (T_choose_columns cs ixs ns lvl pos <=
      16 * (I.c_ix + 1) * N.of_nat (length cs + 1) * N.of_nat (W + 1) *
        N.of_nat ((L + 1) * (L + 1)))%N.
  Proof.
    intros cs ixs ns lvl pos L W Hix Hns Hlengths Hlevel Hwidths.
    set (unit := ((I.c_ix + 1) * N.of_nat (W + 1) *
      N.of_nat ((L + 1) * (L + 1)))%N).
    destruct (scan_factor_bounds L W) as [Hone [Hsquare [Hdegree Hwidth]]].
    fold unit in Hone, Hsquare, Hdegree, Hwidth.
    assert (Hscans : Forall (fun lv =>
      (List.T_existsb (Nat.eqb lvl) (Nat.T_eqb lvl) lv <= 4 * unit)%N) cs).
    { eapply Forall_impl; [| exact Hlengths]. intros lv Hlength.
      pose proof (T_existsb_level_le lvl lv L Hlevel Hlength). lia. }
    assert (Hoperations : Forall2 (fun ix n => (I.T_degree ix n <= 4 * unit)%N /\
      forall d, (N.T_leb (I.degree ix n) d <= 4 * unit)%N) ixs ns).
    { eapply Forall2_impl; [| exact Hwidths]. intros ix n [Hix_width Hbits]. split.
      - eapply N.le_trans; [apply I.T_degree_le |].
        eapply N.le_trans with (m := (I.c_ix * N.of_nat (W + 1))%N); [| lia].
        apply N.mul_le_mono_l. lia.
      - intro d. pose proof (N.T_leb_le (I.degree ix n) d). lia. }
    pose proof (T_choose_columns_budget cs ixs ns lvl pos (4 * unit)%N
      Hix Hns Hscans Hoperations) as Hcost.
    replace (16 * (I.c_ix + 1) * N.of_nat (length cs + 1) * N.of_nat (W + 1) *
      N.of_nat ((L + 1) * (L + 1)))%N with
      (16 * unit * N.of_nat (length cs + 1))%N by (unfold unit; ring).
    clearbody unit. nia.
  Qed.

  (** Charging every aligned column bounds advancement even when a probe exits early. *)
  Lemma T_advance_columns_le : forall cs ixs ns lvl c L W,
    length cs = length ixs -> length cs = length ns ->
    Forall (fun lv => length lv <= L) cs -> lvl <= L ->
    Forall (fun ix => I.width ix [c] <= W) ixs ->
    (T_advance_columns cs ixs lvl ns c <=
      16 * (I.c_ix + 1) * N.of_nat (length cs + 1) * N.of_nat (W + 1) *
        N.of_nat ((L + 1) * (L + 1)))%N.
  Proof.
    intros cs ixs ns lvl c L W Hix Hns Hlengths Hlevel Hwidths.
    set (unit := ((I.c_ix + 1) * N.of_nat (W + 1) *
      N.of_nat ((L + 1) * (L + 1)))%N).
    destruct (scan_factor_bounds L W) as [Hone [Hsquare [Hchild Hwidth]]].
    fold unit in Hone, Hsquare, Hchild, Hwidth.
    assert (Hscans : Forall (fun lv =>
      (List.T_existsb (Nat.eqb lvl) (Nat.T_eqb lvl) lv <= 4 * unit)%N) cs).
    { eapply Forall_impl; [| exact Hlengths]. intros lv Hlength.
      pose proof (T_existsb_level_le lvl lv L Hlevel Hlength). lia. }
    assert (Hoperations : forall ix n, In ix ixs -> (I.T_child ix n c <= 4 * unit)%N).
    { intros ix n Hin. rewrite Forall_forall in Hwidths.
      pose proof (Hwidths ix Hin) as Hix_width.
      eapply N.le_trans; [apply I.T_child_le |].
      eapply N.le_trans with (m := (I.c_ix * N.of_nat (W + 1))%N); [| lia].
      apply N.mul_le_mono_l. lia. }
    pose proof (T_advance_columns_budget cs ixs ns lvl c (4 * unit)%N
      Hix Hns Hscans Hoperations) as Hcost.
    replace (16 * (I.c_ix + 1) * N.of_nat (length cs + 1) * N.of_nat (W + 1) *
      N.of_nat ((L + 1) * (L + 1)))%N with
      (16 * unit * N.of_nat (length cs + 1))%N by (unfold unit; ring).
    clearbody unit. nia.
  Qed.

  (** One level's scans and candidate probes fit its charged recursive work. *)
  Lemma join_level_budget : forall F M D C : N,
    (1 <= F)%N -> (1 <= M)%N -> (C + 1 <= F)%N ->
    (1 + F + 64 * F * (M + 1) + (2 * M + C) + 2 * F * (D + 1) +
      (D + 1) + (1 + 64 * F * (M + 1)) * D <=
      4096 * F * (1 + M + M * (1 + D)))%N.
  Proof.
    intros F M D C HF HM HC.
    assert (Hcolumns : (M <= F * M)%N).
    { rewrite <- N.mul_1_l at 1. now apply N.mul_le_mono_r. }
    assert (Hcandidates : (D <= F * D)%N).
    { rewrite <- N.mul_1_l at 1. now apply N.mul_le_mono_r. }
    assert (Hprobes : (F * D <= F * M * D)%N).
    { replace (F * D)%N with (F * 1 * D)%N at 1 by ring.
      apply N.mul_le_mono_r. now apply N.mul_le_mono_l. }
    replace (1 + F + 64 * F * (M + 1) + (2 * M + C) + 2 * F * (D + 1) +
      (D + 1) + (1 + 64 * F * (M + 1)) * D)%N with
      (2 + C + 2 * M + 67 * F + 64 * (F * M) + 66 * (F * D) + 2 * D +
        64 * (F * M * D))%N by ring.
    replace (4096 * F * (1 + M + M * (1 + D)))%N with
      (4096 * F + 8192 * (F * M) + 4096 * (F * M * D))%N by ring.
    set (FM := (F * M)%N) in *.
    set (FD := (F * D)%N) in *.
    set (FMD := (FM * D)%N) in *.
    clearbody FM FD FMD. lia.
  Qed.

  (** This proof-only recursion counts every column probe and every surviving subtree. *)
  Fixpoint recursive_work (fuel : nat) (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) {struct fuel} : nat :=
    match fuel with
    | 0 => 1 + nvars p
    | S rest =>
      match choose_index p ixs lvl ns with
      | None => 1 + length (cols p) + length (cols p)
      | Some j =>
        1 + length (cols p) + length (cols p) *
          (1 + N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive))) +
        fold_right Nat.add 0
          (map (fun c =>
            match advance_nodes p ixs lvl ns c with
            | None => 0
            | Some nodes => recursive_work rest p ixs (S lvl) nodes
            end) (I.children (nth j ixs I.empty) (nth j ns 1%positive)))
      end
    end.

  (** The selected pivot's stored degree is exactly its enumerated child count. *)
  Lemma chosen_degree_count : forall p ixs lvl pre ns j,
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive)) =
      length (I.children (nth j ixs I.empty) (nth j ns 1%positive)).
  Proof.
    intros p ixs lvl pre ns j Hnodes Hchoose.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange _]. apply in_seq in Hrange.
    destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    exact (I.degree_spec _ _ _ u Hwf Hnode).
  Qed.

  Definition work (p : jplan) (ixs : list I.t) : nat :=
    recursive_work (nvars p) p ixs 0 (map I.root ixs).
  Definition wmax (_ : jplan) (ixs : list I.t) : nat :=
    fold_right (fun ix w => Nat.max (Pos.size_nat (I.next ix) + I.max_cell_bits ix) w)
      0 ixs.

  Module IT := IndexTimeFacts V I.

  (** Strictly increasing columns contain no repeated variable positions. *)
  Lemma sorted_column_nodup : forall lv, StronglySorted lt lv -> NoDup lv.
  Proof.
    intros lv Hsorted. induction Hsorted as [|i lv Hsorted IH Hafter]; constructor.
    - intro Hin. rewrite Forall_forall in Hafter. specialize (Hafter i Hin). lia.
    - exact IH.
  Qed.

  (** An increasing column inside the variable range has at most that many entries. *)
  Lemma column_length_bound : forall lv limit, StronglySorted lt lv ->
    Forall (fun i => i < limit) lv -> length lv <= limit.
  Proof.
    intros lv limit Hsorted Hrange.
    assert (Hinclude : incl lv (seq 0 limit)).
    { intros i Hin. apply in_seq. rewrite Forall_forall in Hrange.
      specialize (Hrange i Hin). lia. }
    pose proof (NoDup_incl_length (sorted_column_nodup lv Hsorted) Hinclude) as Hlength.
    now rewrite length_seq in Hlength.
  Qed.

  (** Every plan column fits within its declared variable count. *)
  Lemma plan_column_lengths : forall p ixs, wf_plan p ixs ->
    Forall (fun lv => length lv <= nvars p) (cols p).
  Proof.
    intros p ixs [_ [Hcols _]]. induction Hcols as [|lv ix cs ixs Hcolumn Hcols IH].
    - constructor.
    - constructor; [|exact IH]. apply column_length_bound; tauto.
  Qed.

  (** The maximum width covers the stored counter and cells of each input index. *)
  Lemma wmax_contains : forall p ixs ix, In ix ixs ->
    Pos.size_nat (I.next ix) + I.max_cell_bits ix <= wmax p ixs.
  Proof.
    intros p ixs. unfold wmax. induction ixs as [|head ixs IH]; intros ix Hin.
    - contradiction.
    - cbn [fold_right]. destruct Hin as [<-|Hin].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.

  (** Pointwise facts at aligned positions reconstruct a two-list invariant. *)
  Lemma Forall2_by_nth : forall (A B : Type) (P : A -> B -> Prop) xs ys da db,
    length xs = length ys ->
    (forall j, j < length xs -> P (nth j xs da) (nth j ys db)) -> Forall2 P xs ys.
  Proof.
    intros A B P xs. induction xs as [|x xs IH]; intros [|y ys] da db Hlength Hpoint;
      cbn [length] in Hlength; try discriminate.
    - constructor.
    - constructor.
      + exact (Hpoint 0 ltac:(cbn [length]; lia)).
      + apply (IH ys da db); [lia|]. intros j Hj.
        apply (Hpoint (S j)). cbn [length]. lia.
  Qed.

  (** Every represented index has bounded empty-query width and encoded degree. *)
  Lemma nodes_degree_widths : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    Forall2 (fun ix n => I.width ix [] <= wmax p ixs + 1 /\
      N.size_nat (I.degree ix n) <= wmax p ixs + 1) ixs ns.
  Proof.
    intros p ixs lvl pre ns Hnodes.
    destruct (nodes_ok_lengths p ixs lvl pre ns Hnodes) as [Hix Hns].
    eapply (Forall2_by_nth I.t positive _ ixs ns I.empty 1%positive); [lia|].
    intros j Hj. destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    assert (Hin : In (nth j ixs I.empty) ixs) by (apply nth_In; exact Hj).
    pose proof (wmax_contains p ixs _ Hin) as Hwidth.
    pose proof (IT.width_empty (nth j ixs I.empty)) as Hempty.
    pose proof (IT.degree_bits _ _ _ u Hwf Hnode) as Hdegree. split; lia.
  Qed.

  (** Every candidate cell from a pivot fits the common stored-width budget. *)
  Lemma chosen_child_bits : forall p ixs lvl pre ns j c,
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    In c (I.children (nth j ixs I.empty) (nth j ns 1%positive)) ->
    cell_bits V.encode c <= wmax p ixs.
  Proof.
    intros p ixs lvl pre ns j c Hnodes Hchoose Hchild.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange _]. apply in_seq in Hrange.
    destruct (nodes_ok_lengths p ixs lvl pre ns Hnodes) as [Hix _].
    destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    assert (Hin : In (nth j ixs I.empty) ixs) by (apply nth_In; lia).
    pose proof (wmax_contains p ixs _ Hin) as Hwidth.
    pose proof (IT.child_bits _ _ _ u c Hwf Hnode Hchild) as Hbits. lia.
  Qed.

  (** A candidate fitting the common budget has bounded query width at every index. *)
  Lemma probe_widths : forall p ixs c, cell_bits V.encode c <= wmax p ixs ->
    Forall (fun ix => I.width ix [c] <= 2 * wmax p ixs + 1) ixs.
  Proof.
    intros p ixs c Hbits. apply Forall_forall. intros ix Hin.
    pose proof (wmax_contains p ixs ix Hin) as Hwidth.
    pose proof (IT.width_singleton ix c) as Hsingle. lia.
  Qed.

  (** Coverage gives at least one column at every unfinished level. *)
  Lemma unfinished_columns : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    lvl < nvars p -> 0 < length (cols p).
  Proof.
    intros p ixs lvl pre ns [[_ [_ Hcover]] _] Hlevel.
    destruct (Hcover lvl Hlevel) as [lv [Hin _]].
    destruct (cols p) as [|head cs]; [contradiction|]. cbn [length]. lia.
  Qed.

  (** A common proof-only factor absorbs index width and unary variable operations. *)
  Definition scan_factor (p : jplan) (ixs : list I.t) : N :=
    ((I.c_ix + 1) * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)))%N.

  (** The common factor covers each of its positive constituent costs. *)
  Lemma scan_factor_covers : forall p ixs,
    (1 <= scan_factor p ixs /\ I.c_ix + 1 <= scan_factor p ixs /\
      N.of_nat (nvars p + 1) <= scan_factor p ixs /\
      N.of_nat ((nvars p + 1) * (nvars p + 1)) <= scan_factor p ixs /\
      (I.c_ix + 1) * N.of_nat (wmax p ixs + 1) <= scan_factor p ixs)%N.
  Proof.
    intros p ixs. unfold scan_factor. rewrite Nat2N.inj_mul.
    assert (Hvars : (1 <= N.of_nat (nvars p + 1))%N) by lia.
    assert (Hwidth : (1 <= N.of_nat (wmax p ixs + 1))%N) by lia.
    assert (Hsquare : (1 <= N.of_nat (nvars p + 1) * N.of_nat (nvars p + 1))%N) by nia.
    assert (Hindex : (1 <= (I.c_ix + 1) * N.of_nat (wmax p ixs + 1))%N) by nia.
    repeat split; nia.
  Qed.

  (** Reading the pivot pays for both list traversals and the eagerly evaluated empty default. *)
  Lemma T_pivot_reads_le : forall p ixs lvl pre ns j,
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    (ListDef.T_nth j ixs I.empty + ListDef.T_nth j ns 1%positive + I.T_empty <=
      2 * N.of_nat (length (cols p)) + I.c_ix)%N.
  Proof.
    intros p ixs lvl pre ns j Hnodes Hchoose.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange _]. apply in_seq in Hrange.
    pose proof (ListDef.T_nth_le I.t j ixs I.empty) as Hix.
    pose proof (ListDef.T_nth_le positive j ns 1%positive) as Hns.
    pose proof I.T_empty_le as Hempty. lia.
  Qed.

  (** Enumerating the pivot children pays their stored degree at the common width. *)
  Lemma T_pivot_children_le : forall p ixs lvl pre ns j,
    nodes_ok p ixs lvl pre ns -> choose_index p ixs lvl ns = Some j ->
    (I.T_children (nth j ixs I.empty) (nth j ns 1%positive) <=
      2 * scan_factor p ixs *
        N.of_nat (N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive)) + 1))%N.
  Proof.
    intros p ixs lvl pre ns j Hnodes Hchoose.
    destruct (choose_index_min p ixs lvl pre ns j Hnodes Hchoose) as [Hpart _].
    apply filter_In in Hpart as [Hrange _]. apply in_seq in Hrange.
    destruct (nodes_ok_lengths p ixs lvl pre ns Hnodes) as [Hix _].
    destruct (nodes_ok_at p ixs lvl pre ns j Hnodes ltac:(lia))
      as [[_ [_ [_ Hwf]]] [u [_ Hnode]]].
    assert (Hin : In (nth j ixs I.empty) ixs) by (apply nth_In; lia).
    pose proof (wmax_contains p ixs _ Hin) as Hstored.
    pose proof (IT.width_empty (nth j ixs I.empty)) as Hempty.
    pose proof (I.T_children_le _ _ (nth j ns 1%positive) Hwf) as Hchildren.
    destruct (scan_factor_covers p ixs) as [_ [_ [_ [_ Hfactor]]]].
    assert (Hquery : (N.of_nat (I.width (nth j ixs I.empty) [] + 1) <=
      2 * N.of_nat (wmax p ixs + 1))%N) by lia.
    assert (Hscaled : (I.c_ix * N.of_nat (I.width (nth j ixs I.empty) [] + 1) <=
      2 * scan_factor p ixs)%N) by nia.
    nia.
  Qed.

  (** Reading the current prefix length fits the common variable-operation budget. *)
  Lemma T_prefix_length_le : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    (Datatypes.T_length pre <= scan_factor p ixs)%N.
  Proof.
    intros p ixs lvl pre ns [_ [Hlength [Hlevel _]]].
    pose proof (Datatypes.T_length_le pre) as Htime.
    destruct (scan_factor_covers p ixs) as [_ [_ [Hfactor _]]]. lia.
  Qed.

  (** Reversing a completed prefix fits the quadratic variable-operation budget. *)
  Lemma T_prefix_rev_le : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    (List.T_rev pre <= scan_factor p ixs)%N.
  Proof.
    intros p ixs lvl pre ns [_ [Hlength [Hlevel _]]].
    pose proof (List.T_rev_le pre) as Htime.
    destruct (scan_factor_covers p ixs) as [_ [_ [_ [Hfactor _]]]].
    rewrite Nat2N.inj_mul in Hfactor.
    assert (Hbound : (N.of_nat (length pre) + 1 <= N.of_nat (nvars p + 1))%N) by lia.
    nia.
  Qed.

  (** Root initialization pays a constant amount for each supplied index. *)
  Lemma T_run_initial_le : forall p ixs,
    (T_run p ixs <= T_enumerate (nvars p) p ixs (map I.root ixs) [] [] +
      4 * (I.c_ix + 1) * N.of_nat (length ixs + 1))%N.
  Proof.
    intros [vars cs] ixs.
    pose proof (Argent.Std.ListDef.T_map_le I.root (fun ix => I.T_root ix)
      I.c_ix ixs I.T_root_le) as Hmap.
    time_unfold T_run. time_unfold T_level_count. time_cbn. nia.
  Qed.

  (** Pivot selection adds only the plan projection and its own call to the column scan. *)
  Lemma T_choose_index_overhead : forall p ixs lvl ns,
    (T_choose_index p ixs lvl ns <= T_choose_columns (cols p) ixs ns lvl 0 + 2)%N.
  Proof.
    intros [vars cs] ixs lvl ns.
    time_unfold T_choose_index. time_unfold T_columns. time_cbn. lia.
  Qed.

  (** The advance wrapper pays the unary level guard and the two plan projections. *)
  Lemma T_advance_nodes_overhead : forall p ixs lvl ns c,
    (T_advance_nodes p ixs lvl ns c <=
      T_advance_columns (cols p) ixs lvl ns c + N.of_nat (lvl + 5))%N.
  Proof.
    intros [vars cs] ixs lvl ns c.
    pose proof (Nat.T_leb_le (S lvl) vars) as Hguard.
    time_unfold T_advance_nodes. time_unfold T_level_count. time_unfold T_columns.
    destruct vars as [|vars].
    - time_cbn. lia.
    - time_cbn. destruct (Nat.leb lvl vars); lia.
  Qed.

  (** The complete pivot scan fits the common factor times the number of columns. *)
  Lemma T_choose_index_le : forall p ixs lvl pre ns, nodes_ok p ixs lvl pre ns ->
    (T_choose_index p ixs lvl ns <=
      64 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N.
  Proof.
    intros p ixs lvl pre ns Hnodes.
    destruct (nodes_ok_lengths p ixs lvl pre ns Hnodes) as [Hix Hns].
    pose proof (plan_column_lengths p ixs (proj1 Hnodes)) as Hlengths.
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel.
    pose proof (nodes_degree_widths p ixs lvl pre ns Hnodes) as Hwidths.
    pose proof (T_choose_columns_le (cols p) ixs ns lvl 0 (nvars p) (wmax p ixs + 1)
      Hix Hns Hlengths Hlevel Hwidths) as Hscan.
    assert (Hscaled : (T_choose_columns (cols p) ixs ns lvl 0 <=
      32 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N).
    { eapply N.le_trans; [exact Hscan|].
      replace (32 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N with
        (16 * (I.c_ix + 1) * N.of_nat (length (cols p) + 1) *
          (2 * N.of_nat (wmax p ixs + 1)) *
          N.of_nat ((nvars p + 1) * (nvars p + 1)))%N by (unfold scan_factor; ring).
      apply N.mul_le_mono_r. apply N.mul_le_mono_l. lia. }
    pose proof (T_choose_index_overhead p ixs lvl ns) as Hwrapper.
    destruct (scan_factor_covers p ixs) as [Hfactor _].
    assert (Hcolumns : (1 <= N.of_nat (length (cols p) + 1))%N) by lia.
    nia.
  Qed.

  (** Every candidate probe fits the same factor when the candidate fits the stored width. *)
  Lemma T_advance_nodes_le : forall p ixs lvl pre ns c, nodes_ok p ixs lvl pre ns ->
    cell_bits V.encode c <= wmax p ixs ->
    (T_advance_nodes p ixs lvl ns c <=
      64 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N.
  Proof.
    intros p ixs lvl pre ns c Hnodes Hbits.
    destruct (nodes_ok_lengths p ixs lvl pre ns Hnodes) as [Hix Hns].
    pose proof (plan_column_lengths p ixs (proj1 Hnodes)) as Hlengths.
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel.
    pose proof (probe_widths p ixs c Hbits) as Hwidths.
    pose proof (T_advance_columns_le (cols p) ixs ns lvl c (nvars p)
      (2 * wmax p ixs + 1) Hix Hns Hlengths Hlevel Hwidths) as Hscan.
    assert (Hscaled : (T_advance_columns (cols p) ixs lvl ns c <=
      32 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N).
    { eapply N.le_trans; [exact Hscan|].
      replace (32 * scan_factor p ixs * N.of_nat (length (cols p) + 1))%N with
        (16 * (I.c_ix + 1) * N.of_nat (length (cols p) + 1) *
          (2 * N.of_nat (wmax p ixs + 1)) *
          N.of_nat ((nvars p + 1) * (nvars p + 1)))%N by (unfold scan_factor; ring).
      apply N.mul_le_mono_r. apply N.mul_le_mono_l. lia. }
    pose proof (T_advance_nodes_overhead p ixs lvl ns c) as Hwrapper.
    destruct (scan_factor_covers p ixs) as [Hfactor [_ [Hvars _]]].
    assert (Hcolumns : (1 <= N.of_nat (length (cols p) + 1))%N) by lia.
    assert (Hguard : (N.of_nat (lvl + 5) <= 5 * scan_factor p ixs)%N) by lia.
    nia.
  Qed.

  (** Each recursive work unit pays a common factor, without a surcharge per subtree. *)
  Lemma T_enumerate_le : forall fuel p ixs lvl pre ns acc,
    fuel + lvl = nvars p -> nodes_ok p ixs lvl pre ns ->
    (T_enumerate fuel p ixs ns pre acc <=
      4096 * scan_factor p ixs * N.of_nat (recursive_work fuel p ixs lvl ns))%N.
  Proof.
    induction fuel as [|fuel IH]; intros p ixs lvl pre ns acc Hfuel Hnodes.
    - pose proof (T_prefix_rev_le p ixs lvl pre ns Hnodes) as Hreverse.
      destruct (scan_factor_covers p ixs) as [Hfactor _].
      set (F := scan_factor p ixs) in *. clearbody F.
      cbn [recursive_work]. time_unfold T_enumerate. time_cbn. nia.
    - pose proof (proj1 (proj2 Hnodes)) as Hlength.
      assert (Hlevel : lvl < nvars p) by lia.
      destruct (choose_index_some p ixs lvl pre ns Hnodes Hlevel) as [j Hchoose].
      pose proof (chosen_degree_count p ixs lvl pre ns j Hnodes Hchoose) as Hdegree.
      pose proof (unfinished_columns p ixs lvl pre ns Hnodes Hlevel) as Hcolumns.
      pose proof (T_prefix_length_le p ixs lvl pre ns Hnodes) as Hlength_time.
      pose proof (T_choose_index_le p ixs lvl pre ns Hnodes) as Hchoose_time.
      pose proof (T_pivot_reads_le p ixs lvl pre ns j Hnodes Hchoose) as Hread_time.
      pose proof (T_pivot_children_le p ixs lvl pre ns j Hnodes Hchoose) as Hchildren_time.
      destruct (scan_factor_covers p ixs) as [Hfactor [Hindex _]].
      set (F := scan_factor p ixs) in *.
      set (children := I.children (nth j ixs I.empty) (nth j ns 1%positive)) in *.
      set (branch_work := fun c => match advance_nodes p ixs lvl ns c with
        | Some nodes => recursive_work fuel p ixs (S lvl) nodes
        | None => 0%nat
        end).
      assert (Hfold : (List.T_fold_left
          (fun out c => match advance_nodes p ixs lvl ns c with
            | Some nodes => enumerate fuel p ixs nodes (c :: pre) out
            | None => out
            end)
          (fun out c => 1 + (T_advance_nodes p ixs lvl ns c +
            match advance_nodes p ixs lvl ns c with
            | Some nodes => T_enumerate fuel p ixs nodes (c :: pre) out
            | None => 0
            end)) children acc <=
        N.of_nat (length children + 1) +
          ((1 + 64 * F * N.of_nat (length (cols p) + 1)) * N.of_nat (length children) +
            (4096 * F) * N.of_nat (fold_right Nat.add 0%nat (map branch_work children))))%N).
      { eapply N.le_trans.
        - eapply T_fold_left_sum_le with (cost := fun c =>
            ((1 + 64 * F * N.of_nat (length (cols p) + 1)) +
              (4096 * F) * N.of_nat (branch_work c))%N).
          intros out c Hin. cbn beta. unfold branch_work.
          pose proof (chosen_child_bits p ixs lvl pre ns j c Hnodes Hchoose Hin) as Hbits.
          pose proof (T_advance_nodes_le p ixs lvl pre ns c Hnodes Hbits) as Hprobe.
          fold F in Hprobe.
          destruct (advance_nodes p ixs lvl ns c) as [nodes|] eqn:Hstep.
          + pose proof (advance_nodes_ok p ixs lvl pre ns c nodes Hnodes Hstep) as Hnext.
            pose proof (IH p ixs (S lvl) (c :: pre) nodes out ltac:(lia) Hnext) as Hsubtree.
            fold F in Hsubtree. lia.
          + lia.
        - rewrite fold_sum_nat_affine. reflexivity. }
      rewrite Hdegree in Hchildren_time.
      assert (Hcolumn_count : (1 <= N.of_nat (length (cols p)))%N) by lia.
      pose proof (join_level_budget F (N.of_nat (length (cols p)))
        (N.of_nat (length children)) I.c_ix Hfactor Hcolumn_count Hindex) as Hbudget.
      cbn [recursive_work]. rewrite Hchoose, Hdegree. fold children branch_work.
      time_unfold T_enumerate. rewrite Hlength, Hchoose. fold children.
      clear IH. clearbody F children branch_work.
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul, ?Nat2N.inj_succ in *. nia.
  Qed.

  Definition c_join : N := (4096 * (I.c_ix + 1))%N.

  (** The public coefficient and dimensions are the common recursive factor. *)
  Lemma join_factor_equation : forall p ixs n,
    (c_join * N.of_nat n * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)) =
      4096 * scan_factor p ixs * N.of_nat n)%N.
  Proof.
    intros p ixs n. unfold c_join, scan_factor. ring.
  Qed.

  Lemma T_run_le : forall p ixs, wf_plan p ixs ->
    (T_run p ixs <= c_join * N.of_nat (work p ixs + length ixs + 2) * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)))%N.
  Proof.
    intros p ixs Hwf.
    pose proof (T_enumerate_le (nvars p) p ixs 0 [] (map I.root ixs) []
      ltac:(lia) (nodes_ok_initial p ixs Hwf)) as Henumerate.
    change (T_enumerate (nvars p) p ixs (map I.root ixs) [] [] <=
      4096 * scan_factor p ixs * N.of_nat (work p ixs))%N in Henumerate.
    pose proof (T_run_initial_le p ixs) as Hinitial.
    destruct (scan_factor_covers p ixs) as [Hfactor [Hindex _]].
    rewrite join_factor_equation.
    rewrite ?Nat2N.inj_add in *. nia.
  Qed.

  Lemma run_bigO : bigO (fun x : jplan * list I.t => wf_plan (fst x) (snd x))
    (fun x => N.of_nat ((work (fst x) (snd x) + length (snd x) + 2) *
      (wmax (fst x) (snd x) + 1) * ((nvars (fst x) + 1) * (nvars (fst x) + 1))))
    (fun x => T_run (fst x) (snd x)).
  Proof. Admitted. (* STUB *)

  Definition advance (p : jplan) (ixs : list I.t) (lvl : nat) (ns : list positive)
      (c : cell V.t) : option (list positive) := advance_nodes p ixs lvl ns c.
  TimeFun advance.
  Definition go (fuel : nat) (p : jplan) (ixs : list I.t) (ns : list positive)
      (pre : list (cell V.t)) (acc : list (list (cell V.t))) :=
    enumerate fuel p ixs ns pre acc.
  TimeFun go.
  Definition work_at (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) : nat := recursive_work (nvars p - lvl) p ixs lvl ns.
  Definition choose (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) : option nat := choose_index p ixs lvl ns.
  TimeFun choose.
  Lemma choose_min : forall p ixs l pre ns j, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j ->
    In j (participants p l) /\ forall k, In k (participants p l) ->
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) <=
       I.degree (nth k ixs I.empty) (nth k ns 1%positive))%N /\
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) =
       I.degree (nth k ixs I.empty) (nth k ns 1%positive) -> j <= k).
  Proof.
    intros p ixs l pre ns j Hnodes _ Hchoose.
    eapply choose_index_min; eassumption.
  Qed.

  Lemma choose_some : forall p ixs l pre ns, nodes_ok p ixs l pre ns ->
    l < nvars p -> exists j, choose p ixs l ns = Some j.
  Proof.
    intros p ixs l pre ns Hnodes Hlevel.
    exact (choose_index_some p ixs l pre ns Hnodes Hlevel).
  Qed.

  Lemma nodes_ok_root : forall p ixs, wf_plan p ixs ->
    nodes_ok p ixs 0 [] (map I.root ixs).
  Proof.
    exact nodes_ok_initial.
  Qed.

  Lemma step_ok : forall p ixs l pre ns c ns', wf_plan p ixs ->
    nodes_ok p ixs l pre ns -> advance p ixs l ns c = Some ns' ->
    nodes_ok p ixs (S l) (c :: pre) ns'.
  Proof.
    intros p ixs l pre ns c ns' _ Hnodes Hstep.
    eapply advance_nodes_ok; eassumption.
  Qed.

  Lemma advance_none : forall p ixs l pre ns c, wf_plan p ixs ->
    nodes_ok p ixs l pre ns -> advance p ixs l ns c = None ->
    forall b, firstn (S l) b = rev (c :: pre) -> ~ answer p ixs b.
  Proof.
    intros p ixs l pre ns c _ Hnodes Hnone b Hprefix Hanswer.
    destruct (advance_nodes_complete p ixs l pre ns c b Hnodes Hanswer Hprefix)
      as [ns' Hsome].
    unfold advance in Hnone. congruence.
  Qed.

  Lemma go_sound : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns ->
    In b (go (nvars p - l) p ixs ns pre acc) ->
    In b acc \/ (answer p ixs b /\ firstn l b = rev pre).
  Proof.
    intros p ixs l pre ns acc b Hnodes Hin.
    eapply enumerate_sound; [|exact Hnodes|exact Hin].
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel. lia.
  Qed.

  Lemma go_complete : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns ->
    answer p ixs b -> firstn l b = rev pre ->
    In b (go (nvars p - l) p ixs ns pre acc).
  Proof.
    intros p ixs l pre ns acc b Hnodes Hanswer Hprefix.
    eapply enumerate_complete; [|exact Hnodes|exact Hanswer|exact Hprefix].
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel. lia.
  Qed.

  Lemma go_nodup : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    NoDup acc ->
    (forall b, answer p ixs b -> firstn l b = rev pre -> ~ In b acc) ->
    NoDup (go (nvars p - l) p ixs ns pre acc).
  Proof.
    intros p ixs l pre ns acc Hnodes Hacc Hfresh.
    eapply enumerate_nodup; [|exact Hnodes|exact Hacc|exact Hfresh].
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel. lia.
  Qed.

  Lemma work_root : forall p ixs,
    work p ixs = work_at p ixs 0 (map I.root ixs).
  Proof.
    intros p ixs. unfold work, work_at. now rewrite Nat.sub_0_r.
  Qed.

  Lemma work_at_done : forall p ixs l ns, nvars p <= l ->
    work_at p ixs l ns = 1 + nvars p.
  Proof.
    intros p ixs l ns Hdone. unfold work_at.
    replace (nvars p - l) with 0 by lia. reflexivity.
  Qed.

  Lemma work_at_step : forall p ixs l pre ns j, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j ->
    work_at p ixs l ns = 1 + length (cols p) + length (cols p) *
      (1 + N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive))) +
      fold_right Nat.add 0
        (map (fun c => match advance p ixs l ns c with
          | None => 0
          | Some ns' => work_at p ixs (S l) ns'
          end) (I.children (nth j ixs I.empty) (nth j ns 1%positive))).
  Proof.
    intros p ixs l pre ns j _ Hlevel Hchoose.
    unfold work_at. replace (nvars p - l) with (S (nvars p - S l)) by lia.
    cbn [recursive_work]. unfold choose in Hchoose. now rewrite Hchoose.
  Qed.

  Lemma run_go : forall p ixs,
    run p ixs = go (nvars p) p ixs (map I.root ixs) [] [].
  Proof.
    reflexivity.
  Qed.

  Lemma T_go_le : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    (T_go (nvars p - l) p ixs ns pre acc <=
      c_join * N.of_nat (work_at p ixs l ns + 1) * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)))%N.
  Proof.
    intros p ixs l pre ns acc Hnodes.
    pose proof (proj1 (proj2 (proj2 Hnodes))) as Hlevel.
    pose proof (T_enumerate_le (nvars p - l) p ixs l pre ns acc ltac:(lia) Hnodes)
      as Henumerate.
    destruct (scan_factor_covers p ixs) as [Hfactor _].
    rewrite join_factor_equation. unfold work_at.
    time_unfold T_go. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Root initialization pays for every supplied index. *)
  Lemma T_run_go : forall p ixs, wf_plan p ixs ->
    (T_run p ixs <= T_go (nvars p) p ixs (map I.root ixs) [] [] +
      c_join * N.of_nat (length ixs + 1) * N.of_nat (wmax p ixs + 1))%N.
  Proof.
    intros p ixs _.
    pose proof (T_run_initial_le p ixs) as Hinitial.
    assert (Hwidth : (1 <= N.of_nat (wmax p ixs + 1))%N) by lia.
    assert (Hroot_budget : (4 * (I.c_ix + 1) * N.of_nat (length ixs + 1) <=
      c_join * N.of_nat (length ixs + 1) * N.of_nat (wmax p ixs + 1))%N).
    { unfold c_join. eapply N.le_trans with
        (m := (4096 * (I.c_ix + 1) * N.of_nat (length ixs + 1))%N).
      - apply N.mul_le_mono_r. apply N.mul_le_mono_r. lia.
      - rewrite <- N.mul_1_r at 1. apply N.mul_le_mono_l. exact Hwidth. }
    time_unfold T_go. lia.
  Qed.

End JoinT.
