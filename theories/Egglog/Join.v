(** * Generic joins over live index prefixes

    Joins bind one variable at a time and probe every participating index.
    For example, two binary indexes can share their middle variable.
    Builds on: JoinSig and the index operations. *)

From Stdlib Require Import List PArith NArith Arith Sorting.Sorted Lia.
From Argent Require Import Time Tactics Std.
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

Module ListDef.
  TimeFun List.nth.
End ListDef.
Import ListDef.

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

  (** Both computations precede the result match, including when a probe fails. *)
  Fixpoint advance_columns (cs : list (list nat)) (ixs : list I.t) (lvl : nat)
      (ns : list positive) (c : cell V.t) : option (list positive) :=
    match cs, ixs, ns with
    | [], [], [] => Some []
    | lv :: rest, ix :: tail, n :: nodes =>
      let head := if existsb (Nat.eqb lvl) lv then I.child ix n c else Some n in
      let later := advance_columns rest tail lvl nodes c in
      match head, later with
      | Some m, Some ms => Some (m :: ms)
      | _, _ => None
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

  Lemma run_sound : forall p ixs b, wf_plan p ixs ->
    In b (run p ixs) -> answer p ixs b.
  Proof. Admitted. (* STUB *)

  Lemma run_complete : forall p ixs b, wf_plan p ixs ->
    answer p ixs b -> In b (run p ixs).
  Proof. Admitted. (* STUB *)

  Lemma run_nodup : forall p ixs, wf_plan p ixs -> NoDup (run p ixs).
  Proof. Admitted. (* STUB *)

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

  Definition work (p : jplan) (ixs : list I.t) : nat :=
    recursive_work (nvars p) p ixs 0 (map I.root ixs).
  Definition wmax (_ : jplan) (ixs : list I.t) : nat :=
    fold_right (fun ix w => Nat.max (Pos.size_nat (I.next ix) + I.max_cell_bits ix) w)
      0 ixs.
  Definition c_join : N := 1. (* STUB *)
  Lemma T_run_le : forall p ixs, wf_plan p ixs ->
    (T_run p ixs <= c_join * N.of_nat (work p ixs + length ixs + 2) * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_run_ge : forall p ixs, wf_plan p ixs ->
    (N.of_nat (work p ixs) <= T_run p ixs)%N.
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
  Proof. Admitted. (* STUB *)

  Lemma go_nodup : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    NoDup acc ->
    (forall b, answer p ixs b -> firstn l b = rev pre -> ~ In b acc) ->
    NoDup (go (nvars p - l) p ixs ns pre acc).
  Proof. Admitted. (* STUB *)

  Lemma work_root : forall p ixs,
    work p ixs = work_at p ixs 0 (map I.root ixs).
  Proof. Admitted. (* STUB *)

  Lemma work_at_done : forall p ixs l ns, nvars p <= l ->
    work_at p ixs l ns = 1 + nvars p.
  Proof. Admitted. (* STUB *)

  Lemma work_at_step : forall p ixs l pre ns j, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j ->
    work_at p ixs l ns = 1 + length (cols p) + length (cols p) *
      (1 + N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive))) +
      fold_right Nat.add 0
        (map (fun c => match advance p ixs l ns c with
          | None => 0
          | Some ns' => work_at p ixs (S l) ns'
          end) (I.children (nth j ixs I.empty) (nth j ns 1%positive))).
  Proof. Admitted. (* STUB *)

  Lemma run_go : forall p ixs,
    run p ixs = go (nvars p) p ixs (map I.root ixs) [] [].
  Proof. Admitted. (* STUB *)

  Lemma T_go_le : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    (T_go (nvars p - l) p ixs ns pre acc <=
      c_join * N.of_nat (work_at p ixs l ns + 1) * N.of_nat (wmax p ixs + 1) *
      N.of_nat ((nvars p + 1) * (nvars p + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Root initialization pays for every supplied index. *)
  Lemma T_run_go : forall p ixs, wf_plan p ixs ->
    (T_run p ixs <= T_go (nvars p) p ixs (map I.root ixs) [] [] +
      c_join * N.of_nat (length ixs + 1) * N.of_nat (wmax p ixs + 1))%N.
  Proof. Admitted. (* STUB *)

End JoinT.
