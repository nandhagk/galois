(** * Generic joins over live index prefixes

    Joins bind one variable at a time and probe every participating index.
    For example, two binary indexes can share their middle variable.
    Builds on: JoinSig and the index operations. *)

From Stdlib Require Import List PArith NArith Arith Sorting.Sorted Lia.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig IndexSig Syntax JoinSig Index.

Import List.ListNotations.

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
  Proof. Admitted. (* STUB *)

  Lemma go_sound : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns ->
    In b (go (nvars p - l) p ixs ns pre acc) ->
    In b acc \/ (answer p ixs b /\ firstn l b = rev pre).
  Proof. Admitted. (* STUB *)

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
