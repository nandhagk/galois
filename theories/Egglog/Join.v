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

  Definition nodes_ok (p : jplan) (ixs : list I.t) (lvl : nat)
      (pre : list (cell V.t)) (ns : list positive) : Prop :=
    wf_plan p ixs /\ length pre = lvl /\ lvl <= nvars p /\
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) (rev pre) = Some u /\
      I.node (snd lvix) n u) (combine (cols p) ixs) ns.
  Definition advance (p : jplan) (ixs : list I.t) (lvl : nat) (ns : list positive)
      (c : cell V.t) : option (list positive) := advance_nodes p ixs lvl ns c.
  TimeFun advance.
  Definition go (fuel : nat) (p : jplan) (ixs : list I.t) (ns : list positive)
      (pre : list (cell V.t)) (acc : list (list (cell V.t))) :=
    enumerate fuel p ixs ns pre acc.
  TimeFun go.
  Definition work_at (p : jplan) (ixs : list I.t) (lvl : nat)
      (ns : list positive) : nat := recursive_work (nvars p - lvl) p ixs lvl ns.
  Definition participants (p : jplan) (lvl : nat) : list nat :=
    filter (fun j => existsb (Nat.eqb lvl) (nth j (cols p) []))
      (seq 0 (length (cols p))).
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
  Proof. Admitted. (* STUB *)

  Lemma choose_some : forall p ixs l pre ns, nodes_ok p ixs l pre ns ->
    l < nvars p -> exists j, choose p ixs l ns = Some j.
  Proof. Admitted. (* STUB *)

  Lemma nodes_ok_root : forall p ixs, wf_plan p ixs ->
    nodes_ok p ixs 0 [] (map I.root ixs).
  Proof. Admitted. (* STUB *)

  Lemma step_ok : forall p ixs l pre ns c ns', wf_plan p ixs ->
    nodes_ok p ixs l pre ns -> advance p ixs l ns c = Some ns' ->
    nodes_ok p ixs (S l) (c :: pre) ns'.
  Proof. Admitted. (* STUB *)

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
