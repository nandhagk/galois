(** * Tagged word payloads

    Tags attach widths to payloads and represent bottom and top.
    For example, joining values of different widths produces top.
    Builds on: WordSig and BitsLang. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Time Std BigO.
From Galois.Bits Require Import Word.
From Galois.Domains Require Import LangSig WordSig HarnessSig Harness BitsLang.

Module TaggedCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    <: HARNESS_BASE_OPS BitsLangCode.
  Definition t := tagged W.p.
  Definition bot : t := TBot.
  Definition top : t := TAny.
  Definition is_bot (a : t) : bool :=
    match a with
    | TBot => true
    | TVal w p => W.pis_bot w p
    | TAny => false
    end.
  Definition leb (a b : t) : bool :=
    match a, b with
    | TBot, _ => true
    | _, TAny => true
    | TVal w p, TVal v q =>
      if Pos.eqb w v then W.pleb w p q else W.pis_bot w p
    | TVal w p, TBot => W.pis_bot w p
    | _, _ => false
    end.
  Definition join (a b : t) : t :=
    if is_bot a then b else if is_bot b then a else
    match a, b with
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pjoin w p q) else TAny
    | _, _ => TAny
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | TBot, _ | _, TBot => TBot
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pmeet w p q) else TBot
    end.
  Definition wparam := W.pwparam.
  Definition widen (q : wparam) (a b : t) : t :=
    if leb b a then a else
    match a, b with
    | TBot, _ => b
    | TVal w p, TVal v r =>
      if W.pis_bot w p then b else
      if Pos.eqb w v then TVal w (W.pwiden q w p r) else TAny
    | _, _ => TAny
    end.
  Definition narrow (a b : t) : t :=
    match a, b with
    | TAny, _ => b
    | _, TAny => a
    | TVal w p, TVal v q => if Pos.eqb w v then TVal w (W.pnarrow w p q) else TBot
    | _, _ => TBot
    end.
  Definition point (a : t) : option BitsLangCode.val :=
    match a with
    | TVal w p => match W.ppoint w p with Some z => Some (w, z) | None => None end
    | _ => None
    end.
  Definition abst (v : BitsLangCode.val) : t :=
    if Z.eqb (Word.wrap (fst v) (snd v)) (snd v)
    then TVal (fst v) (W.pconst (fst v) (snd v)) else TAny.
End TaggedCode.

Module TaggedTableCode (L : WORD_LANGUAGE_OPS) (W : WORD_PAYLOAD_OPS L)
    (T : WORD_TABLE_OPS L W).
  Fixpoint untag (xs : list (tagged W.p)) : option (list (positive * W.p)) :=
    match xs with
    | nil => Some nil
    | TVal w p :: rest =>
      match untag rest with
      | Some ws => Some ((w, p) :: ws)
      | None => None
      end
    | _ => None
    end.

  Fixpoint retag (ws : list positive) (ps : list W.p) : list (tagged W.p) :=
    match ws, ps with
    | w :: rest, p :: tail => TVal w p :: retag rest tail
    | _, _ => nil
    end.

  Definition fwd (o : BitsLangCode.op) (xs : list (tagged W.p)) : option (tagged W.p) :=
    match o with
    | BConst w z =>
      match xs with nil => Some (TVal w (W.pconst w z)) | _ => None end
    | BOp o =>
      match untag xs with
      | Some ws =>
        match Op.result_width o (map fst ws) with
        | Some w => match T.wfwd o w ws with Some p => Some (TVal w p) | None => None end
        | None => None
        end
      | None => None
      end
    end.

  Definition bwd (o : BitsLangCode.op) (r : tagged W.p) (xs : list (tagged W.p))
      : option (list (tagged W.p)) :=
    match o, r, untag xs with
    | BOp o, TVal w p, Some ws =>
      match Op.result_width o (map fst ws) with
      | Some rw =>
        if Pos.eqb w rw then
          match T.wbwd o w p ws with
          | Some ps => Some (retag (map fst ws) ps)
          | None => None
          end
        else None
      | None => None
      end
    | _, _, _ => None
    end.

  Definition grd (_ : BitsLangCode.guard) (_ : list (tagged W.p))
      : option (list (tagged W.p)) := None.
End TaggedTableCode.

Definition tagged_gamma {P : Type} (is_word : positive -> Z -> Prop)
    (pgamma : positive -> P -> Z -> Prop) (a : tagged P) (c : BitsLang.val) : Prop :=
  match a with
  | TBot => False
  | TAny => True
  | TVal w p => fst c = w /\ is_word w (snd c) /\ pgamma w p (snd c)
  end.

Module Type TAGGED_BASE (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) :=
  HARNESS_BASE BitsLang with Definition t := tagged W.p
    with Definition gamma := tagged_gamma L.is_word W.pgamma.

Module Tagged (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) <: HARNESS_BASE BitsLang.
  Include TaggedCode L W.
  Definition gamma := tagged_gamma L.is_word W.pgamma.
  Definition wrank (q : wparam) (a : t) : nat :=
    match a with
    | TBot | TAny => 0
    | TVal w p => S (W.pwrank q w p)
    end.
  Lemma leb_refl : forall a, leb a a = true.
  Proof.
    intros [|w p|]; cbn [leb]; try reflexivity.
    rewrite Pos.eqb_refl. apply W.pleb_refl.
  Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* CONVERT: tagged_laws: The variable v was not found. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. intros []; reflexivity. Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* CONVERT: tagged_laws: Found no subterm matching "(?M1523 =? ?M1523)%positive" *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* CONVERT: tagged_laws: Found no subterm matching "(?M1523 =? ?M1523)%positive" *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.
  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted. (* CONVERT: tagged_meet_lower: The variable tagged_val_lower was not found in the current *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.
  Lemma widen_ub_l : forall q a b, leb a (widen q a b) = true.
  Proof. Admitted. (* CONVERT: tagged_laws: In environment *)
  Lemma widen_ub_r : forall q a b, leb b (widen q a b) = true.
  Proof. Admitted. (* CONVERT: tagged_laws: Found no subterm matching "(?M1523 =? ?M1523)%positive" *)
  Lemma widen_stable : forall q a b, leb b a = true -> widen q a b = a.
  Proof. Admitted.
  Lemma wrank_widen : forall q a b, is_bot a = false -> leb b a = false ->
    (wrank q (widen q a b) < wrank q a)%nat.
  Proof. Admitted.
  Lemma wrank_widen_le : forall q a b, is_bot a = false -> (wrank q (widen q a b) <= wrank q a)%nat.
  Proof. Admitted.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* CONVERT: tagged_laws: The variable w was not found in the current environment. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted. (* CONVERT: tagged_numeric_laws: The variable tagged_lattice was not found in the current environment. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. intros c Hg. exact Hg. Qed.
  Lemma gamma_top : forall c, gamma top c.
  Proof. Admitted.
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof. Admitted. (* CONVERT: tagged_meet_sound: The variable tagged_val_sound was not found in the current *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof. Admitted. (* CONVERT: tagged_empty_false: The relation (fun (x : tagged W.p) (y : width * Z) => ~ gamma x y) is not a declared reflexive relation. Maybe you need to require the Corelib.Classes.RelationClasses library *)
  (** Every value below a recognized bottom is recognized as bottom. *)
  Lemma is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  Proof. Admitted.
  Lemma point_sound : forall a v c, point a = Some v -> gamma a c -> c = v.
  Proof.
    intros [|w p|] [v x] [u z] Hpoint Hgamma; cbn in Hpoint; try discriminate.
    destruct (W.ppoint w p) as [value|] eqn:Hpayload; [|discriminate].
    inversion Hpoint; subst v x.
    destruct Hgamma as [Hwidth [Hword Hpayload_gamma]]. cbn in Hwidth. subst u.
    f_equal. exact (W.ppoint_sound w p z value Hpayload Hword Hpayload_gamma).
  Qed.
  Lemma abst_sound : forall v, gamma (abst v) v.
  Proof. Admitted. (* CONVERT: tagged_numeric_laws: No product even after head-reduction. *)
End Tagged.

Module TaggedTimingHelpers (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L).
  Include Tagged L W.
  TimeFun bot.
  TimeFun top.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun point.
  TimeFun abst.

End TaggedTimingHelpers.

Module TaggedTable (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) (T : WORD_TABLE L W)
    (B : TAGGED_BASE L W) <: TABLE BitsLang B.
  Include TaggedTableCode L W T.

  Lemma fwd_sound : forall o xs cs c r, fwd o xs = Some r ->
    Forall2 B.gamma xs cs -> BitsLang.eval o cs = Some c -> B.gamma r c.
  Proof. Admitted. (* CONVERT: tagged_forward_sound: The variable tagged_no_empty was not found in the current environment. *)

  Lemma bwd_sound : forall o r xs ys cs c, bwd o r xs = Some ys ->
    Forall2 B.gamma xs cs -> BitsLang.eval o cs = Some c -> B.gamma r c ->
    Forall2 B.gamma ys cs.
  Proof. Admitted. (* CONVERT: tagged_assume_sound: The variable tagged_empty_false was not found in the current *)

  Lemma grd_sound : forall g xs ys cs, grd g xs = Some ys ->
    Forall2 B.gamma xs cs -> BitsLang.holds g cs -> Forall2 B.gamma ys cs.
  Proof. Admitted.
End TaggedTable.

Module TaggedTableTimingHelpers (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W).
  Include TaggedTableCode L W T.
  TimeFun untag.
  TimeFun retag.
  TimeFun fwd.
  TimeFun bwd.
  TimeFun grd.
End TaggedTableTimingHelpers.

Module TaggedWordPlan (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W) <: WORD_PLAN L W T.
  Include TaggedTableCode L W T.
  TimeFun untag.
  TimeFun retag.

  Definition tagged_wrank (q : W.pwparam) (a : tagged W.p) : nat :=
    match a with
    | TBot | TAny => 0
    | TVal w p => 1 + W.pwrank q w p
    end.
  Definition k_untag : N := 1%N. (* STUB *)
  Definition k_retag : N := 1%N. (* STUB *)
  Definition tagged_gamma (a : tagged W.p) (c : positive * Z) : Prop :=
    match a with
    | TBot => False
    | TAny => True
    | TVal w p => fst c = w /\ L.is_word w (snd c) /\ W.pgamma w p (snd c)
    end.
  Lemma F1_untag_sound : forall xs cs wps,
    Forall2 tagged_gamma xs cs -> untag xs = Some wps ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs.
  Proof. Admitted. (* STUB *)
  Lemma F2_retag_sound : forall ws ps cs,
    Forall2 (fun w c => fst c = w /\ L.is_word w (snd c)) ws cs ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c)) (combine ws ps) cs ->
    length ps = length ws -> Forall2 tagged_gamma (retag ws ps) cs.
  Proof. Admitted. (* STUB *)
  Lemma T1_untag : forall xs,
    (T_untag xs <= k_untag * N.of_nat ((length xs + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_retag : forall ws ps,
    (T_retag ws ps <= k_retag * N.of_nat ((length ws + length ps + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
End TaggedWordPlan.

Module WordDomain (L : WORD_LANGUAGE) (W : WORD_PAYLOAD L) (T : WORD_TABLE L W).
  Module B := Tagged L W.
  Module Table := TaggedTable L W T B.
  Module Domain := Harness BitsLang B Table.
End WordDomain.
