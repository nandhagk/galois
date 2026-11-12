(** * Flat constant domain code

    Flat values distinguish bottom, one value and top.
    For example, joining distinct singleton values returns top.
    Builds on: ConstSig and the concrete language operations. *)

From Stdlib Require Import List ZArith Bool.
From Galois.Bits Require Import Word Fun Op.
From Galois.Domains Require Import ConstSig LangSig WordSig.
Import List.ListNotations.

Module ConstCode (L : LANG_OPS) (E : VAL_EQ_OPS L) <: CONST_OPS L E.
  Definition t := flat L.val.
  Definition wparam := unit.
  Definition leb (a b : t) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => E.eqb x y
    | _, _ => false
    end.
  Definition bot : t := FBot.
  Definition top : t := FTop.
  Definition is_bot (a : t) := match a with FBot => true | _ => false end.
  Definition join (a b : t) : t :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if E.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition meet (a b : t) : t :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if E.eqb x y then a else FBot
    end.
  Definition widen (_ : unit) (a b : t) := join a b.
  Definition narrow (a _ : t) := a.
  Definition point (a : t) := match a with FVal x => Some x | _ => None end.
  Definition abst (v : L.val) : t := FVal v.
  Fixpoint points (xs : list t) : option (list L.val) :=
    match xs with
    | [] => Some []
    | FVal x :: rest =>
      match points rest with
      | Some vs => Some (x :: vs)
      | None => None
      end
    | _ => None
    end.
  Definition forward (o : L.op) (xs : list t) : t :=
    if existsb is_bot xs then FBot else
      match points xs with
      | Some vs => match L.eval o vs with Some v => FVal v | None => FBot end
      | None => FTop
      end.
  Definition backward (_ : L.op) (_ : t) (xs : list t) := xs.
  Definition guard (_ : L.guard) (xs : list t) := xs.
End ConstCode.

Module ConstWordCode (L : WORD_LANGUAGE_OPS)
    <: (WORD_PAYLOAD_OPS L with Definition p := flat Z).
  Definition p := flat Z.
  Definition pleb (_ : positive) (a b : p) : bool :=
    match a, b with
    | FBot, _ => true
    | _, FTop => true
    | FVal x, FVal y => Z.eqb x y
    | _, _ => false
    end.
  Definition pjoin (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ => b
    | _, FBot => a
    | FVal x, FVal y => if Z.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition pmeet (_ : positive) (a b : p) : p :=
    match a, b with
    | FBot, _ | _, FBot => FBot
    | FTop, _ => b
    | _, FTop => a
    | FVal x, FVal y => if Z.eqb x y then a else FBot
    end.
  Definition pbot (_ : positive) : p := FBot.
  Definition ptop (_ : positive) : p := FTop.
  Definition pis_bot (_ : positive) (a : p) :=
    match a with FBot => true | _ => false end.
  Definition pconst (w : positive) (z : Z) : p := FVal (L.wrap w z).
  Definition ppoint (_ : positive) (a : p) : option Z :=
    match a with FVal z => Some z | _ => None end.
  Definition pwparam := unit.
  Definition pwiden (_ : pwparam) w a b := pjoin w a b.
  Definition pnarrow w a b := pmeet w a b.
End ConstWordCode.

Module ConstWordTableCode (L : WORD_LANGUAGE_OPS)
    (W : WORD_PAYLOAD_OPS L with Definition p := flat Z) <: WORD_TABLE_OPS L W.
  Definition const_is (a : flat Z) (z : Z) :=
    match a with FVal x => Z.eqb x z | _ => false end.
  Definition shortcut (o : L.op) (a b : positive * W.p) : option Z :=
    match o with
    | bvmul | bvand =>
      if const_is (snd a) 0 || const_is (snd b) 0 then Some 0 else None
    | bvor =>
      if const_is (snd a) (modulus (fst a) - 1) ||
         const_is (snd b) (modulus (fst a) - 1)
      then Some (modulus (fst a) - 1) else None
    | bvshl | bvlshr | bvashr | bvurem =>
      if const_is (snd a) 0 then Some 0 else None
    | _ => None
    end%Z.
  Definition inverse (f : Z -> Z) (a : flat Z) : flat Z :=
    match a with FVal z => FVal (f z) | _ => FTop end.
  Definition inverse_pair w (f g : Z -> Z) (a b : W.p) :=
    [W.pmeet w a (inverse f b); W.pmeet w b (inverse g a)].
  Definition backward_one o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(_, a)], FVal r =>
      [W.pmeet rw a (FVal (match o with bvnot => wnot rw r | _ => wneg rw r end))]
    | _, _ => map snd xs
    end.
  Definition backward_two o rw (q : W.p) (xs : list (positive * W.p)) :=
    match xs, q with
    | [(w, a); (_, b)], FVal r =>
      match o with
      | bveq => if Z.eqb r 1 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvne => if Z.eqb r 0 then [W.pmeet rw a b; W.pmeet rw b a] else [a; b]
      | bvadd => inverse_pair rw (fun z => wsub w r z) (fun z => wsub w r z) a b
      | bvsub => inverse_pair rw (fun z => wadd w r z) (fun z => wsub w z r) a b
      | bvxor => inverse_pair rw (fun z => wxor w r z) (fun z => wxor w r z) a b
      | _ => [a; b]
      end
    | _, _ => map snd xs
    end%Z.
  Definition wfwd o (_ : positive) (xs : list (positive * W.p)) : option W.p :=
    match o, xs with
    | (bvmul | bvand | bvor | bvshl | bvlshr | bvashr | bvurem), [a; b] =>
      Some (match shortcut o a b with Some c => FVal c | None => FTop end)
    | _, _ => None
    end.
  Definition wbwd o rw q (xs : list (positive * W.p)) : option (list W.p) :=
    match o, xs with
    | (bvnot | bvneg), [_] => Some (backward_one o rw q xs)
    | (bveq | bvne | bvadd | bvsub | bvxor), [_; _] => Some (backward_two o rw q xs)
    | _, _ => None
    end.
End ConstWordTableCode.

Local Close Scope Z_scope.

Module Const (L : LANG) (E : VAL_EQ L) <: CONST L E.
  Include ConstCode L E.
  Include CONST_SPEC L E.
  Definition gamma := flat_gamma.
  Definition wrank (_ : wparam) (a : t) : nat := 2 - level a.
  Lemma leb_refl : forall a, leb a a = true.
  Proof. Admitted.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted.

  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted.

  Lemma meet_lb_l : forall a b, leb (meet a b) a = true.
  Proof. Admitted.
  (** Meet is below its right operand. *)
  Lemma meet_lb_r : forall a b, leb (meet a b) b = true.
  Proof. Admitted.

  (** Widening is above its previous value. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted.
  (** Widening is above its candidate value. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted.
  (** A candidate below the previous value leaves widening unchanged. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted.
  (** An unstable widening from a nonbottom strictly decreases rank. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted.
  (** Widening from a nonbottom does not increase rank. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted.
  (** Narrowing stays between an ordered candidate and previous value. *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted.

  (** Abstract inclusion entails concrete inclusion. *)
  Lemma gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  Proof. Admitted.
  (** Bottom describes no concrete value. *)
  Lemma gamma_bot : forall c, ~ gamma bot c.
  Proof. Admitted.
  (** Top describes every concrete value. *)
  Lemma gamma_top : forall c, gamma top c.
  Proof. Admitted.
  (** Meet retains values described by both operands. *)
  Lemma gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  Proof. Admitted.
  (** A positive bottom test excludes every concrete value. *)
  Lemma is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  Proof. Admitted.
  (** Forward transfer contains every successful concrete result. *)
  Lemma forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  Proof. Admitted.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Lemma backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  Proof. Admitted.
  (** Backward transfer refines each operand in its original position. *)
  Lemma backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  Proof. Admitted.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Lemma guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  Proof. Admitted.
  (** Guard transfer refines each operand in its original position. *)
  Lemma guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
  Proof. Admitted.
End Const.

Module ConstWord (L : WORD_LANGUAGE) <: CONST_WORD_PAYLOAD L.
  Include ConstWordCode L.
  Definition pgamma (_ : positive) (a : p) (z : Z) : Prop :=
    match a with FBot => False | FVal x => z = x | FTop => True end.
  Definition pwrank (_ : pwparam) (_ : positive) (a : p) : nat :=
    match a with FBot => 2 | FVal _ => 1 | FTop => 0 end.
  (** Widening contains both payloads. *)
  Lemma pwiden_ub_l : forall q w a b, pleb w a (pwiden q w a b) = true.
  Proof. Admitted.
  Lemma pwiden_ub_r : forall q w a b, pleb w b (pwiden q w a b) = true.
  Proof. Admitted.
  (** Stable widening retains the previous payload. *)
  Lemma pwiden_stable : forall q w a b, pleb w b a = true -> pwiden q w a b = a.
  Proof. Admitted.
  (** An unstable nonbottom widening strictly lowers the rank. *)
  Lemma pwrank_widen : forall q w a b, pis_bot w a = false -> pleb w b a = false ->
    (pwrank q w (pwiden q w a b) < pwrank q w a)%nat.
  Proof. Admitted.
  (** Nonbottom widening does not increase rank. *)
  Lemma pwrank_widen_le : forall q w a b, pis_bot w a = false ->
    (pwrank q w (pwiden q w a b) <= pwrank q w a)%nat.
  Proof. Admitted.
  (** Narrowing lies between ordered inputs. *)
  Lemma pnarrow_between : forall w a b, pleb w b a = true ->
    pleb w b (pnarrow w a b) = true /\ pleb w (pnarrow w a b) a = true.
  Proof. Admitted.
  (** Width-specific inclusion is reflexive. *)
  Lemma pleb_refl : forall w a, pleb w a a = true.
  Proof. Admitted.
  (** Width-specific inclusion is transitive. *)
  Lemma pleb_trans : forall w a b c,
    pleb w a b = true -> pleb w b c = true -> pleb w a c = true.
  Proof. Admitted.
  (** Bottom is below every payload. *)
  Lemma pbot_least : forall w a, pleb w (pbot w) a = true.
  Proof. Admitted.
  (** Top is above every payload. *)
  Lemma ptop_greatest : forall w a, pleb w a (ptop w) = true.
  Proof. Admitted.
  (** The bottom test recognizes bottom. *)
  Lemma pis_bot_bot : forall w, pis_bot w (pbot w) = true.
  Proof. Admitted.
  (** Recognized bottoms are below every payload. *)
  Lemma pis_bot_least : forall w a b, pis_bot w a = true -> pleb w a b = true.
  Proof. Admitted.
  (** Join contains the left payload. *)
  Lemma pjoin_ub_l : forall w a b, pleb w a (pjoin w a b) = true.
  Proof. Admitted.
  (** Join contains the right payload. *)
  Lemma pjoin_ub_r : forall w a b, pleb w b (pjoin w a b) = true.
  Proof. Admitted.
  (** Meet refines the left payload. *)
  Lemma pmeet_lb_l : forall w a b, pleb w (pmeet w a b) a = true.
  Proof. Admitted.
  (** Meet refines the right payload. *)
  Lemma pmeet_lb_r : forall w a b, pleb w (pmeet w a b) b = true.
  Proof. Admitted.
  (** Inclusion retains represented integers. *)
  Lemma pgamma_mono : forall w a b z,
    pleb w a b = true -> pgamma w a z -> pgamma w b z.
  Proof. Admitted.
  (** Bottom represents no integer. *)
  Lemma pgamma_bot : forall w z, ~ pgamma w (pbot w) z.
  Proof. Admitted.
  (** Top contains every normalized integer at its width. *)
  Lemma ptop_full : forall w z, L.is_word w z -> pgamma w (ptop w) z.
  Proof. Admitted.
  (** Meet retains every common integer. *)
  Lemma pgamma_meet : forall w a b z,
    pgamma w a z -> pgamma w b z -> pgamma w (pmeet w a b) z.
  Proof. Admitted.
  (** Recognized bottoms contain no integer. *)
  Lemma pis_bot_sound : forall w a z, pis_bot w a = true -> ~ pgamma w a z.
  Proof. Admitted.
  (** A constant payload contains the wrapped integer. *)
  Lemma pconst_sound : forall w z, pgamma w (pconst w z) (L.wrap w z).
  Proof. Admitted.
  (** A recognized point identifies all represented integers. *)
  Lemma ppoint_sound : forall w a z v,
    ppoint w a = Some v -> pgamma w a z -> z = v.
  Proof. Admitted.
End ConstWord.

Module ConstWordTable (L : WORD_LANGUAGE) (W : CONST_WORD_PAYLOAD L) <: CONST_WORD_TABLE L W.
  Include ConstWordTableCode L W.
  (** A forward word entry retains each concrete result at its checked width. *)
  Lemma wfwd_sound : forall o rw wps cs z r, wfwd o rw wps = Some r ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw r z.
  Proof. Admitted.
  (** A backward word entry retains each concrete operand in its original position. *)
  Lemma wbwd_sound : forall o rw q wps ys cs z, wbwd o rw q wps = Some ys ->
    Forall2 (fun wp c => fst wp = fst c /\ L.is_word (fst c) (snd c) /\
      W.pgamma (fst wp) (snd wp) (snd c)) wps cs ->
    L.eval_op o cs = Some (rw, z) -> W.pgamma rw q z ->
    Forall2 (fun wp c => W.pgamma (fst wp) (snd wp) (snd c))
      (combine (map fst wps) ys) cs.
  Proof. Admitted.
End ConstWordTable.
