(** * Width-tagged payloads

    Tags distinguish impossible values, fixed-width payloads and unrestricted values.
    For example, joining two different widths produces the unrestricted tag.
    Builds on: DomainsNumeric and CostList. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric.
Import List.ListNotations Cost.Notations.

(** Fixed-width values retain their payload's width independently of its representation. *)
Inductive tagged (P : Type) : Type :=
  | TBot
  | TVal (w : width) (p : P)
  | TAny.

Arguments TBot {P}.
Arguments TVal {P}.
Arguments TAny {P}.

(** Tagged operations call payload operations only for matching widths. *)
Definition tagged_lattice {P} (L : width -> lattice P) : lattice (tagged P) :=
  {| leb_c := fun a b => Cost.step ;;
       match a, b with
       | TBot, _ => Cost.ret true
       | _, TAny => Cost.ret true
       | TVal w p, TVal v q =>
         if Pos.eqb w v then Cost.step ;; leb_c (L w) p q else Cost.ret false
       | _, _ => Cost.ret false
       end;
     bot := TBot;
     join_c := fun a b => Cost.step ;;
       match a, b with
       | TBot, _ => Cost.ret b
       | _, TBot => Cost.ret a
       | TVal w p, TVal v q =>
         if Pos.eqb w v then Cost.step ;; Cost.map (TVal w) (join_c (L w) p q)
         else Cost.ret TAny
       | _, _ => Cost.ret TAny
       end;
     widen_c := fun a b => Cost.step ;;
       match a, b with
       | TBot, _ => Cost.ret b
       | _, TBot => Cost.ret a
       | TVal w p, TVal v q =>
         if Pos.eqb w v then Cost.step ;; Cost.map (TVal w) (widen_c (L w) p q)
         else Cost.ret TAny
       | _, _ => Cost.ret TAny
       end;
     narrow_c := fun a b => Cost.step ;;
       match a, b with
       | TVal w p, TVal v q =>
         if Pos.eqb w v then Cost.step ;; Cost.map (TVal w) (narrow_c (L w) p q)
         else Cost.ret a
       | _, _ => Cost.ret a
       end |}.

Local Lemma tagged_le {P} (L : width -> lattice P) a b :
  leb (tagged_lattice L) a b =
  match a, b with
  | TBot, _ => true
  | _, TAny => true
  | TVal w p, TVal v q => if Pos.eqb w v then leb (L w) p q else false
  | _, _ => false
  end.
Proof.
  destruct a, b; cbn; try reflexivity. destruct (Pos.eqb w w0); reflexivity.
Qed.

Local Lemma tagged_join {P} (L : width -> lattice P) a b :
  join (tagged_lattice L) a b =
  match a, b with
  | TBot, _ => b
  | _, TBot => a
  | TVal w p, TVal v q => if Pos.eqb w v then TVal w (join (L w) p q) else TAny
  | _, _ => TAny
  end.
Proof.
  destruct a, b; cbn; try reflexivity. destruct (Pos.eqb w w0); reflexivity.
Qed.

Local Lemma tagged_widen {P} (L : width -> lattice P) a b :
  widen (tagged_lattice L) a b =
  match a, b with
  | TBot, _ => b
  | _, TBot => a
  | TVal w p, TVal v q => if Pos.eqb w v then TVal w (widen (L w) p q) else TAny
  | _, _ => TAny
  end.
Proof.
  destruct a, b; cbn; try reflexivity. destruct (Pos.eqb w w0); reflexivity.
Qed.

Local Lemma tagged_narrow {P} (L : width -> lattice P) a b :
  narrow (tagged_lattice L) a b =
  match a, b with
  | TVal w p, TVal v q => if Pos.eqb w v then TVal w (narrow (L w) p q) else a
  | _, _ => a
  end.
Proof.
  destruct a, b; cbn; try reflexivity. destruct (Pos.eqb w w0); reflexivity.
Qed.

(** Width tagging preserves the weak laws without requiring least payload joins. *)
Theorem tagged_laws {P} (D : word_domain P) :
  (forall w, lattice_laws (plat D w)) -> lattice_laws (tagged_lattice (plat D)).
Proof.
  intro H. constructor.
  - intros [|w p|]; rewrite tagged_le; try reflexivity.
    rewrite Pos.eqb_refl. apply (leb_refl (H w)).
  - intros [|w p|] [|v q|] [|u r|]; rewrite !tagged_le;
      intros Hab Hbc; try discriminate; try reflexivity.
    destruct (Pos.eqb w v) eqn:Hwv; [|discriminate].
    destruct (Pos.eqb v u) eqn:Hvu; [|discriminate].
    apply Pos.eqb_eq in Hwv. apply Pos.eqb_eq in Hvu. subst v u.
    rewrite Pos.eqb_refl. exact (leb_trans (H w) p q r Hab Hbc).
  - intros []; reflexivity.
  - intros [|w p|] [|v q|]; rewrite tagged_join, tagged_le; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (H w)).
    + destruct (Pos.eqb_spec w v); subst; [|reflexivity].
      rewrite ?tagged_le, ?Pos.eqb_refl. apply (join_upper_l (H v)).
  - intros [|w p|] [|v q|]; rewrite tagged_join, tagged_le; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (H v)).
    + destruct (Pos.eqb_spec w v); subst; [|reflexivity].
      rewrite ?tagged_le, ?Pos.eqb_refl. apply (join_upper_r (H v)).
  - intros [|w p|] [|v q|]; rewrite tagged_widen, tagged_le; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (H w)).
    + destruct (Pos.eqb_spec w v); subst; [|reflexivity].
      rewrite ?tagged_le, ?Pos.eqb_refl. apply (widen_upper_l (H v)).
  - intros [|w p|] [|v q|]; rewrite tagged_widen, tagged_le; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (H v)).
    + destruct (Pos.eqb_spec w v); subst; [|reflexivity].
      rewrite ?tagged_le, ?Pos.eqb_refl. apply (widen_upper_r (H v)).
  - intros [|w p|] [|v q|]; rewrite tagged_narrow, !tagged_le;
      intro Hba; try discriminate; try reflexivity.
    + rewrite Pos.eqb_refl. apply (leb_refl (H w)).
    + destruct (Pos.eqb_spec v w); subst; [|discriminate].
      rewrite Pos.eqb_refl in *. rewrite ?tagged_le, ?Pos.eqb_refl.
      apply (narrow_lower (H w)), Hba.
  - intros [|w p|] [|v q|]; rewrite tagged_narrow, !tagged_le;
      intro Hba; try discriminate; try reflexivity.
    destruct (Pos.eqb_spec v w); subst; [|discriminate].
    rewrite Pos.eqb_refl in *. rewrite ?tagged_le, ?Pos.eqb_refl.
    apply (narrow_upper (H w)), Hba.
Qed.

(** Tagged meaning rejects bottom and enforces normalization at fixed widths. *)
Definition tagged_gamma {P} (G : width -> P -> Z -> Prop) : concretisation (tagged P) word :=
  {| gamma := fun t c =>
       match t with
       | TBot => False
       | TVal w p => fst c = w /\ is_word w (snd c) /\ G w p (snd c)
       | TAny => True
       end |}.

Definition tagged_val_c {P} (D : word_domain P) w p : Cost.t (tagged P) :=
  let* empty := Cost.step ;; leb_c (plat D w) p (bot (plat D w)) in
  Cost.ret (if empty then TBot else TVal w p).

Definition tagged_val {P} (D : word_domain P) w p := Cost.value (tagged_val_c D w p).

Definition tagged_empty_c {P} (D : word_domain P) (t : tagged P) : Cost.t bool :=
  match t with
  | TBot => Cost.ret true
  | TVal w p => Cost.step ;; leb_c (plat D w) p (bot (plat D w))
  | TAny => Cost.ret false
  end.

Fixpoint tagged_values_c {P} (xs : list (tagged P)) : Cost.t (option (list (width * P))) :=
  match xs with
  | [] => Cost.ret (Some [])
  | TVal w p :: xs =>
    Cost.step ;;
    Cost.map (fun tail =>
      match tail with Some tail => Some ((w, p) :: tail) | None => None end)
      (tagged_values_c xs)
  | _ :: _ => Cost.step ;; Cost.ret None
  end.

Fixpoint tagged_refine_c {P} (D : word_domain P) (xs : list (width * P)) (qs : list P)
    : Cost.t (list (tagged P)) :=
  match xs, qs with
  | (w, p) :: xs, q :: qs =>
    Cost.step ;;
    let* t := tagged_val_c D w q in
    Cost.map (cons t) (tagged_refine_c D xs qs)
  | (w, p) :: xs, [] =>
    Cost.step ;; Cost.map (cons (TVal w p)) (tagged_refine_c D xs [])
  | [], _ => Cost.ret []
  end.

Definition tagged_forward_c {P} (D : word_domain P) o xs : Cost.t (tagged P) :=
  let* empty := existsb_c (tagged_empty_c D) xs in
  if empty then Cost.ret TBot else
  let* wps := tagged_values_c xs in
  match wps with
  | None => Cost.ret TAny
  | Some wps =>
    let* ws := map_c (fun wp => Cost.ret (fst wp)) wps in
    match result_width o ws with
    | Some rw =>
      let* p := Cost.step ;; pforward_c D o wps rw in tagged_val_c D rw p
    | None => Cost.ret TBot
    end
  end.

Definition tagged_assume_c {P} (D : word_domain P) o a xs : Cost.t (list (tagged P)) :=
  let reject := fun xs => map_c (fun _ => Cost.ret TBot) xs in
  let* empty := tagged_empty_c D a in
  if empty then reject xs else
  let* wps := tagged_values_c xs in
  match a, wps with
  | TVal rw q, Some wps =>
    let* ws := map_c (fun wp => Cost.ret (fst wp)) wps in
    match result_width o ws with
    | Some rw' =>
      if Pos.eqb rw rw' then
        let* qs := Cost.step ;; passume_c D o wps rw q in tagged_refine_c D wps qs
      else reject xs
    | None => reject xs
    end
  | _, _ => Cost.ret xs
  end.

Definition tagged_meet_c {P} (D : word_domain P) (a b : tagged P) : Cost.t (tagged P) :=
  match a, b with
  | TBot, _ => Cost.ret TBot
  | _, TBot => Cost.ret TBot
  | TAny, TAny => Cost.ret TAny
  | TAny, TVal w p => tagged_val_c D w p
  | TVal w p, TAny => tagged_val_c D w p
  | TVal w p, TVal v q =>
    if Pos.eqb w v then
      let* r := Cost.step ;; pmeet_c D w p q in tagged_val_c D w r
    else Cost.ret TBot
  end.

(** Width tagging turns the payload dictionary into a numeric dictionary. *)
Definition tagged_domain {P} (D : word_domain P) : numeric_domain (tagged P) :=
  {| lat := tagged_lattice (plat D);
     top_at := fun w => TVal w (ptop D w);
     of_const_c := fun w z => Cost.step ;; Cost.map (TVal w) (pconst_c D w z);
     forward_c := tagged_forward_c D;
     assume_c := tagged_assume_c D;
     meet_c := tagged_meet_c D |}.

Local Lemma tagged_val_sound {P} (D : word_domain P) G :
  word_laws D G -> forall w p z, is_word w z -> G w p z ->
  gamma (tagged_gamma G) (tagged_val D w p) (w, z).
Proof.
  intros H w p z Hw Hp.
  change (gamma (tagged_gamma G)
    (if leb (plat D w) p (bot (plat D w)) then TBot else TVal w p) (w, z)).
  destruct (leb (plat D w) p (bot (plat D w))) eqn:Hbot; cbn.
  - exfalso. apply (pgamma_bot_empty H w z).
    exact (pgamma_monotone H w p _ z Hbot Hp).
  - auto.
Qed.

Local Lemma tagged_val_lower {P} (D : word_domain P) w p q :
  leb (plat D w) p q = true ->
  leb (tagged_lattice (plat D)) (tagged_val D w p) (TVal w q) = true.
Proof.
  intro H.
  change (leb (tagged_lattice (plat D))
    (if leb (plat D w) p (bot (plat D w)) then TBot else TVal w p) (TVal w q) = true).
  destruct (leb (plat D w) p (bot (plat D w))); rewrite tagged_le; [reflexivity|].
  now rewrite Pos.eqb_refl.
Qed.

Local Lemma tagged_empty_false {P} (D : word_domain P) G :
  word_laws D G -> forall t c, gamma (tagged_gamma G) t c ->
  Cost.value (tagged_empty_c D t) = false.
Proof.
  intros H [|w p|] [v z] Hg; cbn in Hg; try contradiction; [|reflexivity].
  destruct Hg as [Hvw [Hw Hp]]. subst v.
  change (leb (plat D w) p (bot (plat D w)) = false).
  destruct (leb (plat D w) p (bot (plat D w))) eqn:Hbot; [|reflexivity].
  exfalso. apply (pgamma_bot_empty H w z).
  exact (pgamma_monotone H w p _ z Hbot Hp).
Qed.

Local Lemma tagged_no_empty {P} (D : word_domain P) G :
  word_laws D G -> forall xs cs, Forall2 (gamma (tagged_gamma G)) xs cs ->
  existsb (fun x => Cost.value (tagged_empty_c D x)) xs = false.
Proof.
  intros H xs cs Hxs. induction Hxs as [|x c xs cs Hx Hxs IH]; cbn; [reflexivity|].
  rewrite (tagged_empty_false D G H x c Hx), IH. reflexivity.
Qed.

Local Lemma tagged_values_sound {P} G xs cs wps :
  Forall2 (gamma (tagged_gamma G)) xs cs ->
  Cost.value (@tagged_values_c P xs) = Some wps ->
  Forall2 (payload_sound G) wps cs.
Proof.
  intro H. revert wps.
  induction H as [|[|w p|] [v z] xs cs Hx Hxs IH]; intros wps Hv;
    cbn in Hv; try discriminate.
  - inversion Hv. constructor.
  - destruct (Cost.value (tagged_values_c xs)) as [tail|] eqn:Htail;
      cbn in Hv; [|discriminate].
    inversion Hv; subst wps. constructor; [|apply IH; reflexivity].
    cbn in Hx. destruct Hx as [Hvw [Hw Hp]]. subst v.
    split; [reflexivity|]. split; [exact Hw|exact Hp].
Qed.

Local Lemma tagged_values_rebuild {P} (xs : list (tagged P)) wps :
  Cost.value (tagged_values_c xs) = Some wps ->
  xs = map (fun wp => TVal (fst wp) (snd wp)) wps.
Proof.
  revert wps. induction xs as [|[|w p|] xs IH]; intros wps Hv;
    cbn in Hv; try discriminate.
  - inversion Hv. reflexivity.
  - destruct (Cost.value (tagged_values_c xs)) as [tail|] eqn:Htail;
      cbn in Hv; [|discriminate].
    inversion Hv; subst wps. cbn. f_equal. apply IH. reflexivity.
Qed.

Local Lemma payload_widths {P} G wps cs :
  Forall2 (@payload_sound P G) wps cs -> map fst wps = map fst cs.
Proof.
  intro H. induction H as [|x c xs cs [Hw Hp] Htail IH]; cbn; congruence.
Qed.

Local Lemma tagged_forward_sound {P} (D : word_domain P) G :
  word_laws D G -> forall o xs cs rw z, Forall2 (gamma (tagged_gamma G)) xs cs ->
  eval_op o cs = Some (rw, z) ->
  gamma (tagged_gamma G) (Cost.value (tagged_forward_c D o xs)) (rw, z).
Proof.
  intros H o xs cs rw z Hxs He.
  unfold tagged_forward_c. autorewrite with galois_cost.
  rewrite (tagged_no_empty D G H xs cs Hxs). autorewrite with galois_cost.
  destruct (Cost.value (tagged_values_c xs)) as [wps|] eqn:Hv; [|exact I].
  pose proof (tagged_values_sound G xs cs wps Hxs Hv) as Hp.
  autorewrite with galois_cost. rewrite ?Hv. autorewrite with galois_cost.
  replace (map (fun x : width * P => Cost.value (Cost.ret (fst x))) wps)
    with (map fst wps) by reflexivity.
  rewrite (payload_widths G wps cs Hp), (eval_op_width o cs (rw, z) He).
  autorewrite with galois_cost. apply (tagged_val_sound D G H).
  - exact (eval_op_is_word o cs (rw, z) He).
  - exact (pforward_sound H o wps cs rw z Hp He).
Qed.

Local Lemma tagged_refine_sound {P} (D : word_domain P) G :
  word_laws D G -> forall wps cs qs, Forall2 (payload_sound G) wps cs ->
  Forall2 (fun p c => G (fst p) (snd p) (snd c)) (combine (map fst wps) qs) cs ->
  Forall2 (gamma (tagged_gamma G)) (Cost.value (tagged_refine_c D wps qs)) cs.
Proof.
  intros H wps cs qs Hp. revert qs.
  induction Hp as [|[w p] [v z] wps cs [Hwv [Hw Hp]] Htail IH]; intros qs Hqs.
  - destruct qs; constructor.
  - destruct qs as [|q qs]; cbn in Hqs; [inversion Hqs|].
    inversion Hqs as [|wp c tail cs' Hq Hrest]; subst.
    cbn [tagged_refine_c]. autorewrite with galois_cost. constructor.
    + cbn in Hwv, Hw, Hq. subst v. now apply (tagged_val_sound D G H).
    + now apply IH.
Qed.

Local Lemma tagged_refine_lower {P} (D : word_domain P) wps qs :
  Forall2 (fun wp q => leb (plat D (fst wp)) q (snd wp) = true) wps qs ->
  Forall2 (fun x y => leb (tagged_lattice (plat D)) x y = true)
    (Cost.value (tagged_refine_c D wps qs)) (map (fun wp => TVal (fst wp) (snd wp)) wps).
Proof.
  intro H. induction H as [|[w p] q xs qs Hhead Htail IH];
    cbn [tagged_refine_c map]; autorewrite with galois_cost; constructor.
  - now apply tagged_val_lower.
  - exact IH.
Qed.

Local Lemma tagged_refine_length {P} (D : word_domain P) wps qs :
  length (Cost.value (tagged_refine_c D wps qs)) = length wps.
Proof.
  revert qs. induction wps as [|[w p] xs IH]; intros [|q qs];
    cbn [tagged_refine_c]; autorewrite with galois_cost; cbn; auto.
Qed.

Local Lemma tagged_assume_sound {P} (D : word_domain P) G :
  word_laws D G -> forall o a xs cs rw z, Forall2 (gamma (tagged_gamma G)) xs cs ->
  eval_op o cs = Some (rw, z) -> gamma (tagged_gamma G) a (rw, z) ->
  Forall2 (gamma (tagged_gamma G)) (Cost.value (tagged_assume_c D o a xs)) cs.
Proof.
  intros H o a xs cs rw z Hxs He Ha.
  unfold tagged_assume_c. autorewrite with galois_cost.
  rewrite (tagged_empty_false D G H a (rw, z) Ha). autorewrite with galois_cost.
  destruct a as [|aw q|]; [contradiction| |exact Hxs].
  destruct (Cost.value (tagged_values_c xs)) as [wps|] eqn:Hv; [|exact Hxs].
  pose proof (tagged_values_sound G xs cs wps Hxs Hv) as Hp.
  autorewrite with galois_cost. rewrite ?Hv. autorewrite with galois_cost.
  replace (map (fun x : width * P => Cost.value (Cost.ret (fst x))) wps)
    with (map fst wps) by reflexivity.
  rewrite (payload_widths G wps cs Hp).
  rewrite (eval_op_width o cs (rw, z) He).
  cbn in Ha. destruct Ha as [Hrw [Hw Hq]]. subst aw.
  rewrite Pos.eqb_refl. autorewrite with galois_cost.
  apply (tagged_refine_sound D G H wps cs _ Hp).
  exact (passume_sound H o wps cs rw z q Hp He Hq).
Qed.

Local Lemma tagged_assume_lower {P} (D : word_domain P) G :
  word_laws D G -> forall o a xs,
  Forall2 (fun x y => leb (tagged_lattice (plat D)) x y = true)
    (Cost.value (tagged_assume_c D o a xs)) xs.
Proof.
  intros H o a xs.
  assert (Hbot : Forall2 (fun x y => leb (tagged_lattice (plat D)) x y = true)
    (map (fun _ => TBot) xs) xs).
  { induction xs as [|x xs IH]; cbn; constructor; [reflexivity|exact IH]. }
  assert (Hsame : Forall2 (fun x y => leb (tagged_lattice (plat D)) x y = true) xs xs).
  { clear Hbot. induction xs as [|x xs IH]; constructor.
    - apply (leb_refl (tagged_laws D (plat_laws H))).
    - exact IH. }
  unfold tagged_assume_c. autorewrite with galois_cost.
  destruct (Cost.value (tagged_empty_c D a));
    [autorewrite with galois_cost; exact Hbot|].
  autorewrite with galois_cost.
  destruct a as [|rw q|]; try exact Hsame.
  destruct (Cost.value (tagged_values_c xs)) as [wps|] eqn:Hv; [|exact Hsame].
  autorewrite with galois_cost. rewrite ?Hv. autorewrite with galois_cost.
  replace (map (fun x : width * P => Cost.value (Cost.ret (fst x))) wps)
    with (map fst wps) by reflexivity.
  destruct (result_width o (map fst wps)) as [rw'|];
    [|autorewrite with galois_cost; exact Hbot].
  destruct (Pos.eqb rw rw'); [|autorewrite with galois_cost; exact Hbot].
  autorewrite with galois_cost. rewrite (tagged_values_rebuild xs wps Hv).
  apply tagged_refine_lower. exact (passume_refines H o wps rw q).
Qed.

Local Lemma tagged_assume_length {P} (D : word_domain P) o a xs :
  length (Cost.value (tagged_assume_c D o a xs)) = length xs.
Proof.
  unfold tagged_assume_c. autorewrite with galois_cost.
  destruct (Cost.value (tagged_empty_c D a));
    [autorewrite with galois_cost; apply length_map|].
  autorewrite with galois_cost. destruct a as [|rw q|]; try reflexivity.
  destruct (Cost.value (tagged_values_c xs)) as [wps|] eqn:Hv; [|reflexivity].
  autorewrite with galois_cost. rewrite ?Hv. autorewrite with galois_cost.
  replace (map (fun x : width * P => Cost.value (Cost.ret (fst x))) wps)
    with (map fst wps) by reflexivity.
  destruct (result_width o (map fst wps)) as [rw'|];
    [|autorewrite with galois_cost; apply length_map].
  destruct (Pos.eqb rw rw'); [|autorewrite with galois_cost; apply length_map].
  autorewrite with galois_cost.
  rewrite tagged_refine_length, (tagged_values_rebuild xs wps Hv), length_map. reflexivity.
Qed.

Local Lemma tagged_meet_sound {P} (D : word_domain P) G :
  word_laws D G -> forall a b c, gamma (tagged_gamma G) a c ->
  gamma (tagged_gamma G) b c ->
  gamma (tagged_gamma G) (Cost.value (tagged_meet_c D a b)) c.
Proof.
  intros H [|w p|] [|v q|] [u z] Ha Hb; cbn in Ha, Hb;
    try contradiction; cbn [tagged_meet_c]; try exact I.
  - destruct Ha as [Huw [Hw Hp]], Hb as [Huv [_ Hq]]. subst u v.
    rewrite Pos.eqb_refl. autorewrite with galois_cost.
    apply (tagged_val_sound D G H); [exact Hw|]. now apply (pmeet_sound H).
  - destruct Ha as [Huw [Hw Hp]]. subst u. now apply (tagged_val_sound D G H).
  - destruct Hb as [Huv [Hw Hp]]. subst u. now apply (tagged_val_sound D G H).
Qed.

Local Lemma tagged_meet_lower {P} (D : word_domain P) G :
  word_laws D G -> forall a b,
  leb (tagged_lattice (plat D)) (Cost.value (tagged_meet_c D a b)) a = true.
Proof.
  intros H [|w p|] [|v q|]; cbn [tagged_meet_c]; try reflexivity.
  - destruct (Pos.eqb w v); [|reflexivity]. autorewrite with galois_cost.
    apply tagged_val_lower. apply (pmeet_lower_left H).
  - apply tagged_val_lower. apply (leb_refl (plat_laws H w)).
  - unfold tagged_val_c. autorewrite with galois_cost.
    destruct (Cost.value (leb_c (plat D v) q (bot (plat D v)))); reflexivity.
Qed.

(** Every lawful payload dictionary yields a lawful numeric dictionary through width tagging. *)
Theorem tagged_numeric_laws {P} (D : word_domain P) G :
  word_laws D G -> numeric_laws (tagged_domain D) (tagged_gamma G).
Proof.
  intro H. constructor.
  - apply tagged_laws. apply (plat_laws H).
  - constructor. intros a b [u z] Hle Ha.
    change (leb (tagged_lattice (plat D)) a b = true) in Hle.
    destruct a as [|w p|], b as [|v q|];
      rewrite tagged_le in Hle; cbn in Ha |- *;
      try contradiction; try discriminate; try exact I.
    destruct (Pos.eqb w v) eqn:Hwv; [|discriminate].
    apply Pos.eqb_eq in Hwv. subst v.
    destruct Ha as [Huw [Hw Hp]]. split; [exact Huw|]. split; [exact Hw|].
    exact (pgamma_monotone H w p q z Hle Hp).
  - constructor. intros c Hg. exact Hg.
  - intros w z Hw. cbn. split; [reflexivity|]. split; [exact Hw|].
    now apply (ptop_sound H).
  - intros w z. cbn. split; [reflexivity|].
    split; [apply wrap_is_word|apply (pconst_sound H)].
  - intros o xs cs [rw z]. apply (tagged_forward_sound D G H).
  - intros o a xs cs [rw z]. apply (tagged_assume_sound D G H).
  - exact (tagged_assume_length D).
  - exact (tagged_assume_lower D G H).
  - exact (tagged_meet_sound D G H).
  - exact (tagged_meet_lower D G H).
Qed.

Arguments tagged_forward_c : simpl never.
Arguments tagged_assume_c : simpl never.
Arguments tagged_meet_c : simpl never.
