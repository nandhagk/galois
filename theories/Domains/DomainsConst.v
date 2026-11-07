(** * Constant word payloads

    Flat constants evaluate known operands and solve invertible constant equations.
    For example, knowing that x + 3 is 7 refines x to 4 modulo its word width.
    Builds on: LatticeFlat, DomainsTransfer and Bits arithmetic. *)

From Stdlib Require Import ZArith List Bool Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeFlat LatticeConcrete LatticeHeight.
From Galois.Bits Require Import BitsWord BitsFun BitsOp BitsTestbit BitsArith.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer DomainsTagged.
Import List.ListNotations Cost.Notations.
Local Open Scope Z_scope.

(** Constants denote integer equality independently of word validity. *)
Definition const_gamma (_ : width) (p : flat Z) (z : Z) : Prop :=
  gamma (flat_gamma (fun c z => z = c)) p z.

(** Intersection detects inconsistent known constants. *)
Definition const_meet (a b : flat Z) : flat Z :=
  match a, b with
  | FBot, _ | _, FBot => FBot
  | FTop, _ => b
  | _, FTop => a
  | FVal x, FVal y => if Z.eqb x y then FVal x else FBot
  end.

(** Intersection retains every integer admitted by both operands. *)
Theorem const_meet_sound w a b z :
  const_gamma w a z -> const_gamma w b z -> const_gamma w (const_meet a b) z.
Proof.
  destruct a as [|x|], b as [|y|]; cbn [const_gamma flat_gamma gamma const_meet];
    intros Ha Hb; try contradiction; try assumption.
  subst x y. now rewrite Z.eqb_refl.
Qed.

(** Intersection refines its left operand even for raw nonword constants. *)
Theorem const_meet_lower a b : leb (flat_lattice Z.eqb) (const_meet a b) a = true.
Proof.
  change (flat_leb Z.eqb (const_meet a b) a = true).
  destruct a as [|x|], b as [|y|]; cbn [const_meet flat_leb];
    try reflexivity; try apply Z.eqb_refl.
  destruct (Z.eqb x y); cbn [flat_leb]; auto using Z.eqb_refl.
Qed.

Definition const_is (p : flat Z) (z : Z) : bool :=
  match p with
  | FVal c => Z.eqb c z
  | _ => false
  end.

(** Binary annihilators retain information when one operand is unknown. *)
Definition const_shortcut (o : op) (a b : width * flat Z) : option Z :=
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
  end.

Local Lemma const_is_sound w p z c :
  const_gamma w p z -> const_is p c = true -> z = c.
Proof.
  destruct p as [|a|]; cbn [const_gamma flat_gamma gamma const_is];
    intros Hp His; try contradiction; try discriminate.
  apply Z.eqb_eq in His. congruence.
Qed.

Local Lemma const_either w p q x y c :
  const_gamma w p x -> const_gamma w q y ->
  const_is p c || const_is q c = true -> x = c \/ y = c.
Proof.
  intros Hp Hq Htest. apply orb_true_iff in Htest as [Htest|Htest].
  - left. exact (const_is_sound w p x c Hp Htest).
  - right. exact (const_is_sound w q y c Hq Htest).
Qed.

Local Lemma const_zero_bits w x : is_word w x -> wand w 0 x = 0.
Proof.
  intro Hx.
  apply (word_ext w); [apply wand_is_word|apply zero_is_word|].
  intros i Hi. rewrite testbit_wand by (auto using zero_is_word; lia).
  now rewrite !Z.bits_0.
Qed.

Local Lemma const_ones_bits w x :
  is_word w x -> wor w (modulus w - 1) x = modulus w - 1.
Proof.
  intro Hx.
  apply (word_ext w); [apply wor_is_word|apply ones_is_word|].
  intros i Hi. rewrite testbit_wor by (auto using ones_is_word; lia).
  rewrite all_ones_bits by exact Hi.
  destruct (i <? Zpos w) eqn:Hlow; cbn; [reflexivity|].
  apply Z.ltb_ge in Hlow.
  exact (word_bits_high w x i ltac:(assumption) Hlow).
Qed.

Local Lemma const_zero_ops w y : is_word w y ->
  wmul w 0 y = 0 /\ wshl w 0 y = 0 /\
  wlshr w 0 y = 0 /\ washr w 0 y = 0 /\ wurem w 0 y = 0.
Proof.
  intro Hy.
  assert (Hpow : 2 ^ wrap w y <> 0).
  { pose proof (wrap_is_word w y) as [Hnonnegative Hupper].
    apply Z.pow_nonzero; lia. }
  rewrite wmul_value, wshl_value, wlshr_value, washr_value.
  rewrite wrap_0, msb_zero, signed_zero, Z.mul_0_l, wrap_0.
  rewrite Z.div_0_l by exact Hpow. rewrite wrap_0.
  split; [reflexivity|].
  destruct (Zpos w <=? wrap w y); cbn; repeat split; try reflexivity.
  all: change ((if wrap w y =? 0 then wrap w 0 else wrap w 0 mod wrap w y) = 0);
    rewrite wrap_0; destruct (wrap w y =? 0) eqn:Hz; [reflexivity|];
    apply Z.eqb_neq in Hz; now apply Z.mod_0_l.
Qed.

Definition const_forward_entry o (_ : width) (xs : list (width * flat Z))
    : Cost.t (flat Z) :=
  Cost.step ;;
  Cost.ret
    (match xs with
     | [a; b] =>
       match const_shortcut o a b with
       | Some c => FVal c
       | None => FTop
       end
     | _ => FTop
     end).

(** Inverse callbacks retain their work and the overhead of invoking a known operand. *)
Definition const_inverse_c (f : Z -> Cost.t Z) (p : flat Z) : Cost.t (flat Z) :=
  match p with
  | FVal z => Cost.map FVal (Cost.step ;; f z)
  | _ => Cost.ret FTop
  end.

(** An unknown inverse operand imposes no additional constant constraint. *)
Definition const_inverse f p := Cost.value (const_inverse_c f p).

(** Both inverse callbacks retain their costs before their facts are intersected. *)
Definition const_inverse_pair_c (f g : Z -> Cost.t Z) (a b : flat Z) :=
  let* ia := const_inverse_c f b in
  let* ib := const_inverse_c g a in
  Cost.ret [const_meet a ia; const_meet b ib].

Definition const_backward_one o rw (q : flat Z) (xs : list (width * flat Z))
    : Cost.t (list (flat Z)) :=
  match xs, q with
  | [(_, a)], FVal r =>
    Cost.step ;; Cost.ret [const_meet a (FVal
      (match o with bvnot => wnot rw r | _ => wneg rw r end))]
  | _, _ => map_c (fun wp => Cost.ret (snd wp)) xs
  end.

Definition const_backward_two o (_ : width) (q : flat Z) (xs : list (width * flat Z))
    : Cost.t (list (flat Z)) :=
  match xs, q with
  | [(w, a); (_, b)], FVal r =>
    Cost.step ;;
      match o with
       | bveq =>
         Cost.ret (if Z.eqb r 1 then [const_meet a b; const_meet b a] else [a; b])
       | bvne =>
         Cost.ret (if Z.eqb r 0 then [const_meet a b; const_meet b a] else [a; b])
       | bvadd =>
         const_inverse_pair_c (fun z => Cost.step ;; Cost.ret (wsub w r z))
           (fun z => Cost.step ;; Cost.ret (wsub w r z)) a b
       | bvsub =>
         const_inverse_pair_c (fun z => Cost.step ;; Cost.ret (wadd w r z))
           (fun z => Cost.step ;; Cost.ret (wsub w z r)) a b
       | bvxor =>
         const_inverse_pair_c (fun z => Cost.step ;; Cost.ret (wxor w r z))
           (fun z => Cost.step ;; Cost.ret (wxor w r z)) a b
       | _ => Cost.ret [a; b]
       end
  | _, _ => map_c (fun wp => Cost.ret (snd wp)) xs
  end.

(** The table contains only annihilators and the legacy invertible backward families. *)
Definition const_table : Transfer.table (width * flat Z) (flat Z) op width :=
  {| Transfer.fwd := fun o n => Cost.ret
       (match o, n with
        | (bvmul | bvand | bvor | bvshl | bvlshr | bvashr | bvurem), 2%nat =>
          Some (const_forward_entry o)
        | _, _ => None
        end);
     Transfer.bwd := fun o n => Cost.ret
       (match o, n with
        | (bvnot | bvneg), 1%nat => Some (const_backward_one o)
        | (bveq | bvne | bvadd | bvsub | bvxor), 2%nat => Some (const_backward_two o)
        | _, _ => None
        end) |}.

(** The fixed-arity evaluator receives at most three operands, so its lists are scalar leaves. *)
Definition const_eval_c o (xs : list word) :=
  match xs with
  | _ :: _ :: _ :: _ :: _ => Cost.ret None
  | _ => Cost.step ;; Cost.ret (eval_op o xs)
  end.

Local Lemma const_eval_equation o xs : Cost.value (const_eval_c o xs) = eval_op o xs.
Proof.
  destruct xs as [|a [|b [|c [|d rest]]]]; try reflexivity.
  destruct (eval_op o (a :: b :: c :: d :: rest)) as [r|] eqn:He; [|reflexivity].
  pose proof (eval_op_arity o _ r He) as Hlen.
  destruct o; cbn in Hlen; discriminate.
Qed.

(** Flat values supply exact points, empty operands and identity backward embeddings. *)
Definition const_shape : Transfer.shape (width * flat Z) (flat Z) op width word :=
  {| Transfer.eval_c := const_eval_c;
     Transfer.point_c := fun wp => Cost.step ;; Cost.ret
       (match snd wp with FVal z => Some (fst wp, z) | _ => None end);
     Transfer.is_empty_c := fun wp => Cost.step ;; Cost.ret
       (match snd wp with FBot => true | _ => false end);
     Transfer.inj_c := fun _ c => Cost.step ;; Cost.ret (FVal (snd c));
     Transfer.bot_out := fun _ => FBot;
     Transfer.top_out := fun _ => FTop;
     Transfer.keep_c := fun wp => Cost.ret (snd wp) |}.

(** The constant domain uses the landed flat lattice and the shared transfer harness. *)
Definition const_word_domain : word_domain (flat Z) :=
  word_of_table const_table const_shape (fun _ => flat_lattice Z.eqb) (fun _ => FTop)
    (fun w z => Cost.step ;; Cost.ret (FVal (wrap w z)))
    (fun _ a b => Cost.step ;; Cost.ret (const_meet a b)).

Local Lemma const_shape_laws :
  transfer_sem const_shape (payload_sound const_gamma) (word_output const_gamma) word_context.
Proof.
  constructor.
  - intros [w [|z|]] [v x] [u y] Hp [Hw [Hy Hg]]; try discriminate.
    inversion Hp; subst. cbn in Hw, Hg. subst. reflexivity.
  - intros [w [|z|]] c He [_ [_ Hg]]; try discriminate. exact Hg.
  - intros r [w z] Hctx. reflexivity.
  - intros r c H. exact H.
  - intros. exact I.
  - intros r [w p] [v z] [Hw [Hz Hg]]. cbn in Hw. subst v. exact Hg.
Qed.

Local Lemma const_shortcut_sound o w a b x y rw z c :
  is_word w x -> is_word w y -> const_gamma w a x -> const_gamma w b y ->
  eval_op o [(w, x); (w, y)] = Some (rw, z) ->
  const_shortcut o (w, a) (w, b) = Some c -> z = c.
Proof.
  intros Hx Hy Ha Hb Heval Hshortcut.
  destruct o; cbn [const_shortcut fst snd] in Hshortcut; try discriminate.
  all: repeat match type of Hshortcut with
    | (if ?b then _ else _) = _ => destruct b eqn:Htest; [|discriminate]
    end; inversion Hshortcut; subst c.
  - pose proof (const_either w a b x y 0 Ha Hb Htest) as Hzero.
    rewrite (eval_op_fun2 bvmul w x y wmul eq_refl) in Heval.
    inversion Heval; subst rw z. destruct Hzero as [-> | ->].
    + exact (proj1 (const_zero_ops w y Hy)).
    + rewrite wmul_comm. exact (proj1 (const_zero_ops w x Hx)).
  - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
    rewrite (eval_op_fun2 bvurem w 0 y wurem eq_refl) in Heval.
    inversion Heval; subst rw z.
    exact (proj2 (proj2 (proj2 (proj2 (const_zero_ops w y Hy))))).
  - pose proof (const_either w a b x y 0 Ha Hb Htest) as Hzero.
    rewrite (eval_op_fun2 bvand w x y wand eq_refl) in Heval.
    inversion Heval; subst rw z. destruct Hzero as [-> | ->].
    + now apply const_zero_bits.
    + rewrite wand_comm. now apply const_zero_bits.
  - pose proof (const_either w a b x y _ Ha Hb Htest) as Hones.
    rewrite (eval_op_fun2 bvor w x y wor eq_refl) in Heval.
    inversion Heval; subst rw z. destruct Hones as [-> | ->].
    + now apply const_ones_bits.
    + rewrite wor_comm. now apply const_ones_bits.
  - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
    rewrite (eval_op_fun2 bvshl w 0 y wshl eq_refl) in Heval.
    inversion Heval; subst rw z. exact (proj1 (proj2 (const_zero_ops w y Hy))).
  - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
    rewrite (eval_op_fun2 bvlshr w 0 y wlshr eq_refl) in Heval.
    inversion Heval; subst rw z. exact (proj1 (proj2 (proj2 (const_zero_ops w y Hy)))).
  - apply (const_is_sound w a x 0 Ha) in Htest. subst x.
    rewrite (eval_op_fun2 bvashr w 0 y washr eq_refl) in Heval.
    inversion Heval; subst rw z.
    exact (proj1 (proj2 (proj2 (proj2 (const_zero_ops w y Hy))))).
Qed.

(** Every binary annihilator entry retains the exact result on normalized operands. *)
Theorem const_forward_entry_sound o rw xs cs c :
  (o = bvmul \/ o = bvand \/ o = bvor \/ o = bvshl \/ o = bvlshr \/
    o = bvashr \/ o = bvurem) ->
  Forall2 (payload_sound const_gamma) xs cs -> eval_op o cs = Some c ->
  word_context rw c ->
  word_output const_gamma rw (Cost.value (const_forward_entry o rw xs)) c.
Proof.
  intros Ho Hxs Heval Hctx.
  destruct xs as [|[w a] [|[v b] [|wp rest]]]; try exact I.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Ha, Hb. subst wx vy. destruct c as [target z].
  change (const_gamma target
    (Cost.value (const_forward_entry o rw [(w, a); (v, b)])) z).
  unfold const_forward_entry. autorewrite with galois_cost.
  destruct (const_shortcut o (w, a) (v, b)) as [k|] eqn:Hshortcut; [|exact I].
  assert (Hw : w = v).
  { destruct o; cbn [const_shortcut] in Hshortcut; try discriminate;
      match type of Heval with
      | eval_op ?k _ = _ =>
        eapply (eval_op_fun2_width k _ w v x y (target, z)); [reflexivity|exact Heval]
      end. }
  subst v. exact (const_shortcut_sound o w a b x y target z k Hx Hy Ha Hb Heval Hshortcut).
Qed.

Local Lemma const_add_inverse w x y : is_word w x -> wsub w (wadd w x y) y = x.
Proof.
  intro Hx. rewrite wsub_value, wadd_value, wrap_sub, wrap_wrap, <- wrap_sub.
  replace (x + y - y) with x by ring. now apply wrap_id.
Qed.

Local Lemma const_sub_inverse_left w x y : is_word w x -> wadd w (wsub w x y) y = x.
Proof.
  intro Hx. rewrite wadd_value, wsub_value, wrap_add, wrap_wrap, <- wrap_add.
  replace (x - y + y) with x by ring. now apply wrap_id.
Qed.

Local Lemma const_sub_inverse_right w x y : is_word w y -> wsub w x (wsub w x y) = y.
Proof.
  intro Hy. rewrite !wsub_value, wrap_sub, wrap_wrap, <- wrap_sub.
  replace (x - (x - y)) with y by ring. now apply wrap_id.
Qed.

Local Lemma const_xor_inverse w x y : is_word w x -> wxor w (wxor w x y) y = x.
Proof.
  intro Hx. rewrite <- wxor_assoc, wxor_self.
  apply (word_ext w); [apply wxor_is_word|exact Hx|].
  intros i Hi. rewrite testbit_wxor by (auto using zero_is_word; lia).
  now rewrite Z.bits_0, xorb_false_r.
Qed.

Local Lemma const_neg_inverse w x : is_word w x -> wneg w (wneg w x) = x.
Proof.
  intro Hx. rewrite !wneg_value, wrap_opp.
  replace (- - x) with x by ring. now apply wrap_id.
Qed.

Local Lemma const_inverse_sound w f p x y :
  const_gamma w p y -> x = Cost.value (f y) -> const_gamma w (const_inverse f p) x.
Proof.
  destruct p as [|c|]; unfold const_inverse, const_inverse_c;
    autorewrite with galois_cost; cbn [const_gamma flat_gamma gamma];
    intros Hp Hxy; try contradiction; try exact I. now subst y.
Qed.

Local Lemma const_backward_one_sound o rw q xs cs c :
  (o = bvnot \/ o = bvneg) -> length xs = 1%nat ->
  Forall2 (payload_sound const_gamma) xs cs -> eval_op o cs = Some c ->
  word_context rw c ->
  word_output const_gamma rw q c ->
  Forall2 (word_output const_gamma rw)
    (Cost.value (const_backward_one o rw q xs)) cs.
Proof.
  intros Ho Hlen Hxs Heval Hctx Hq.
  destruct xs as [|[w a] [|wp rest]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [v x] ? ? Hhead Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hw [Hx Ha]]. cbn in Hw, Ha. subst v.
  destruct q as [|r|]; [contradiction| |].
  - destruct c as [target z]. destruct Hctx as [Htarget Hword].
    cbn in Htarget. subst rw.
    cbn [word_output const_gamma flat_gamma gamma fst snd] in Hq.
    subst r. destruct Ho as [-> | ->].
    + pose proof (eq_trans (eq_sym (eval_op_fun1 bvnot w x wnot eq_refl)) Heval) as Hr.
      inversion Hr; subst target z. unfold const_backward_one.
      autorewrite with galois_cost. constructor; [|constructor].
      apply const_meet_sound; [exact Ha|].
      cbn [const_gamma flat_gamma gamma]. symmetry.
      now apply wnot_involutive.
    + pose proof (eq_trans (eq_sym (eval_op_fun1 bvneg w x wneg eq_refl)) Heval) as Hr.
      inversion Hr; subst target z. unfold const_backward_one.
      autorewrite with galois_cost. constructor; [|constructor].
      apply const_meet_sound; [exact Ha|].
      cbn [const_gamma flat_gamma gamma]. symmetry.
      now apply const_neg_inverse.
  - cbn [const_backward_one]. rewrite value_map_c. constructor; [exact Ha|constructor].
Qed.

Local Lemma const_backward_two_sound o rw q xs cs c :
  (o = bveq \/ o = bvne \/ o = bvadd \/ o = bvsub \/ o = bvxor) ->
  length xs = 2%nat -> Forall2 (payload_sound const_gamma) xs cs ->
  eval_op o cs = Some c -> word_output const_gamma rw q c ->
  Forall2 (word_output const_gamma rw)
    (Cost.value (const_backward_two o rw q xs)) cs.
Proof.
  intros Ho Hlen Hxs Heval Hq.
  destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate.
  inversion Hxs as [|? [wx x] ? ? Hhead Htail]; subst.
  inversion Htail as [|? [vy y] ? ? Hhead' Hnil]; subst. inversion Hnil; subst.
  destruct Hhead as [Hwx [Hx Ha]], Hhead' as [Hvy [Hy Hb]].
  cbn in Hwx, Hvy, Ha, Hb. subst wx vy.
  assert (Hw : w = v).
  { destruct Ho as [-> | [-> | [-> | [-> | ->]]]];
      match type of Heval with
      | eval_op ?k _ = _ =>
        first [eapply (eval_op_fun2_width k _ w v x y c); [reflexivity|exact Heval] |
          eapply (eval_op_cmp_width k _ w v x y c); [reflexivity|exact Heval]]
      end. }
  subst v. destruct q as [|r|]; [contradiction| |].
  - destruct c as [target z]. cbn [word_output const_gamma flat_gamma gamma fst snd] in Hq.
    subst r.
    assert (Hpair : forall a' b', const_gamma w a' x -> const_gamma w b' y ->
      Forall2 (word_output const_gamma rw) [a'; b'] [(w, x); (w, y)]).
    { intros a' b' Hx' Hy'. constructor; [exact Hx'|].
      constructor; [exact Hy'|constructor]. }
    destruct Ho as [-> | [-> | [-> | [-> | ->]]]].
    + pose proof (eq_trans (eq_sym (eval_op_cmp bveq w x y _ eq_refl)) Heval) as Hr.
      cbn beta in Hr. rewrite !wrap_id in Hr by assumption.
      destruct (x =? y) eqn:Hxy; inversion Hr; subst target z; unfold const_backward_two;
        autorewrite with galois_cost; cbn.
      * apply Z.eqb_eq in Hxy. subst y. apply Hpair; apply const_meet_sound; assumption.
      * apply Hpair; assumption.
    + pose proof (eq_trans (eq_sym (eval_op_cmp bvne w x y _ eq_refl)) Heval) as Hr.
      cbn beta in Hr. rewrite !wrap_id in Hr by assumption.
      destruct (x =? y) eqn:Hxy; inversion Hr; subst target z; unfold const_backward_two;
        autorewrite with galois_cost; cbn.
      * apply Z.eqb_eq in Hxy. subst y. apply Hpair; apply const_meet_sound; assumption.
      * apply Hpair; assumption.
    + pose proof (eq_trans (eq_sym (eval_op_fun2 bvadd w x y wadd eq_refl)) Heval) as Hr.
      inversion Hr; subst target z. unfold const_backward_two, const_inverse_pair_c.
      autorewrite with galois_cost.
      apply Hpair; apply const_meet_sound; try assumption.
      * apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_add_inverse.
      * apply (const_inverse_sound w _ a y x Ha). rewrite wadd_comm.
        symmetry. now apply const_add_inverse.
    + pose proof (eq_trans (eq_sym (eval_op_fun2 bvsub w x y wsub eq_refl)) Heval) as Hr.
      inversion Hr; subst target z. unfold const_backward_two, const_inverse_pair_c.
      autorewrite with galois_cost.
      apply Hpair; apply const_meet_sound; try assumption.
      * apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_sub_inverse_left.
      * apply (const_inverse_sound w _ a y x Ha). symmetry. now apply const_sub_inverse_right.
    + pose proof (eq_trans (eq_sym (eval_op_fun2 bvxor w x y wxor eq_refl)) Heval) as Hr.
      inversion Hr; subst target z. unfold const_backward_two, const_inverse_pair_c.
      autorewrite with galois_cost.
      apply Hpair; apply const_meet_sound; try assumption.
      * apply (const_inverse_sound w _ b x y Hb). symmetry. now apply const_xor_inverse.
      * apply (const_inverse_sound w _ a y x Ha). rewrite (wxor_comm w x y).
        symmetry. now apply const_xor_inverse.
  - cbn [const_backward_two]. rewrite value_map_c.
    constructor; [exact Ha|]. constructor; [exact Hb|constructor].
Qed.

(** Every supplied transfer preserves concrete evaluation and backward operand counts. *)
Theorem const_table_laws :
  table_laws const_table const_shape (payload_sound const_gamma)
    (word_output const_gamma) word_context.
Proof.
  constructor.
  - intros o n f rw xs cs c Hf Hlen Hxs Heval Hctx.
    change (Cost.value (const_eval_c o cs) = Some c) in Heval.
    rewrite const_eval_equation in Heval.
    destruct o; destruct n as [|[|[|n]]]; cbn in Hf; try discriminate;
      injection Hf as <-.
    all: eapply const_forward_entry_sound; [tauto|eassumption|eassumption|eassumption].
  - intros o n f rw q xs cs c Hf Hlen Hxs Heval Hctx Hq.
    change (Cost.value (const_eval_c o cs) = Some c) in Heval.
    rewrite const_eval_equation in Heval.
    destruct o; destruct n as [|[|[|n]]]; cbn in Hf; try discriminate;
      injection Hf as <-.
    all: first
      [eapply const_backward_one_sound; [tauto|exact Hlen|exact Hxs|exact Heval|
        exact Hctx|exact Hq]
      |eapply const_backward_two_sound; [tauto|exact Hlen|exact Hxs|exact Heval|exact Hq]].
  - intros o n f rw q xs Hf Hlen.
    destruct o; destruct n as [|[|[|n]]]; cbn in Hf; try discriminate;
      injection Hf as <-; destruct q as [|r|];
      destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate;
      unfold const_backward_one, const_backward_two, const_inverse_pair_c;
      autorewrite with galois_cost;
      try rewrite value_map_c, length_map; try reflexivity.
    all: try destruct (r =? 0); try destruct (r =? 1); reflexivity.
Qed.

(** All backward entries intersect new information with the old operand facts. *)
Theorem const_table_refines :
  table_refines const_table const_shape
    (fun wp q => leb (flat_lattice Z.eqb) q (snd wp) = true).
Proof.
  constructor.
  - intros [w p]. apply (leb_refl (flat_laws Z.eqb Z.eqb_eq)).
  - intros o n f rw q xs Hf Hlen.
    destruct o; destruct n as [|[|[|n]]]; cbn in Hf; try discriminate;
      injection Hf as <-; destruct q as [|r|];
      destruct xs as [|[w a] [|[v b] [|wp rest]]]; cbn in Hlen; try discriminate;
      unfold const_backward_one, const_backward_two, const_inverse_pair_c;
      autorewrite with galois_cost;
      try rewrite value_map_c; cbn [map fst snd].
    all: try destruct (r =? 0); try destruct (r =? 1).
    all: repeat apply Forall2_cons;
      try apply const_meet_lower;
      try apply (leb_refl (flat_laws Z.eqb Z.eqb_eq));
      try apply Forall2_nil.
Qed.

(** The constant word domain satisfies soundness, meet and structural refinement laws. *)
Theorem const_word_laws : word_laws const_word_domain const_gamma.
Proof.
  apply word_of_table_laws.
  - exact const_eval_equation.
  - exact const_shape_laws.
  - exact const_table_laws.
  - intros. exact (flat_laws Z.eqb Z.eqb_eq).
  - intros w a b z Hle Ha.
    exact (gamma_monotone (flat_gamma_laws Z.eqb (fun c z => z = c) Z.eqb_eq)
      a b z Hle Ha).
  - intros w z H. exact H.
  - intros. exact I.
  - intros. reflexivity.
  - exact const_table_refines.
  - intros. now apply const_meet_sound.
  - intros. apply const_meet_lower.
Qed.

(** Width tagging supplies numeric evaluation and assumption soundness for constants. *)
Theorem const_numeric_laws :
  numeric_laws (tagged_domain const_word_domain) (tagged_gamma const_gamma).
Proof.
  apply tagged_numeric_laws. exact const_word_laws.
Qed.

(** Constants have the flat lattice's three levels. *)
Theorem const_height_on : height_on (flat_lattice Z.eqb) (fun _ => True).
Proof.
  exact (flat_height Z.eqb Z.eqb_eq).
Defined.

#[export] Hint Resolve const_forward_entry_sound const_meet_sound : galois_gamma.
