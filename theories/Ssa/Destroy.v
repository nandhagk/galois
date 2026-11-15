(** * SSA destruction with checked edge copies

    Branch edges receive private copy blocks before parameters become checked moves.
    For example, a swap is copied on its taken edge using a fresh temporary.
    Builds on: Lang, positive-key tries, ParMoveSig and DestroySig. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Ssa Require Import Lang LiveSig ValidateSig ParMoveSig DestroySig.
Import List.ListNotations.

Module Pos.
  TimeFun Pos.max.
End Pos.

(** A finite loop result persists when the fuel increases. *)
Lemma loop_fuel_result_mono {A B} (next : A -> A + B) :
  forall n m a r, n <= m -> loop_fuel next n a = inr r ->
    loop_fuel next m a = inr r.
Proof.
  induction n as [|n IH]; intros m a r Hle Hrun.
  - discriminate Hrun.
  - destruct m as [|m]; [lia|].
    cbn [loop_fuel] in *.
    destruct (next a) as [a'|out].
    + eapply IH; [lia|exact Hrun].
    + exact Hrun.
Qed.

(** Additional fuel retains both returned values and errors of a function run. *)
Lemma run_with_mono {K G C} (eval : K -> list C -> option C)
    (test : G -> list C -> option bool) :
  forall (p : func positive K G) n m ins r, n <= m -> r <> Timeout ->
    run_with eval test n p ins = r -> run_with eval test m p ins = r.
Proof.
  intros p n m ins r Hle Hfinite Hrun.
  unfold run_with in *.
  destruct (bind_vars (inputs _ _ _ p) ins []) as [initial|] eqn:Hbind.
  - destruct (loop_fuel (step eval test p) n (entry _ _ _ p, [], initial))
      as [st|out] eqn:Hloop.
    + exfalso. apply Hfinite. symmetry. exact Hrun.
    + rewrite (loop_fuel_result_mono _ _ _ _ _ Hle Hloop). exact Hrun.
  - exact Hrun.
Qed.

Module DestroyCode (O : OPS)
    (K : KEY_OPS with Definition t := O.K) (G : KEY_OPS with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (PM : PARMOVE_OPS) <: DESTROY_OPS O K G P PM.
  Definition fresh_after (xs : list positive) : positive :=
    Pos.succ (fold_right Pos.max 1%positive xs).

  Definition split_edge (fresh target : positive) (actuals : list positive)
      : positive * (positive * list (positive * block positive O.K O.G)) :=
    match actuals with
    | [] => (fresh, (target, []))
    | _ :: _ =>
      (Pos.succ fresh,
        (fresh, [(fresh, Block _ _ _ [] [] (Jump target actuals))]))
    end.

  Definition split_exit (fresh : positive) (e : exit positive O.G)
      : positive * (exit positive O.G * list (positive * block positive O.K O.G)) :=
    match e with
    | Branch guard operands yes yes_args no no_args =>
      let '(next, (yes', yes_blocks)) := split_edge fresh yes yes_args in
      let '(last, (no', no_blocks)) := split_edge next no no_args in
      (last, (Branch guard operands yes' [] no' [], yes_blocks ++ no_blocks))
    | _ => (fresh, (e, []))
    end.

  Fixpoint split_blocks (fresh : positive)
      (bs : list (positive * block positive O.K O.G))
      : positive * list (positive * block positive O.K O.G) :=
    match bs with
    | [] => (fresh, [])
    | (id, body) :: rest =>
      let '(next, (e, extra)) := split_exit fresh (term _ _ _ body) in
      let '(last, tail) := split_blocks next rest in
      (last, (id, Block _ _ _ (params _ _ _ body) (code _ _ _ body) e) :: extra ++ tail)
    end.

  Definition split (s : P.t) : option P.t :=
    let '(_, bs) := split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s) in
    Some (Func _ _ _ (entry _ _ _ s) (inputs _ _ _ s) bs).

  Fixpoint distinct_vars (xs : list positive) (seen : ptrie unit) : bool :=
    match xs with
    | [] => true
    | x :: rest =>
      match trie_get x seen with
      | Some _ => false
      | None => distinct_vars rest (PTrieCode.set x tt seen)
      end
    end.

  Fixpoint params_index (bs : list (positive * block positive O.K O.G))
      : option (ptrie (list positive)) :=
    match bs with
    | [] => Some Empty
    | (id, body) :: rest =>
      if distinct_vars (params _ _ _ body) Empty then
        match params_index rest with
        | None => None
        | Some table => Some (PTrieCode.set id (params _ _ _ body) table)
        end
      else None
    end.

  Fixpoint pair_moves (formals actuals : list positive) : option moves :=
    match formals, actuals with
    | [], [] => Some []
    | x :: xs, y :: ys =>
      match pair_moves xs ys with
      | None => None
      | Some par => Some ((x, y) :: par)
      end
    | _, _ => None
    end.

  Definition move_code (sq : moves) : list (positive * O.K * list positive) :=
    map (fun '(dst, src) => (dst, O.mov, [src])) sq.

  Definition moves_ok (par : moves) (tmp : positive) : bool :=
    andb (distinct_vars (map fst par) Empty)
      (negb (existsb (fun x => Pos.eqb tmp x) (map fst par ++ map snd par))).

  Definition empty_params (table : ptrie (list positive)) (target : positive) : bool :=
    match trie_get target table with Some [] => true | _ => false end.

  Definition copy_block (table : ptrie (list positive)) (tmp : positive)
      (body : block positive O.K O.G) : option (block positive O.K O.G * option move_check) :=
    match term _ _ _ body with
    | Jump target actuals =>
      match trie_get target table with
      | None => None
      | Some formals =>
        match pair_moves formals actuals with
        | None => None
        | Some [] => Some (Block _ _ _ [] (code _ _ _ body) (Jump target []), None)
        | Some par =>
          let sq := PM.seq par tmp in
          if andb (moves_ok par tmp) (PM.check_moves par tmp sq) then
            (* Reading every actual preserves errors even when a self-copy is omitted. *)
            let reads := move_code (map (fun src => (tmp, src)) actuals) in
            Some (Block _ _ _ [] (code _ _ _ body ++ reads ++ move_code sq)
              (Jump target []), Some (par, tmp, sq))
          else None
        end
      end
    | Branch guard operands yes [] no [] =>
      if andb (empty_params table yes) (empty_params table no) then
        Some (Block _ _ _ [] (code _ _ _ body) (Branch guard operands yes [] no []), None)
      else None
    | Branch _ _ _ _ _ _ => None
    | Return values => Some (Block _ _ _ [] (code _ _ _ body) (Return values), None)
    end.

  Fixpoint copy_blocks (table : ptrie (list positive)) (tmp : positive)
      (bs : list (positive * block positive O.K O.G))
      : option (list (positive * block positive O.K O.G) * list move_check) :=
    match bs with
    | [] => Some ([], [])
    | (id, body) :: rest =>
      match copy_block table tmp body, copy_blocks table tmp rest with
      | Some (body', checked), Some (tail, checks) =>
        Some ((id, body') :: tail,
          match checked with None => checks | Some mc => mc :: checks end)
      | _, _ => None
      end
    end.

  Definition copy_stage (s : P.t) : option (P.t * list move_check) :=
    match params_index (blocks _ _ _ s) with
    | None => None
    | Some table =>
      match trie_get (entry _ _ _ s) table with
      | Some [] =>
        match copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) with
        | None => None
        | Some (bs, checks) =>
          Some (Func _ _ _ (entry _ _ _ s) (inputs _ _ _ s) bs, checks)
        end
      | _ => None
      end
    end.

  Definition copies (s : P.t) : option P.t :=
    match copy_stage s with None => None | Some (p, _) => Some p end.

  Definition checked_moves (s : P.t) : list move_check :=
    match copy_stage s with None => [] | Some (_, checks) => checks end.

  Definition destroy (s : P.t) : option P.t :=
    match split s with None => None | Some split_s => copies split_s end.
End DestroyCode.

Module Destroy (O : OPS)
    (K : KEY with Definition t := O.K) (G : KEY with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (PM : PARMOVE) (OL : LAWS O)
    <: DESTROY O K G P PM OL.
  Include DestroyCode O K G P PM.

  (** The distinctness pass rejects repeated variables and variables already seen. *)
  Lemma distinct_vars_sound : forall xs seen, distinct_vars xs seen = true ->
    NoDup xs /\ forall x, In x xs -> trie_get x seen = None.
  Proof.
    induction xs as [|x xs IH]; intros seen Hdistinct.
    - split; [constructor|]. intros y Hin. contradiction.
    - cbn [distinct_vars] in Hdistinct.
      destruct (trie_get x seen) as [found|] eqn:Hseen; [discriminate|].
      destruct (IH (PTrieCode.set x tt seen) Hdistinct) as [Htail Hmissing].
      assert (Hnot : ~ In x xs).
      { intro Hin. specialize (Hmissing x Hin).
        rewrite PTrie.get_set_same in Hmissing. discriminate. }
      split; [constructor; assumption|].
      intros y [Heq|Hin].
      + subst y. exact Hseen.
      + specialize (Hmissing y Hin).
        rewrite PTrie.get_set_other in Hmissing; [exact Hmissing|].
        intro Heq. subst y. contradiction.
  Qed.

  (** The explicit move precondition check establishes uniqueness and temporary freshness. *)
  Lemma moves_ok_sound : forall par tmp, moves_ok par tmp = true ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par).
  Proof.
    intros par tmp Hchecked. unfold moves_ok in Hchecked.
    apply andb_true_iff in Hchecked as [Hdistinct Hfresh].
    apply negb_true_iff in Hfresh. split.
    - exact (proj1 (distinct_vars_sound _ _ Hdistinct)).
    - intro Hin.
      assert (Hexists : existsb (fun x => Pos.eqb tmp x)
          (map fst par ++ map snd par) = true).
      { apply existsb_exists. exists tmp. split; [exact Hin|apply Pos.eqb_refl]. }
      rewrite Hfresh in Hexists. discriminate.
  Qed.

  Definition move_check_good (mc : move_check) : Prop :=
    let '(par, tmp, sq) := mc in
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par) /\
      PM.check_moves par tmp sq = true.

  (** Every recorded block check passed both the preconditions and the symbolic checker. *)
  Lemma copy_block_checked : forall table tmp body out checked,
    copy_block table tmp body = Some (out, checked) ->
    match checked with None => True | Some mc => move_check_good mc end.
  Proof.
    intros table tmp [formals instructions ending] out checked.
    destruct ending as [target actuals|guard operands yes yes_args no no_args|values];
      cbn [copy_block term code].
    - destruct (trie_get target table) as [target_formals|]; [|discriminate].
      destruct (pair_moves target_formals actuals) as [[|first par]|]; try discriminate.
      + intros Hcopy. inversion Hcopy; subst. exact I.
      + destruct (andb (moves_ok (first :: par) tmp)
          (PM.check_moves (first :: par) tmp (PM.seq (first :: par) tmp)))
          eqn:Hchecked; [|discriminate].
        intros Hcopy. inversion Hcopy; subst.
        apply andb_true_iff in Hchecked as [Hvalid Hchecked].
        destruct (moves_ok_sound _ _ Hvalid) as [Hdistinct Hfresh].
        repeat split; assumption.
    - destruct yes_args as [|x xs]; [|discriminate].
      destruct no_args as [|x xs]; [|discriminate].
      destruct (andb (empty_params table yes) (empty_params table no)); [|discriminate].
      intros Hcopy. inversion Hcopy; subst. exact I.
    - intros Hcopy. inversion Hcopy; subst. exact I.
  Qed.

  (** Combining rewritten blocks keeps the evidence for each recorded move problem. *)
  Lemma copy_blocks_checked : forall table tmp bs out checked,
    copy_blocks table tmp bs = Some (out, checked) -> Forall move_check_good checked.
  Proof.
    intros table tmp bs. induction bs as [|[id body] rest IH]; intros out checked Hcopy.
    - inversion Hcopy; subst. constructor.
    - cbn [copy_blocks] in Hcopy.
      destruct (copy_block table tmp body) as [[body' one]|] eqn:Hbody; [|discriminate].
      destruct (copy_blocks table tmp rest) as [[tail checks]|] eqn:Htail;
        [|discriminate].
      inversion Hcopy; subst. destruct one as [mc|].
      + constructor.
        * exact (copy_block_checked table tmp body body' (Some mc) Hbody).
        * eapply IH. reflexivity.
      + eapply IH. reflexivity.
  Qed.

  (** Each advertised move problem belongs to a successful checked copy pass. *)
  Lemma checked_moves_good : forall s, Forall move_check_good (checked_moves s).
  Proof.
    intro s. unfold checked_moves, copy_stage.
    destruct (params_index (blocks _ _ _ s)) as [table|]; [|constructor].
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|]; try constructor.
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|] eqn:Hblocks; [|constructor].
    eapply copy_blocks_checked. exact Hblocks.
  Qed.

  (** Rewritten blocks have neither parameters nor outgoing actual arguments. *)
  Lemma copy_block_imp : forall table tmp body out checked,
    copy_block table tmp body = Some (out, checked) ->
    params _ _ _ out = [] /\ imp_exit (term _ _ _ out).
  Proof.
    intros table tmp [formals instructions ending] out checked.
    destruct ending as [target actuals|guard operands yes yes_args no no_args|values];
      cbn [copy_block term code].
    - destruct (trie_get target table) as [target_formals|]; [|discriminate].
      destruct (pair_moves target_formals actuals) as [[|first par]|]; try discriminate.
      + intros Hcopy. inversion Hcopy; subst. split; reflexivity.
      + destruct (andb (moves_ok (first :: par) tmp)
          (PM.check_moves (first :: par) tmp (PM.seq (first :: par) tmp)));
          [|discriminate].
        intros Hcopy. inversion Hcopy; subst. split; reflexivity.
    - destruct yes_args as [|x xs]; [|discriminate].
      destruct no_args as [|x xs]; [|discriminate].
      destruct (andb (empty_params table yes) (empty_params table no)); [|discriminate].
      intros Hcopy. inversion Hcopy; subst. repeat split; reflexivity.
    - intros Hcopy. inversion Hcopy; subst. split; [reflexivity|exact I].
  Qed.

  (** Rewriting all blocks establishes imperative form for the resulting block list. *)
  Lemma copy_blocks_imp : forall table tmp bs out checked,
    copy_blocks table tmp bs = Some (out, checked) ->
    Forall (fun item => params _ _ _ (snd item) = [] /\
      imp_exit (term _ _ _ (snd item))) out.
  Proof.
    intros table tmp bs. induction bs as [|[id body] rest IH]; intros out checked Hcopy.
    - inversion Hcopy; subst. constructor.
    - cbn [copy_blocks] in Hcopy.
      destruct (copy_block table tmp body) as [[body' one]|] eqn:Hbody; [|discriminate].
      destruct (copy_blocks table tmp rest) as [[tail checks]|] eqn:Htail;
        [|discriminate].
      inversion Hcopy; subst. constructor.
      + eapply copy_block_imp. exact Hbody.
      + eapply IH. reflexivity.
  Qed.

  (** Copy insertion keeps the function header and produces imperative form. *)
  Lemma copies_shape : forall s p, copies s = Some p ->
    entry _ _ _ p = entry _ _ _ s /\ inputs _ _ _ p = inputs _ _ _ s /\ imp_form p.
  Proof.
    intros s p Hcopies. unfold copies, copy_stage in Hcopies.
    destruct (params_index (blocks _ _ _ s)) as [table|]; [|discriminate].
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|]; try discriminate.
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|] eqn:Hblocks; [|discriminate].
    inversion Hcopies; subst. split; [reflexivity|]. split; [reflexivity|].
    unfold imp_form. cbn [blocks]. eapply copy_blocks_imp. exact Hblocks.
  Qed.

  (** Every successful destruction has imperative form. *)
  Lemma destroy_imp : forall s p, destroy s = Some p -> imp_form p.
  Proof.
    intros s p Hdestroy. unfold destroy in Hdestroy.
    destruct (split s) as [split_s|]; [|discriminate].
    exact (proj2 (proj2 (copies_shape split_s p Hdestroy))).
  Qed.
  Lemma destroy_correct : forall s p, ssa_wf s -> destroy s = Some p ->
    forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) p ins = r) /\
      (run_with O.eval O.test n p ins = r -> run_with O.eval O.test n s ins = r).
  Proof. Admitted. (* STUB *)
End Destroy.

Module DestroyT (O : OPS)
    (K : KEY_T with Definition t := O.K) (G : KEY_T with Definition t := O.G)
    (P : TYPE with Definition t := func positive O.K O.G)
    (PM : PARMOVE_T) (OL : LAWS O)
    <: DESTROY_ALL O K G P PM OL.
  Include Destroy O K G P PM OL.
  TimeFun fresh_after.
  TimeFun split_edge.
  TimeFun split_exit.
  TimeFun split_blocks.
  TimeFun split.
  TimeFun distinct_vars.
  TimeFun params_index.
  TimeFun pair_moves.
  TimeFun move_code.
  TimeFun moves_ok.
  TimeFun empty_params.
  TimeFun copy_block.
  TimeFun copy_blocks.
  TimeFun copy_stage.
  TimeFun copies.
  TimeFun checked_moves.
  TimeFun destroy.
  Definition c_ds : N := 1. (* STUB *)
  Definition destroy_work (s : P.t) :=
    function_size s + destroy_edge_args s + split_count s + 1.
  Lemma T_destroy_le : forall s,
    (T_destroy s <= c_ds * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma destroy_bigO : bigO (fun _ : P.t => True)
    (fun s => N.of_nat (destroy_work s * (function_width s + 1))) T_destroy.
  Proof. Admitted. (* STUB *)
  Definition k_split : N := 1. (* STUB *)
  Definition k_copies : N := 1. (* STUB *)
  Definition k_wrap : N := 1. (* STUB *)
  Definition entered_agree (s p : P.t) (ss sp : machine_state O.C) :=
    let '(bs, actuals_s, es) := ss in
    let '(bp, actuals_p, ep) := sp in
    bs = bp /\
    match find_block bs (blocks _ _ _ s), find_block bp (blocks _ _ _ p) with
    | None, None => True
    | Some sb, Some pb =>
        match bind_vars (params _ _ _ sb) actuals_s es,
          bind_vars (params _ _ _ pb) actuals_p ep with
        | None, None => True
        | Some entered_s, Some entered_p =>
            forall x, In x (function_vars s) -> lookup x entered_s = lookup x entered_p
        | _, _ => False
        end
    | _, _ => False
    end.
  Definition copy_outcomes s p (os op : machine_state O.C + result O.C) :=
    match os, op with
    | inl ss, inl sp => entered_agree s p ss sp
    | inr rs, inr rp => rs = rp
    | _, _ => False
    end.
  Lemma F1_destroy_phases : forall s, destroy s =
    match split s with None => None | Some split_s => copies split_s end.
  Proof.
    reflexivity.
  Qed.
  Lemma F2_split_preserves : forall s split_s, ssa_wf s -> split s = Some split_s ->
    ssa_wf split_s /\ forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) split_s ins = r) /\
      (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  Proof. Admitted. (* STUB *)
  Lemma F3_moves_checked : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par) /\
      PM.check_moves par tmp sq = true.
  Proof.
    intros s p par tmp sq Hcopies Hin.
    pose proof (checked_moves_good s) as Hchecked.
    rewrite Forall_forall in Hchecked. exact (Hchecked (par, tmp, sq) Hin).
  Qed.
  Lemma F4_edge_copy_sim : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) -> forall (e : positive -> option O.C) x,
      x <> tmp -> exec_seq sq e x = exec_par par e x.
  Proof.
    intros s p par tmp sq Hcopies Hin e x Hneq.
    destruct (F3_moves_checked s p par tmp sq Hcopies Hin) as [Hdistinct [Hfresh Hchecked]].
    exact (PM.check_moves_sound par tmp sq Hdistinct Hfresh Hchecked O.C e x Hneq).
  Qed.
  Lemma F5_block_sim : forall s p ss sp, ssa_wf s -> copies s = Some p ->
    entered_agree s p ss sp ->
    copy_outcomes s p (step O.eval O.test s ss) (step O.eval O.test p sp).
  Proof. Admitted. (* STUB *)
  Lemma F6_copies_run : forall s p, ssa_wf s -> copies s = Some p ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof. Admitted. (* STUB *)
  Lemma F7_copies_imp : forall s p, copies s = Some p -> imp_form p.
  Proof.
    intros s p Hcopies. exact (proj2 (proj2 (copies_shape s p Hcopies))).
  Qed.
  Lemma F8_run_mono : forall (p : P.t) n m ins r, n <= m -> r <> Timeout ->
    run_with O.eval O.test n p ins = r -> run_with O.eval O.test m p ins = r.
  Proof.
    apply run_with_mono.
  Qed.
  Lemma T1_split : forall s,
    (T_split s <= k_split * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma F9_moves_size : forall s split_s, split s = Some split_s ->
    fold_right (fun mc n => length (fst (fst mc)) + 1 + n) 0 (checked_moves split_s) <=
      destroy_work s /\
    forall par tmp sq, In (par, tmp, sq) (checked_moves split_s) ->
      sq = PM.seq par tmp /\ bits_of par + Pos.size_nat tmp <= 2 * (function_width s + 1).
  Proof. Admitted. (* STUB *)
  Lemma T2_copies : forall s split_s, split s = Some split_s ->
    (T_copies split_s <= k_copies * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1) +
      fold_right N.add 0%N (map (fun mc =>
        PM.T_seq (fst (fst mc)) (snd (fst mc)) +
        PM.T_check_moves (fst (fst mc)) (snd (fst mc)) (snd mc))%N
        (checked_moves split_s)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_wrapper : forall s,
    (T_destroy s <= T_split s +
      match split s with None => k_wrap | Some split_s => T_copies split_s + k_wrap end)%N.
  Proof. Admitted. (* STUB *)
End DestroyT.
