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

(** Reading a row depends only on the variables occurring in that row. *)
Lemma read_vars_agree {C} : forall xs (e f : env C),
  (forall x, In x xs -> lookup x e = lookup x f) -> read_vars e xs = read_vars f xs.
Proof.
  induction xs as [|x xs IH]; intros e f Hagree; [reflexivity|].
  cbn [read_vars]. rewrite (Hagree x (or_introl eq_refl)), (IH e f).
  - reflexivity.
  - intros y Hin. apply Hagree. now right.
Qed.

(** A fresh binding leaves reads of other variables unchanged. *)
Lemma read_vars_other {C} : forall xs x c (e : env C),
  ~ In x xs -> read_vars ((x, c) :: e) xs = read_vars e xs.
Proof.
  intros xs x c e Hfresh. apply read_vars_agree.
  intros y Hin. cbn [lookup]. destruct (Pos.eqb y x) eqn:Heq; [|reflexivity].
  apply Pos.eqb_eq in Heq. subst y. contradiction.
Qed.

(** Executing concatenated instruction lists agrees with sequential execution. *)
Lemma exec_code_append {K C} (eval : K -> list C -> option C) :
  forall left right (e : env C), exec_code eval (left ++ right) e =
    match exec_code eval left e with None => None | Some out => exec_code eval right out end.
Proof.
  induction left as [|[[dst op] args] rest IH]; intros right e; [reflexivity|].
  cbn [app exec_code]. destruct (read_vars e args) as [values|]; [|reflexivity].
  destruct (eval op values) as [value|]; [apply IH|reflexivity].
Qed.

(** The same instructions preserve agreement on a set containing all their reads. *)
Lemma exec_code_agree {K C} (eval : K -> list C -> option C) :
  forall instructions universe (e f : env C),
  (forall dst op args, In (dst, op, args) instructions -> incl args universe) ->
  (forall x, In x universe -> lookup x e = lookup x f) ->
  match exec_code eval instructions e, exec_code eval instructions f with
  | None, None => True
  | Some out, Some out' => forall x, In x universe -> lookup x out = lookup x out'
  | _, _ => False
  end.
Proof.
  induction instructions as [|[[dst op] args] rest IH]; intros universe e f Hreads Hagree.
  - exact Hagree.
  - cbn [exec_code].
    rewrite (read_vars_agree args e f).
    2: { intros x Hin. apply Hagree. exact (Hreads dst op args (or_introl eq_refl) x Hin). }
    destruct (read_vars f args) as [values|]; [|exact I].
    destruct (eval op values) as [value|]; [|exact I].
    apply IH.
    + intros dst' op' args' Hin. apply (Hreads dst' op' args'). now right.
    + intros x Hin. cbn [lookup]. destruct (Pos.eqb x dst); [reflexivity|].
      apply Hagree. exact Hin.
Qed.

(** Binding parameters leaves variables outside the parameter list unchanged. *)
Lemma bind_vars_other {C} : forall xs values (e out : env C),
  bind_vars xs values e = Some out ->
  forall x, ~ In x xs -> lookup x out = lookup x e.
Proof.
  induction xs as [|y ys IH]; intros values e out Hbind x Hfresh.
  - destruct values; inversion Hbind; reflexivity.
  - destruct values as [|value values]; [discriminate|].
    cbn [bind_vars] in Hbind.
    rewrite (IH values ((y, value) :: e) out Hbind x).
    + cbn [lookup]. destruct (Pos.eqb x y) eqn:Heq; [|reflexivity].
      apply Pos.eqb_eq in Heq. subst y. exfalso. apply Hfresh. now left.
    + intro Hin. apply Hfresh. now right.
Qed.

(** A distinct parameter retains the value supplied at its own position. *)
Lemma bind_vars_nth {C} : forall xs values (e out : env C) i x c,
  NoDup xs -> nth_error xs i = Some x -> nth_error values i = Some c ->
  bind_vars xs values e = Some out -> lookup x out = Some c.
Proof.
  induction xs as [|y ys IH]; intros values e out i x c Hdistinct Hx Hc Hbind.
  - destruct i; discriminate.
  - destruct values as [|value values]; [discriminate|].
    inversion Hdistinct as [|head tail Hfresh Htail]; subst.
    cbn [bind_vars] in Hbind. destruct i as [|i].
    + inversion Hx; inversion Hc; subst.
      rewrite (bind_vars_other ys values ((x, c) :: e) out Hbind x Hfresh).
      cbn [lookup]. now rewrite Pos.eqb_refl.
    + eapply IH; eassumption.
Qed.

(** A successful row read supplies the original value at every row position. *)
Lemma read_vars_nth {C} : forall xs (e : env C) values i x,
  read_vars e xs = Some values -> nth_error xs i = Some x ->
  exists c, nth_error values i = Some c /\ lookup x e = Some c.
Proof.
  induction xs as [|y ys IH]; intros e values i x Hread Hx.
  - destruct i; discriminate.
  - cbn [read_vars] in Hread.
    destruct (lookup y e) as [value|] eqn:Hvalue; [|discriminate].
    destruct (read_vars e ys) as [tail|] eqn:Htail; [|discriminate].
    inversion Hread; subst values. destruct i as [|i].
    + inversion Hx; subst x. exists value. split; [reflexivity|exact Hvalue].
    + exact (IH e tail i x Htail Hx).
Qed.

(** Every member of a successfully read row has a value. *)
Lemma read_vars_defined {C} : forall xs (e : env C) values,
  read_vars e xs = Some values -> forall x, In x xs -> exists c, lookup x e = Some c.
Proof.
  intros xs e values Hread x Hin.
  apply In_nth_error in Hin as [i Hi].
  destruct (read_vars_nth xs e values i x Hread Hi) as [c [Hc Hvalue]].
  exists c. exact Hvalue.
Qed.

(** Successful reads preserve the number of operands. *)
Lemma read_vars_length {C} : forall xs (e : env C) values,
  read_vars e xs = Some values -> length xs = length values.
Proof.
  induction xs as [|x xs IH]; intros e values Hread.
  - inversion Hread. reflexivity.
  - cbn [read_vars] in Hread.
    destruct (lookup x e) as [value|]; [|discriminate].
    destruct (read_vars e xs) as [tail|] eqn:Htail; [|discriminate].
    inversion Hread; subst values. cbn [length]. f_equal. eapply IH. exact Htail.
Qed.

(** Equal row lengths suffice for parameter binding to succeed. *)
Lemma bind_vars_exists {C} : forall xs values (e : env C),
  length xs = length values -> exists out, bind_vars xs values e = Some out.
Proof.
  induction xs as [|x xs IH]; intros values e Hlength.
  - destruct values; [exists e; reflexivity|discriminate].
  - destruct values as [|value values]; [discriminate|].
    cbn [bind_vars]. apply IH. cbn [length] in Hlength. now injection Hlength.
Qed.

(** A distinct parallel destination receives its listed original source. *)
Lemma exec_par_hit {A} : forall par (rho : positive -> option A) dst src,
  NoDup (map fst par) -> In (dst, src) par -> exec_par par rho dst = rho src.
Proof.
  induction par as [|[x y] par IH]; intros rho dst src Hdistinct Hin; [contradiction|].
  inversion Hdistinct as [|head tail Hfresh Htail]; subst.
  cbn [exec_par]. destruct Hin as [Heq|Hin].
  - inversion Heq; subst. now rewrite Pos.eqb_refl.
  - destruct (Pos.eqb dst x) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst dst. exfalso. apply Hfresh. apply in_map_iff.
      exists (x, src). split; [reflexivity|exact Hin].
    + apply IH; assumption.
Qed.

(** Variables outside a parallel destination row retain their previous values. *)
Lemma exec_par_miss {A} : forall par (rho : positive -> option A) x,
  ~ In x (map fst par) -> exec_par par rho x = rho x.
Proof.
  induction par as [|[dst src] par IH]; intros rho x Hfresh; [reflexivity|].
  cbn [exec_par]. destruct (Pos.eqb x dst) eqn:Heq.
  - apply Pos.eqb_eq in Heq. subst dst. exfalso. apply Hfresh. now left.
  - apply IH. intro Hin. apply Hfresh. now right.
Qed.

(** Binding a row of read values agrees with the associated parallel assignment. *)
Lemma bind_moves_agree {C} : forall par values (e out : env C),
  NoDup (map fst par) -> read_vars e (map snd par) = Some values ->
  bind_vars (map fst par) values e = Some out ->
  forall x, lookup x out = exec_par par (fun y => lookup y e) x.
Proof.
  intros par values e out Hdistinct Hread Hbind x.
  destruct (in_dec Pos.eq_dec x (map fst par)) as [Hin|Hfresh].
  - apply in_map_iff in Hin as [[dst src] [Heq Hin]]. cbn [fst] in Heq. subst dst.
    pose proof Hin as Hindex. apply In_nth_error in Hindex as [i Hi].
    assert (Hdst : nth_error (map fst par) i = Some x).
    { rewrite nth_error_map, Hi. reflexivity. }
    assert (Hsrc : nth_error (map snd par) i = Some src).
    { rewrite nth_error_map, Hi. reflexivity. }
    destruct (read_vars_nth _ e values i src Hread Hsrc) as [c [Hc Hvalue]].
    rewrite (bind_vars_nth _ values e out i x c Hdistinct Hdst Hc Hbind).
    rewrite (exec_par_hit par (fun y => lookup y e) x src Hdistinct Hin).
    symmetry. exact Hvalue.
  - rewrite (bind_vars_other _ values e out Hbind x Hfresh).
    symmetry. exact (exec_par_miss par (fun y => lookup y e) x Hfresh).
Qed.

(** Parallel assignment observes only its queried variable and its source row. *)
Lemma exec_par_agree {A} : forall par (rho sigma : positive -> option A) x,
  (forall y, y = x \/ In y (map snd par) -> rho y = sigma y) ->
  exec_par par rho x = exec_par par sigma x.
Proof.
  induction par as [|[dst src] par IH]; intros rho sigma x Hagree.
  - apply Hagree. now left.
  - cbn [exec_par]. destruct (Pos.eqb x dst).
    + apply Hagree. right. now left.
    + apply IH. intros y [Heq|Hin].
      * apply Hagree. now left.
      * apply Hagree. right. now right.
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
  (** The preflight copies read the whole source row without changing its values. *)
  Lemma preflight_run : forall actuals tmp (e : env O.C), ~ In tmp actuals ->
    exec_code O.eval (move_code (map (fun src => (tmp, src)) actuals)) e =
      match read_vars e actuals with
      | None => None
      | Some values => Some (fold_left (fun acc c => (tmp, c) :: acc) values e)
      end.
  Proof.
    induction actuals as [|src actuals IH]; intros tmp e Hfresh; [reflexivity|].
    cbn [move_code map exec_code read_vars].
    destruct (lookup src e) as [value|] eqn:Hsource; [|reflexivity].
    rewrite OL.eval_mov.
    rewrite IH.
    - rewrite read_vars_other.
      + destruct (read_vars e actuals); reflexivity.
      + intro Hin. apply Hfresh. now right.
    - intro Hin. apply Hfresh. now right.
  Qed.

  (** Repeated writes of the temporary preserve every other lookup. *)
  Lemma preflight_agree : forall values (e : env O.C) tmp x, x <> tmp ->
    lookup x (fold_left (fun acc c => (tmp, c) :: acc) values e) = lookup x e.
  Proof.
    induction values as [|c values IH]; intros e tmp x Hneq; [reflexivity|].
    cbn [fold_left]. rewrite IH by exact Hneq. cbn [lookup].
    destruct (Pos.eqb x tmp) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq. contradiction.
  Qed.

  (** A nonempty successful preflight initializes the temporary. *)
  Lemma preflight_defined : forall values (e : env O.C) tmp, values <> [] ->
    exists c, lookup tmp (fold_left (fun acc c => (tmp, c) :: acc) values e) = Some c.
  Proof.
    induction values as [|c values IH]; intros e tmp Hnonempty; [contradiction|].
    cbn [fold_left]. destruct values as [|d rest].
    - exists c. cbn [fold_left lookup]. now rewrite Pos.eqb_refl.
    - apply IH. discriminate.
  Qed.

  (** Defined move operands make concrete move instructions agree with sequential assignment. *)
  Lemma move_code_defined : forall sq allowed (e : env O.C),
    (forall m, In m sq -> In (snd m) allowed) ->
    (forall x, In x allowed -> exists c, lookup x e = Some c) ->
    exists out, exec_code O.eval (move_code sq) e = Some out /\
      forall x, lookup x out = exec_seq sq (fun y => lookup y e) x.
  Proof.
    induction sq as [|[dst src] rest IH]; intros allowed e Hreads Hdefined.
    - exists e. split; reflexivity.
    - destruct (Hdefined src (Hreads (dst, src) (or_introl eq_refl))) as [c Hsource].
      assert (Htail : forall m, In m rest -> In (snd m) allowed).
      { intros m Hin. apply Hreads. now right. }
      assert (Hdefined' : forall x, In x allowed -> exists c',
          lookup x ((dst, c) :: e) = Some c').
      { intros x Hin. cbn [lookup]. destruct (Pos.eqb x dst).
        - exists c. reflexivity.
        - apply Hdefined. exact Hin. }
      destruct (IH allowed ((dst, c) :: e) Htail Hdefined') as [out [Hrun Hagree]].
      exists out. split.
      + cbn [move_code map exec_code read_vars]. rewrite Hsource, OL.eval_mov. exact Hrun.
      + intro x. rewrite Hagree. cbn [exec_seq]. rewrite Hsource. reflexivity.
  Qed.

  (** Checked copies preserve missing-read failures and implement the parallel assignment. *)
  Lemma checked_copy_run : forall par tmp (e : env O.C), par <> [] ->
    NoDup (map fst par) -> ~ In tmp (map fst par ++ map snd par) ->
    PM.check_moves par tmp (PM.seq par tmp) = true ->
    match read_vars e (map snd par) with
    | None => exec_code O.eval
        (move_code (map (fun src => (tmp, src)) (map snd par)) ++
          move_code (PM.seq par tmp)) e = None
    | Some values => exists out, exec_code O.eval
        (move_code (map (fun src => (tmp, src)) (map snd par)) ++
          move_code (PM.seq par tmp)) e = Some out /\
        forall x, x <> tmp -> lookup x out = exec_par par (fun y => lookup y e) x
    end.
  Proof.
    intros par tmp e Hnonempty Hdistinct Hfresh Hchecked.
    assert (Hsources : ~ In tmp (map snd par)).
    { intro Hin. apply Hfresh. apply in_or_app. now right. }
    rewrite exec_code_append, preflight_run by exact Hsources.
    destruct (read_vars e (map snd par)) as [values|] eqn:Hread; [|reflexivity].
    assert (Hvalues : values <> []).
    { intro Heq. subst values.
      pose proof (read_vars_length _ e [] Hread) as Hlength.
      rewrite length_map in Hlength. destruct par; [contradiction|discriminate]. }
    set (scratch := fold_left (fun acc c => (tmp, c) :: acc) values e).
    assert (Hdefined : forall x, In x (tmp :: map snd par) ->
        exists c, lookup x scratch = Some c).
    { intros x [Heq|Hin].
      - subst x. apply preflight_defined. exact Hvalues.
      - destruct (read_vars_defined _ e values Hread x Hin) as [c Hvalue].
        exists c. unfold scratch. rewrite preflight_agree; [exact Hvalue|].
        intro Heq. subst x. contradiction. }
    assert (Hreads : forall m, In m (PM.seq par tmp) -> In (snd m) (tmp :: map snd par)).
    { intros m Hin. destruct (PM.seq_ids par tmp m Hin) as [Hdst [Hsrc|Htmp]].
      - now right.
      - now left. }
    destruct (move_code_defined (PM.seq par tmp) (tmp :: map snd par)
      scratch Hreads Hdefined) as [out [Hrun Hagree]].
    exists out. split; [exact Hrun|].
    intros x Hneq. rewrite Hagree.
    rewrite (PM.check_moves_sound par tmp (PM.seq par tmp)
      Hdistinct Hfresh Hchecked O.C (fun y => lookup y scratch) x Hneq).
    apply exec_par_agree. intros y [Heq|Hin].
    - subst y. apply preflight_agree. exact Hneq.
    - apply preflight_agree. intro Heq. subst y. contradiction.
  Qed.

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

  Definition finish_exit (e : exit positive O.G) (finished : env O.C)
      : machine_state O.C + result O.C :=
    match e with
    | Jump next actuals =>
      match read_vars finished actuals with
      | Some values => inl (next, values, finished)
      | None => inr Wrong
      end
    | Branch guard operands yes yes_args no no_args =>
      match read_vars finished operands with
      | None => inr Wrong
      | Some values =>
        match O.test guard values with
        | None => inr Wrong
        | Some choice =>
          let next := if choice then yes else no in
          let actuals := if choice then yes_args else no_args in
          match read_vars finished actuals with
          | Some passed => inl (next, passed, finished)
          | None => inr Wrong
          end
        end
      end
    | Return values =>
      match read_vars finished values with
      | Some returned => inr (Returned returned)
      | None => inr Wrong
      end
    end.

  Definition execute_body (body : block positive O.K O.G) (entered : env O.C) :=
    match exec_code O.eval (code _ _ _ body) entered with
    | None => inr Wrong
    | Some finished => finish_exit (term _ _ _ body) finished
    end.

  (** Pairing exact rows recovers both original rows. *)
  Lemma pair_moves_rows : forall formals actuals par, pair_moves formals actuals = Some par ->
    map fst par = formals /\ map snd par = actuals.
  Proof.
    induction formals as [|x xs IH]; intros actuals par Hpair.
    - destruct actuals; inversion Hpair. split; reflexivity.
    - destruct actuals as [|y ys]; [discriminate|]. cbn [pair_moves] in Hpair.
      destruct (pair_moves xs ys) as [tail|] eqn:Htail; [|discriminate].
      inversion Hpair; subst par. destruct (IH ys tail Htail) as [Hleft Hright].
      cbn [map fst snd]. split; f_equal; assumption.
  Qed.

  (** The allocated identifier is greater than every identifier in its input row. *)
  Lemma fresh_after_gt : forall xs x, In x xs -> (x < fresh_after xs)%positive.
  Proof.
    intros xs x Hin. unfold fresh_after. apply Pos.lt_succ_r.
    induction xs as [|y ys IH]; [contradiction|]. cbn [fold_right].
    destruct Hin as [Heq|Hin].
    - subst y. apply Pos.le_max_l.
    - eapply Pos.le_trans; [apply IH; exact Hin|apply Pos.le_max_r].
  Qed.

  (** A fresh identifier does not occur in the row used to allocate it. *)
  Lemma fresh_after_fresh : forall xs, ~ In (fresh_after xs) xs.
  Proof.
    intros xs Hin. exact (Pos.lt_irrefl _ (fresh_after_gt xs _ Hin)).
  Qed.

  (** The parameter index follows the same first-block convention as the interpreter. *)
  Lemma params_index_find : forall bs table, params_index bs = Some table -> forall id,
    trie_get id table = option_map (params positive O.K O.G) (find_block id bs).
  Proof.
    induction bs as [|[id body] rest IH]; intros table Hindex query.
    - inversion Hindex; subst table. apply PTrie.get_empty.
    - cbn [params_index] in Hindex.
      destruct (distinct_vars (params _ _ _ body) Empty); [|discriminate].
      destruct (params_index rest) as [tail|] eqn:Htail; [|discriminate].
      inversion Hindex; subst table. cbn [find_block].
      destruct (Pos.eqb query id) eqn:Heq.
      + apply Pos.eqb_eq in Heq. subst query. apply PTrie.get_set_same.
      + apply Pos.eqb_neq in Heq. rewrite PTrie.get_set_other by exact Heq.
        apply IH. reflexivity.
  Qed.

  (** Each looked-up output block is the rewrite of the corresponding first input block. *)
  Lemma copy_blocks_find : forall table tmp bs out checked,
    copy_blocks table tmp bs = Some (out, checked) -> forall id,
    match find_block id bs with
    | None => find_block id out = None
    | Some body => exists body' one,
        find_block id out = Some body' /\ copy_block table tmp body = Some (body', one)
    end.
  Proof.
    intros table tmp bs. induction bs as [|[id body] rest IH]; intros out checked Hcopy query.
    - inversion Hcopy; subst. reflexivity.
    - cbn [copy_blocks] in Hcopy.
      destruct (copy_block table tmp body) as [[body' one]|] eqn:Hbody; [|discriminate].
      destruct (copy_blocks table tmp rest) as [[tail checks]|] eqn:Htail; [|discriminate].
      inversion Hcopy; subst. cbn [find_block].
      destruct (Pos.eqb query id).
      + exists body', one. split; [reflexivity|exact Hbody].
      + eapply IH. reflexivity.
  Qed.

  (** The copy wrapper exposes its successful index and rewriting passes. *)
  Lemma copies_data : forall s p, copies s = Some p -> exists table checked,
    params_index (blocks _ _ _ s) = Some table /\
    trie_get (entry _ _ _ s) table = Some [] /\
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) /\
    entry _ _ _ p = entry _ _ _ s /\ inputs _ _ _ p = inputs _ _ _ s.
  Proof.
    intros s p Hcopies. unfold copies, copy_stage in Hcopies.
    destruct (params_index (blocks _ _ _ s)) as [table|] eqn:Hindex; [|discriminate].
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|] eqn:Hentry; try discriminate.
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|] eqn:Hblocks; [|discriminate].
    inversion Hcopies; subst p. exists table, checked. repeat split; try assumption.
  Qed.

  (** A successful block lookup identifies an actual source block. *)
  Lemma find_source_block : forall (bs : list (positive * block positive O.K O.G)) id body,
    find_block id bs = Some body -> In (id, body) bs.
  Proof.
    induction bs as [|[key head] rest IH]; intros id body Hfind; [discriminate|].
    cbn [find_block] in Hfind. destruct (Pos.eqb id key) eqn:Heq.
    - apply Pos.eqb_eq in Heq. inversion Hfind; subst. now left.
    - right. apply IH. exact Hfind.
  Qed.

  (** Each operand of a listed instruction belongs to the source variable universe. *)
  Lemma listed_code_args : forall (s : P.t) id body dst op args,
    In (id, body) (blocks _ _ _ s) -> In (dst, op, args) (code _ _ _ body) ->
    incl args (function_vars s).
  Proof.
    intros s id body dst op args Hbody Hin x Hx. unfold function_vars.
    apply in_or_app. right. apply in_flat_map. exists (id, body). split; [exact Hbody|].
    cbn [snd]. apply in_or_app. right. apply in_or_app. left.
    apply in_flat_map. exists (dst, op, args). split; [exact Hin|]. cbn. now right.
  Qed.

  (** Every operand of a listed exit belongs to the source variable universe. *)
  Lemma listed_exit_uses : forall (s : P.t) id body, In (id, body) (blocks _ _ _ s) ->
    incl (exit_uses (term _ _ _ body)) (function_vars s).
  Proof.
    intros s id body Hbody x Hx. unfold function_vars.
    apply in_or_app. right. apply in_flat_map. exists (id, body). split; [exact Hbody|].
    cbn [snd]. apply in_or_app. right. apply in_or_app. now right.
  Qed.

  (** Successful empty-row checks identify the exact row stored in the index. *)
  Lemma empty_params_sound : forall table target, empty_params table target = true ->
    trie_get target table = Some [].
  Proof.
    intros table target Hempty. unfold empty_params in Hempty.
    destruct (trie_get target table) as [[|x xs]|]; try discriminate. reflexivity.
  Qed.

  (** Empty edge rows re-establish the state relation without changing either environment. *)
  Lemma entered_empty : forall s p table checked target es ep,
    params_index (blocks _ _ _ s) = Some table ->
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) -> trie_get target table = Some [] ->
    (forall x, In x (function_vars s) -> lookup x es = lookup x ep) ->
    entered_agree s p (target, [], es) (target, [], ep).
  Proof.
    intros s p table checked target es ep Hindex Hblocks Hrow Hagree.
    rewrite (params_index_find _ table Hindex target) in Hrow.
    destruct (find_block target (blocks _ _ _ s)) as [body|] eqn:Hsource;
      [|discriminate].
    cbn [option_map] in Hrow. injection Hrow as Hparams.
    pose proof (copy_blocks_find _ _ _ _ _ Hblocks target) as Hfind.
    rewrite Hsource in Hfind. destruct Hfind as [body' [one [Htarget Hcopy]]].
    destruct (copy_block_imp _ _ _ _ _ Hcopy) as [Hparams' Hexit].
    unfold entered_agree. rewrite Hsource, Htarget, Hparams, Hparams'.
    split; [reflexivity|exact Hagree].
  Qed.

  (** Concrete parameter binding and the copied parallel assignment enter matching states. *)
  Lemma entered_moves : forall s p table checked target par values es ep,
    params_index (blocks _ _ _ s) = Some table ->
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) -> trie_get target table = Some (map fst par) ->
    NoDup (map fst par) -> read_vars es (map snd par) = Some values ->
    (forall x, In x (function_vars s) ->
      lookup x ep = exec_par par (fun y => lookup y es) x) ->
    entered_agree s p (target, values, es) (target, [], ep).
  Proof.
    intros s p table checked target par values es ep Hindex Hblocks Hrow Hdistinct Hread Hagree.
    rewrite (params_index_find _ table Hindex target) in Hrow.
    destruct (find_block target (blocks _ _ _ s)) as [body|] eqn:Hsource;
      [|discriminate].
    cbn [option_map] in Hrow. injection Hrow as Hparams.
    pose proof (copy_blocks_find _ _ _ _ _ Hblocks target) as Hfind.
    rewrite Hsource in Hfind. destruct Hfind as [body' [one [Htarget Hcopy]]].
    destruct (copy_block_imp _ _ _ _ _ Hcopy) as [Hparams' Hexit].
    assert (Hlength : length (map fst par) = length values).
    { rewrite length_map. pose proof (read_vars_length _ es values Hread) as Hlength.
      now rewrite length_map in Hlength. }
    destruct (bind_vars_exists _ values es Hlength) as [entered Hbind].
    unfold entered_agree. rewrite Hsource, Htarget, Hparams, Hparams', Hbind.
    split; [reflexivity|]. intros x Hin. rewrite (Hagree x Hin).
    exact (bind_moves_agree par values es entered Hdistinct Hread Hbind x).
  Qed.

  (** A checked nonempty jump has the same outcome after its concrete copy sequence. *)
  Lemma checked_jump_sim : forall s p table checked target par es ep,
    params_index (blocks _ _ _ s) = Some table ->
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) -> trie_get target table = Some (map fst par) ->
    par <> [] -> moves_ok par (fresh_after (function_vars s)) = true ->
    PM.check_moves par (fresh_after (function_vars s))
      (PM.seq par (fresh_after (function_vars s))) = true ->
    incl (map snd par) (function_vars s) ->
    (forall x, In x (function_vars s) -> lookup x es = lookup x ep) ->
    copy_outcomes s p (finish_exit (Jump target (map snd par)) es)
      (match exec_code O.eval
        (move_code (map (fun src => (fresh_after (function_vars s), src)) (map snd par)) ++
          move_code (PM.seq par (fresh_after (function_vars s)))) ep with
      | None => inr Wrong
      | Some out => finish_exit (Jump target []) out
      end).
  Proof.
    intros s p table checked target par es ep Hindex Hblocks Hrow Hnonempty
      Hvalid Hchecked Hsources Hagree.
    destruct (moves_ok_sound _ _ Hvalid) as [Hdistinct Hfresh].
    pose proof (checked_copy_run par (fresh_after (function_vars s)) ep
      Hnonempty Hdistinct Hfresh Hchecked) as Hrun.
    assert (Hread : read_vars es (map snd par) = read_vars ep (map snd par)).
    { apply read_vars_agree. intros x Hin. apply Hagree. now apply Hsources. }
    unfold finish_exit at 1. rewrite Hread.
    destruct (read_vars ep (map snd par)) as [values|] eqn:Hvalues.
    - destruct Hrun as [out [Hrun Hout]]. rewrite Hrun.
      cbn [finish_exit read_vars copy_outcomes].
      eapply entered_moves; [exact Hindex|exact Hblocks|exact Hrow|exact Hdistinct| |].
      + rewrite Hread. reflexivity.
      + intros x Hin. rewrite Hout.
        * apply exec_par_agree. intros y [Heq|Hsrc].
          -- subst y. symmetry. apply Hagree. exact Hin.
          -- symmetry. apply Hagree. now apply Hsources.
        * intro Heq. subst x. exact (fresh_after_fresh _ Hin).
    - rewrite Hrun. reflexivity.
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
