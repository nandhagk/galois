(** * SSA destruction with checked edge copies

    Branch edges receive private copy blocks before parameters become checked moves.
    For example, a swap is copied on its taken edge using a fresh temporary.
    Builds on: Lang, positive-key tries, ParMoveSig and DestroySig. *)

From Stdlib Require Import List Arith PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
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
    if distinct_vars (map fst par) Empty then
      negb (existsb (fun x => Pos.eqb tmp x) (map fst par ++ map snd par))
    else false.

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
          if moves_ok par tmp then
            if PM.check_moves par tmp sq then
              (* Reading every actual preserves errors even when a self-copy is omitted. *)
              let reads := move_code (map (fun src => (tmp, src)) actuals) in
              Some (Block _ _ _ [] (code _ _ _ body ++ reads ++ move_code sq)
                (Jump target []), Some (par, tmp, sq))
            else None
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

  (** Lazy freshness checking preserves the original conjunction. *)
  Lemma moves_ok_andb par tmp :
    moves_ok par tmp = andb (distinct_vars (map fst par) Empty)
      (negb (existsb (fun x => Pos.eqb tmp x) (map fst par ++ map snd par))).
  Proof.
    reflexivity.
  Qed.

  (** The explicit move precondition check establishes uniqueness and temporary freshness. *)
  Lemma moves_ok_sound : forall par tmp, moves_ok par tmp = true ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par).
  Proof.
    intros par tmp Hchecked. rewrite moves_ok_andb in Hchecked.
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

  (** Nested option checks preserve the result of their conjunction. *)
  Lemma copy_check_andb {A} (a b : bool) (out : option A) :
    (if a then if b then out else None else None) =
      if andb a b then out else None.
  Proof.
    destruct a; reflexivity.
  Qed.

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
      + rewrite copy_check_andb.
        destruct (andb (moves_ok (first :: par) tmp)
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
      + rewrite copy_check_andb.
        destruct (andb (moves_ok (first :: par) tmp)
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

  (** Parameter-free branch arms preserve the chosen successor and entered environment. *)
  Lemma empty_branch_sim : forall s p table checked guard operands yes no es ep,
    params_index (blocks _ _ _ s) = Some table ->
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) ->
    empty_params table yes = true -> empty_params table no = true ->
    incl operands (function_vars s) ->
    (forall x, In x (function_vars s) -> lookup x es = lookup x ep) ->
    copy_outcomes s p (finish_exit (Branch guard operands yes [] no []) es)
      (finish_exit (Branch guard operands yes [] no []) ep).
  Proof.
    intros s p table checked guard operands yes no es ep Hindex Hblocks Hyes Hno Huses Hagree.
    unfold finish_exit. rewrite (read_vars_agree operands es ep).
    2: { intros x Hin. apply Hagree. now apply Huses. }
    destruct (read_vars ep operands) as [values|]; [|reflexivity].
    destruct (O.test guard values) as [[|]|]; try reflexivity;
      cbn [read_vars copy_outcomes]; eapply entered_empty;
      try eassumption; apply empty_params_sound; assumption.
  Qed.

  (** Copy insertion appends instructions after the original block body. *)
  Lemma copy_block_prefix : forall table tmp body out one,
    copy_block table tmp body = Some (out, one) ->
    exists suffix, code _ _ _ out = code _ _ _ body ++ suffix.
  Proof.
    intros table tmp [formals instructions ending] out one Hcopy.
    destruct ending as [target actuals|guard operands yes yes_args no no_args|values];
      cbn [copy_block term code] in Hcopy.
    - destruct (trie_get target table) as [target_formals|]; [|discriminate].
      destruct (pair_moves target_formals actuals) as [[|first par]|]; try discriminate.
      + inversion Hcopy; subst. exists []. symmetry. apply app_nil_r.
      + rewrite copy_check_andb in Hcopy.
        destruct (andb (moves_ok (first :: par) tmp)
          (PM.check_moves (first :: par) tmp (PM.seq (first :: par) tmp))); [|discriminate].
        inversion Hcopy; subst. eexists. reflexivity.
    - destruct yes_args as [|x xs]; [|discriminate].
      destruct no_args as [|x xs]; [|discriminate].
      destruct (andb (empty_params table yes) (empty_params table no)); [|discriminate].
      inversion Hcopy; subst. exists []. symmetry. apply app_nil_r.
    - inversion Hcopy; subst. exists []. symmetry. apply app_nil_r.
  Qed.

  (** Rewriting a block preserves its result or the relation after successor binding. *)
  Lemma copy_body_sim : forall s p table checked id body body' one es ep,
    params_index (blocks _ _ _ s) = Some table ->
    copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) =
      Some (blocks _ _ _ p, checked) -> In (id, body) (blocks _ _ _ s) ->
    copy_block table (fresh_after (function_vars s)) body = Some (body', one) ->
    (forall x, In x (function_vars s) -> lookup x es = lookup x ep) ->
    copy_outcomes s p (execute_body body es) (execute_body body' ep).
  Proof.
    intros s p table checked id body body' one es ep Hindex Hblocks Hbody Hcopy Hagree.
    pose proof (exec_code_agree O.eval (code _ _ _ body) (function_vars s) es ep
      (fun dst op args Hin => listed_code_args s id body dst op args Hbody Hin) Hagree) as Hcode.
    destruct (exec_code O.eval (code _ _ _ body) es) as [finished|] eqn:Hsource;
      destruct (exec_code O.eval (code _ _ _ body) ep) as [finished'|] eqn:Htarget;
      try contradiction.
    - pose proof (listed_exit_uses s id body Hbody) as Huses.
      destruct body as [formals instructions ending]. cbn [code term] in Hsource, Htarget, Huses.
      unfold execute_body. cbn [code term]. rewrite Hsource.
      destruct ending as [target actuals|guard operands yes yes_args no no_args|values];
        cbn [copy_block term code] in Hcopy.
      + destruct (trie_get target table) as [target_formals|] eqn:Hrow; [|discriminate].
        destruct (pair_moves target_formals actuals) as [[|first par]|] eqn:Hpair;
          try discriminate.
        * destruct (pair_moves_rows _ _ _ Hpair) as [Hformals Hactuals].
          cbn [map] in Hformals, Hactuals. subst target_formals actuals.
          inversion Hcopy; subst. cbn [code term]. rewrite Htarget.
          cbn [finish_exit read_vars copy_outcomes]. eapply entered_empty; eassumption.
        * rewrite copy_check_andb in Hcopy.
          destruct (andb (moves_ok (first :: par) (fresh_after (function_vars s)))
            (PM.check_moves (first :: par) (fresh_after (function_vars s))
              (PM.seq (first :: par) (fresh_after (function_vars s))))) eqn:Hchecked;
            [|discriminate].
          apply andb_true_iff in Hchecked as [Hvalid Hchecked].
          destruct (pair_moves_rows _ _ _ Hpair) as [Hformals Hactuals].
          inversion Hcopy; subst. cbn [code term]. rewrite exec_code_append, Htarget.
          eapply checked_jump_sim.
          -- exact Hindex.
          -- exact Hblocks.
          -- exact Hrow.
          -- discriminate.
          -- exact Hvalid.
          -- exact Hchecked.
          -- exact Huses.
          -- exact Hcode.
      + destruct yes_args as [|x xs]; [|discriminate].
        destruct no_args as [|x xs]; [|discriminate].
        destruct (andb (empty_params table yes) (empty_params table no)) eqn:Hempty;
          [|discriminate].
        apply andb_true_iff in Hempty as [Hyes Hno].
        inversion Hcopy; subst. cbn [code term]. rewrite Htarget.
        eapply empty_branch_sim; try eassumption.
        intros x Hin. apply Huses. apply in_or_app. now left.
      + inversion Hcopy; subst. cbn [code term]. rewrite Htarget.
        unfold finish_exit. rewrite (read_vars_agree values finished finished').
        * destruct (read_vars finished' values); reflexivity.
        * intros x Hin. apply Hcode. apply Huses. exact Hin.
    - destruct (copy_block_prefix _ _ _ _ _ Hcopy) as [suffix Hprefix].
      unfold execute_body. rewrite Hsource, Hprefix, exec_code_append, Htarget. reflexivity.
  Qed.

  (** Successful copy insertion simulates a block from every pair of related entered states. *)
  Lemma copies_block_sim : forall s p ss sp, copies s = Some p ->
    entered_agree s p ss sp ->
    copy_outcomes s p (step O.eval O.test s ss) (step O.eval O.test p sp).
  Proof.
    intros s p [[id actuals] es] [[id' actuals'] ep] Hcopies Hagree.
    destruct (copies_data s p Hcopies) as [table [checked [Hindex [Hentry [Hblocks Hheader]]]]].
    unfold entered_agree in Hagree. destruct Hagree as [Hid Hagree]. subst id'.
    pose proof (copy_blocks_find _ _ _ _ _ Hblocks id) as Hfind.
    destruct (find_block id (blocks _ _ _ s)) as [body|] eqn:Hsource.
    - destruct Hfind as [body' [one [Htarget Hcopy]]]. rewrite Htarget in Hagree.
      unfold step. rewrite Hsource, Htarget.
      destruct (bind_vars (params _ _ _ body) actuals es) as [entered|] eqn:Hbind;
        destruct (bind_vars (params _ _ _ body') actuals' ep) as [entered'|] eqn:Hbind';
        try contradiction; [|reflexivity].
      change (copy_outcomes s p (execute_body body entered) (execute_body body' entered')).
      eapply copy_body_sim; try eassumption. eapply find_source_block. exact Hsource.
    - unfold step. rewrite Hsource, Hfind. reflexivity.
  Qed.

  (** Lockstep block simulation preserves every fuelled loop observation. *)
  Lemma copies_loop_run : forall s p, copies s = Some p -> forall n ss sp,
    entered_agree s p ss sp ->
    (match loop_fuel (step O.eval O.test s) n ss with inl _ => Timeout | inr r => r end) =
    (match loop_fuel (step O.eval O.test p) n sp with inl _ => Timeout | inr r => r end).
  Proof.
    intros s p Hcopies n. induction n as [|n IH]; intros ss sp Hagree; [reflexivity|].
    pose proof (copies_block_sim s p ss sp Hcopies Hagree) as Hstep.
    cbn [loop_fuel].
    destruct (step O.eval O.test s ss) as [ss'|rs];
      destruct (step O.eval O.test p sp) as [sp'|rp];
      cbn [copy_outcomes] in Hstep; try contradiction.
    - apply IH. exact Hstep.
    - exact Hstep.
  Qed.

  (** Copy insertion preserves all fuelled observations, including errors and timeouts. *)
  Lemma copies_run : forall s p, copies s = Some p ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof.
    intros s p Hcopies n ins.
    destruct (copies_data s p Hcopies) as [table [checked
      [Hindex [Hentry [Hblocks [Hentry_eq Hinputs_eq]]]]]].
    unfold run_with. rewrite Hentry_eq, Hinputs_eq.
    destruct (bind_vars (inputs _ _ _ s) ins []) as [initial|]; [|reflexivity].
    apply copies_loop_run; [exact Hcopies|].
    eapply entered_empty; [exact Hindex|exact Hblocks|exact Hentry|].
    intros x Hin. reflexivity.
  Qed.

  Definition edge_expands (lower : positive)
      (bs : list (positive * block positive O.K O.G)) target actuals target' : Prop :=
    (target' = target /\ actuals = []) \/
    ((lower <= target')%positive /\
      find_block target' bs = Some (Block _ _ _ [] [] (Jump target actuals))).

  Definition exit_expands lower bs (e e' : exit positive O.G) : Prop :=
    e = e' \/ exists guard operands yes yes_args no no_args yes' no',
      e = Branch guard operands yes yes_args no no_args /\
      e' = Branch guard operands yes' [] no' [] /\
      edge_expands lower bs yes yes_args yes' /\
      edge_expands lower bs no no_args no'.

  Definition block_expands lower bs (body body' : block positive O.K O.G) : Prop :=
    params _ _ _ body' = params _ _ _ body /\ code _ _ _ body' = code _ _ _ body /\
    exit_expands lower bs (term _ _ _ body) (term _ _ _ body').

  Lemma split_find_append id (left right : list (positive * block positive O.K O.G)) :
    find_block id (left ++ right) =
      match find_block id left with Some body => Some body | None => find_block id right end.
  Proof.
    induction left as [|[key body] left IH]; [reflexivity|].
    cbn [app find_block]. destruct (Pos.eqb id key); [reflexivity|exact IH].
  Qed.

  Lemma split_find_missing id (bs : list (positive * block positive O.K O.G)) :
    (forall key body, In (key, body) bs -> key <> id) -> find_block id bs = None.
  Proof.
    induction bs as [|[key body] bs IH]; intro Hmissing; [reflexivity|].
    cbn [find_block]. destruct (Pos.eqb id key) eqn:Hequal.
    - apply Pos.eqb_eq in Hequal. subst id. exfalso.
      exact (Hmissing key body (or_introl eq_refl) eq_refl).
    - apply IH. intros key' body' Hin. apply (Hmissing key' body'). now right.
  Qed.

  Lemma edge_expands_transport lower upper bs full target actuals target' :
    (lower <= upper)%positive ->
    (forall id body, (upper <= id)%positive -> find_block id bs = Some body ->
      find_block id full = Some body) ->
    edge_expands upper bs target actuals target' ->
    edge_expands lower full target actuals target'.
  Proof.
    intros Hle Hlookup [Hdirect|[Hbound Hbridge]]; [now left|right].
    split; [eapply Pos.le_trans; eassumption|eapply Hlookup; eassumption].
  Qed.

  Lemma exit_expands_transport lower upper bs full e e' :
    (lower <= upper)%positive ->
    (forall id body, (upper <= id)%positive -> find_block id bs = Some body ->
      find_block id full = Some body) ->
    exit_expands upper bs e e' -> exit_expands lower full e e'.
  Proof.
    intros Hle Hlookup [Hequal|Hbranch]; [now left|right].
    destruct Hbranch as [guard [operands [yes [yes_args [no [no_args [yes' [no'
      [Hsource [Htarget [Hyes Hno]]]]]]]]]]].
    exists guard, operands, yes, yes_args, no, no_args, yes', no'.
    repeat split; try assumption; eapply edge_expands_transport; eassumption.
  Qed.

  Lemma block_expands_transport lower upper bs full body body' :
    (lower <= upper)%positive ->
    (forall id found, (upper <= id)%positive -> find_block id bs = Some found ->
      find_block id full = Some found) ->
    block_expands upper bs body body' -> block_expands lower full body body'.
  Proof.
    intros Hle Hlookup [Hparams [Hcode Hexit]]. split; [exact Hparams|].
    split; [exact Hcode|]. eapply exit_expands_transport; eassumption.
  Qed.

  Lemma split_exit_spec fresh e next e' extras :
    split_exit fresh e = (next, (e', extras)) ->
    (fresh <= next)%positive /\
    (forall id body, In (id, body) extras -> (fresh <= id < next)%positive) /\
    exit_expands fresh extras e e'.
  Proof.
    destruct e as [target actuals|guard operands yes yes_args no no_args|values].
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      split; [apply Pos.le_refl|]. split; [intros id body Hin; contradiction|now left].
    - destruct yes_args as [|y ys], no_args as [|n ns]; cbn [split_exit split_edge];
        intro Hsplit; inversion Hsplit; subst next e' extras.
      + split; [apply Pos.le_refl|].
        split; [intros id body Hin; contradiction|now left].
      + split; [lia|]. split.
        * intros id body [Hequal|Hin]; [|contradiction].
          inversion Hequal; subst id body. split; lia.
        * right. exists guard, operands, yes, [], no, (n :: ns), yes, fresh.
          split; [reflexivity|]. split; [reflexivity|]. split.
          -- left. split; reflexivity.
          -- right. split; [apply Pos.le_refl|]. cbn [find_block].
             now rewrite Pos.eqb_refl.
      + split; [lia|]. split.
        * intros id body [Hequal|Hin]; [|contradiction].
          inversion Hequal; subst id body. split; lia.
        * right. exists guard, operands, yes, (y :: ys), no, [], fresh, no.
          split; [reflexivity|]. split; [reflexivity|]. split.
          -- right. split; [apply Pos.le_refl|]. cbn [find_block].
             now rewrite Pos.eqb_refl.
          -- left. split; reflexivity.
      + split; [lia|]. split.
        * intros id body [Hequal|[Hequal|Hin]]; try contradiction;
            inversion Hequal; subst id body; split; lia.
        * right. exists guard, operands, yes, (y :: ys), no, (n :: ns), fresh, (Pos.succ fresh).
          split; [reflexivity|]. split; [reflexivity|]. split.
          -- right. split; [apply Pos.le_refl|]. cbn [find_block].
             now rewrite Pos.eqb_refl.
          -- right. split; [lia|]. cbn [find_block].
             destruct (Pos.eqb (Pos.succ fresh) fresh) eqn:Hequal.
             ++ apply Pos.eqb_eq in Hequal. lia.
             ++ now rewrite Pos.eqb_refl.
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      split; [apply Pos.le_refl|]. split; [intros id body Hin; contradiction|now left].
  Qed.

  Lemma split_blocks_spec boundary bs : forall fresh last out,
    (boundary <= fresh)%positive ->
    (forall id body, In (id, body) bs -> (id < boundary)%positive) ->
    split_blocks fresh bs = (last, out) ->
    (fresh <= last)%positive /\
    (forall id body, In (id, body) out ->
      (id < boundary)%positive \/ (fresh <= id < last)%positive) /\
    forall id, (id < boundary)%positive ->
      match find_block id bs with
      | None => find_block id out = None
      | Some body => exists body', find_block id out = Some body' /\
          block_expands fresh out body body'
      end.
  Proof.
    induction bs as [|[key body] rest IH]; intros fresh last out Hlower Hids Hsplit.
    - cbn [split_blocks] in Hsplit. inversion Hsplit; subst last out.
      split; [apply Pos.le_refl|]. split; [intros id found Hin; contradiction|].
      intros id Hsmall. reflexivity.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extras]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      destruct (split_exit_spec fresh (term _ _ _ body) next ending extras Hexit)
        as [Hnext [Hextra_ids Hexit_expands]].
      assert (Hkey : (key < boundary)%positive).
      { apply (Hids key body). now left. }
      assert (Hrest_ids : forall id found, In (id, found) rest -> (id < boundary)%positive).
      { intros id found Hin. apply (Hids id found). now right. }
      destruct (IH next final tail ltac:(lia) Hrest_ids Htail)
        as [Hfinal [Htail_ids Hlookup]].
      split; [lia|]. split.
      + intros id found [Hequal|Hin].
        * inversion Hequal; subst id found. now left.
        * apply in_app_or in Hin as [Hin|Hin].
          -- right. specialize (Hextra_ids id found Hin). lia.
          -- specialize (Htail_ids id found Hin). destruct Htail_ids; [now left|right; lia].
      + assert (Hextra_lookup : forall id found,
          (fresh <= id)%positive -> find_block id extras = Some found ->
          find_block id ((key, Block _ _ _ (params _ _ _ body) (code _ _ _ body) ending)
            :: extras ++ tail) = Some found).
        { intros id found Hlarge Hfound. cbn [find_block].
          destruct (Pos.eqb id key) eqn:Hequal.
          - apply Pos.eqb_eq in Hequal. lia.
          - rewrite split_find_append, Hfound. reflexivity. }
        assert (Htail_lookup : forall id found,
          (next <= id)%positive -> find_block id tail = Some found ->
          find_block id ((key, Block _ _ _ (params _ _ _ body) (code _ _ _ body) ending)
            :: extras ++ tail) = Some found).
        { intros id found Hlarge Hfound. cbn [find_block].
          destruct (Pos.eqb id key) eqn:Hequal.
          - apply Pos.eqb_eq in Hequal. lia.
          - rewrite split_find_append.
            assert (Hmissing : find_block id extras = None).
            { apply split_find_missing. intros x xbody Hin.
              specialize (Hextra_ids x xbody Hin). lia. }
            rewrite Hmissing. exact Hfound. }
        intros id Hsmall. cbn [find_block]. destruct (Pos.eqb id key) eqn:Hequal.
        * exists (Block _ _ _ (params _ _ _ body) (code _ _ _ body) ending).
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          eapply exit_expands_transport;
            [apply Pos.le_refl|exact Hextra_lookup|exact Hexit_expands].
        * assert (Hmissing : find_block id extras = None).
          { apply split_find_missing. intros x xbody Hin.
            specialize (Hextra_ids x xbody Hin). lia. }
          rewrite split_find_append, Hmissing. specialize (Hlookup id Hsmall).
          destruct (find_block id rest) as [found|]; [|exact Hlookup].
          destruct Hlookup as [found' [Hfound Hexpands]].
          exists found'. split; [exact Hfound|].
          eapply block_expands_transport; [exact Hnext|exact Htail_lookup|exact Hexpands].
  Qed.

  Lemma split_loop_forward {A B} (source target : A -> A + B) (good : A -> Prop)
      (Hpreserve : forall st next, good st -> source st = inl next -> good next)
      (Hexpand : forall st, good st -> source st = target st \/
        exists middle, target st = inl middle /\ target middle = source st) :
    forall n st r, good st -> loop_fuel source n st = inr r ->
      loop_fuel target (2 * n) st = inr r.
  Proof.
    induction n as [|n IH]; intros st r Hgood Hrun; [discriminate|].
    pose proof (Hexpand st Hgood) as Hsteps.
    cbn [loop_fuel] in Hrun.
    replace (2 * S n) with (S (S (2 * n))) by lia.
    destruct (source st) as [next|out] eqn:Hsource.
    - pose proof (IH next r (Hpreserve st next Hgood Hsource) Hrun) as Htail.
      destruct Hsteps as [Hsame|[middle [Hfirst Hsecond]]].
      + cbn [loop_fuel]. rewrite <- Hsame.
        change (loop_fuel target (S (2 * n)) next = inr r).
        exact (loop_fuel_result_mono target (2 * n) (S (2 * n)) next r ltac:(lia) Htail).
      + cbn [loop_fuel]. rewrite Hfirst. cbn [loop_fuel]. rewrite Hsecond. exact Htail.
    - destruct Hsteps as [Hsame|[middle [Hfirst Hsecond]]].
      + cbn [loop_fuel]. rewrite <- Hsame. exact Hrun.
      + cbn [loop_fuel]. rewrite Hfirst. cbn [loop_fuel]. rewrite Hsecond. exact Hrun.
  Qed.

  Lemma split_loop_backward {A B} (source target : A -> A + B) (good : A -> Prop)
      (Hpreserve : forall st next, good st -> source st = inl next -> good next)
      (Hexpand : forall st, good st -> source st = target st \/
        exists middle, target st = inl middle /\ target middle = source st) :
    forall n st r, good st -> loop_fuel target n st = inr r ->
      loop_fuel source n st = inr r.
  Proof.
    induction n as [|n IH]; intros st r Hgood Hrun; [discriminate|].
    destruct (Hexpand st Hgood) as [Hsame|[middle [Hfirst Hsecond]]].
    - cbn [loop_fuel] in Hrun |- *. rewrite <- Hsame in Hrun.
      destruct (source st) as [next|out] eqn:Hsource; [|exact Hrun].
      apply IH; [eapply Hpreserve; eassumption|exact Hrun].
    - cbn [loop_fuel] in Hrun. rewrite Hfirst in Hrun.
      destruct n as [|n]; [discriminate|].
      cbn [loop_fuel] in Hrun. rewrite Hsecond in Hrun.
      cbn [loop_fuel]. destruct (source st) as [next|out] eqn:Hsource; [|exact Hrun].
      apply IH; [eapply Hpreserve; eassumption|].
      exact (loop_fuel_result_mono target n (S n) next r ltac:(lia) Hrun).
  Qed.

  Lemma split_step_body p id actuals before body :
    find_block id (blocks _ _ _ p) = Some body ->
    step O.eval O.test p (id, actuals, before) =
      match bind_vars (params _ _ _ body) actuals before with
      | None => inr Wrong
      | Some entered => execute_body body entered
      end.
  Proof.
    intro Hfind. unfold step. rewrite Hfind. reflexivity.
  Qed.

  Lemma split_step_bridge p bridge target actuals finished :
    find_block bridge (blocks _ _ _ p) = Some (Block _ _ _ [] [] (Jump target actuals)) ->
    step O.eval O.test p (bridge, [], finished) = finish_exit (Jump target actuals) finished.
  Proof.
    intro Hfind. rewrite (split_step_body _ _ _ _ _ Hfind). reflexivity.
  Qed.

  Lemma split_exit_steps lower p ending ending' finished :
    exit_expands lower (blocks _ _ _ p) ending ending' ->
    finish_exit ending finished = finish_exit ending' finished \/
    exists middle, finish_exit ending' finished = inl middle /\
      step O.eval O.test p middle = finish_exit ending finished.
  Proof.
    intros [Hequal|Hbranch]; [subst ending'; now left|].
    destruct Hbranch as [guard [operands [yes [yes_args [no [no_args [yes' [no'
      [Hsource [Htarget [Hyes Hno]]]]]]]]]]].
    subst ending ending'. cbn [finish_exit].
    destruct (read_vars finished operands) as [values|]; [|now left].
    destruct (O.test guard values) as [choice|]; [|now left].
    destruct choice.
    - destruct Hyes as [[Hequal Hempty]|[Hlower Hbridge]].
      + subst yes' yes_args. now left.
      + right. exists (yes', [], finished). split; [reflexivity|].
        exact (split_step_bridge _ _ _ _ _ Hbridge).
    - destruct Hno as [[Hequal Hempty]|[Hlower Hbridge]].
      + subst no' no_args. now left.
      + right. exists (no', [], finished). split; [reflexivity|].
        exact (split_step_bridge _ _ _ _ _ Hbridge).
  Qed.

  Lemma split_block_steps lower source target id actuals before body body' :
    find_block id (blocks _ _ _ source) = Some body ->
    find_block id (blocks _ _ _ target) = Some body' ->
    block_expands lower (blocks _ _ _ target) body body' ->
    step O.eval O.test source (id, actuals, before) =
      step O.eval O.test target (id, actuals, before) \/
    exists middle, step O.eval O.test target (id, actuals, before) = inl middle /\
      step O.eval O.test target middle = step O.eval O.test source (id, actuals, before).
  Proof.
    intros Hsource Htarget [Hparams [Hcode Hexit]].
    rewrite (split_step_body _ _ _ _ _ Hsource), (split_step_body _ _ _ _ _ Htarget), Hparams.
    destruct (bind_vars (params _ _ _ body) actuals before) as [entered|]; [|now left].
    unfold execute_body. rewrite Hcode.
    destruct (exec_code O.eval (code _ _ _ body) entered) as [finished|]; [|now left].
    exact (split_exit_steps lower target _ _ finished Hexit).
  Qed.

  Lemma split_block_id_in (s : P.t) id body :
    In (id, body) (blocks _ _ _ s) -> In id (function_ids s).
  Proof.
    intro Hin. unfold function_ids. right. apply in_or_app. right.
    apply in_flat_map. exists (id, body). split; [exact Hin|]. cbn. now left.
  Qed.

  Lemma split_target_id_in (s : P.t) id body target :
    In (id, body) (blocks _ _ _ s) -> In target (exit_targets (term _ _ _ body)) ->
    In target (function_ids s).
  Proof.
    intros Hin Htarget. unfold function_ids. right. apply in_or_app. right.
    apply in_flat_map. exists (id, body). split; [exact Hin|]. cbn. now right.
  Qed.

  Lemma split_step_target_bound s st next :
    step O.eval O.test s st = inl next ->
    (fst (fst next) < fresh_after (function_ids s))%positive.
  Proof.
    destruct st as [[id actuals] before].
    unfold step. cbn [fst snd].
    destruct (find_block id (blocks _ _ _ s)) as [body|] eqn:Hfind; [|discriminate].
    pose proof (find_source_block _ id body Hfind) as Hin.
    destruct (bind_vars (params _ _ _ body) actuals before) as [entered|]; [|discriminate].
    destruct (exec_code O.eval (code _ _ _ body) entered) as [finished|]; [|discriminate].
    destruct (term _ _ _ body) as [target args|guard operands yes yes_args no no_args|values]
      eqn:Hterm.
    - destruct (read_vars finished args) as [passed|]; [|discriminate].
      intro Hstep. inversion Hstep; subst next. cbn [fst].
      apply fresh_after_gt. apply (split_target_id_in s id body target Hin).
      rewrite Hterm. cbn [exit_targets]. now left.
    - destruct (read_vars finished operands) as [guard_values|]; [|discriminate].
      destruct (O.test guard guard_values) as [choice|]; [|discriminate].
      destruct choice.
      + destruct (read_vars finished yes_args) as [passed|]; [|discriminate].
        intro Hstep. inversion Hstep; subst next. cbn [fst].
        apply fresh_after_gt. apply (split_target_id_in s id body yes Hin).
        rewrite Hterm. cbn [exit_targets]. now left.
      + destruct (read_vars finished no_args) as [passed|]; [|discriminate].
        intro Hstep. inversion Hstep; subst next. cbn [fst].
        apply fresh_after_gt. apply (split_target_id_in s id body no Hin).
        rewrite Hterm. cbn [exit_targets]. right. now left.
    - destruct (read_vars finished values); discriminate.
  Qed.

  Lemma split_semantic_steps s p : split s = Some p ->
    forall st, (fst (fst st) < fresh_after (function_ids s))%positive ->
      step O.eval O.test s st = step O.eval O.test p st \/
      exists middle, step O.eval O.test p st = inl middle /\
        step O.eval O.test p middle = step O.eval O.test s st.
  Proof.
    intro Hsplit. unfold split in Hsplit.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. inversion Hsplit; subst p.
    assert (Hids : forall id body, In (id, body) (blocks _ _ _ s) ->
      (id < fresh_after (function_ids s))%positive).
    { intros id body Hin. apply fresh_after_gt. exact (split_block_id_in s id body Hin). }
    destruct (split_blocks_spec (fresh_after (function_ids s)) (blocks _ _ _ s)
      (fresh_after (function_ids s)) last out (Pos.le_refl _) Hids Hblocks)
      as [Hlast [Hout Hlookup]].
    intros [[id actuals] before] Hsmall. cbn [fst] in Hsmall.
    specialize (Hlookup id Hsmall).
    destruct (find_block id (blocks _ _ _ s)) as [body|] eqn:Hfind.
    - destruct Hlookup as [body' [Hfind' Hexpands]].
      eapply split_block_steps; [exact Hfind|exact Hfind'|exact Hexpands].
    - left. unfold step. cbn [blocks]. rewrite Hfind, Hlookup. reflexivity.
  Qed.

  Lemma split_shape s p : split s = Some p ->
    inputs _ _ _ p = inputs _ _ _ s /\ entry _ _ _ p = entry _ _ _ s.
  Proof.
    unfold split. destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s)).
    intro Hsplit. inversion Hsplit. split; reflexivity.
  Qed.

  Lemma split_run : forall s split_s, split s = Some split_s -> forall n ins r, r <> Timeout ->
    (run_with O.eval O.test n s ins = r ->
      run_with O.eval O.test (2 * n) split_s ins = r) /\
    (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  Proof.
    intros s p Hsplit n ins r Hfinite.
    destruct (split_shape s p Hsplit) as [Hinputs Hentry].
    assert (Hpreserve : forall st next,
      (fst (fst st) < fresh_after (function_ids s))%positive ->
      step O.eval O.test s st = inl next ->
      (fst (fst next) < fresh_after (function_ids s))%positive).
    { intros st next _ Hstep. exact (split_step_target_bound s st next Hstep). }
    assert (Hgood : (entry _ _ _ s < fresh_after (function_ids s))%positive).
    { apply fresh_after_gt. now left. }
    pose proof (split_semantic_steps s p Hsplit) as Hexpand.
    split.
    - intro Hrun. unfold run_with in Hrun |- *. rewrite Hinputs, Hentry.
      destruct (bind_vars (inputs _ _ _ s) ins []) as [initial|]; [|exact Hrun].
      destruct (loop_fuel (step O.eval O.test s) n (entry _ _ _ s, [], initial))
        as [state|out] eqn:Hloop.
      + exfalso. apply Hfinite. symmetry. exact Hrun.
      + rewrite (split_loop_forward _ _ _ Hpreserve Hexpand n
          (entry _ _ _ s, [], initial) out Hgood Hloop). exact Hrun.
    - intro Hrun. unfold run_with in Hrun |- *. rewrite Hinputs, Hentry in Hrun.
      destruct (bind_vars (inputs _ _ _ s) ins []) as [initial|]; [|exact Hrun].
      destruct (loop_fuel (step O.eval O.test p) n (entry _ _ _ s, [], initial))
        as [state|out] eqn:Hloop.
      + exfalso. apply Hfinite. symmetry. exact Hrun.
      + rewrite (split_loop_backward _ _ _ Hpreserve Hexpand n
          (entry _ _ _ s, [], initial) out Hgood Hloop). exact Hrun.
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
  Proof.
    intros s p Hssa Hdestroy n ins r Hfinite. unfold destroy in Hdestroy.
    destruct (split s) as [split_s|] eqn:Hsplit; [|discriminate].
    destruct (split_run s split_s Hsplit n ins r Hfinite) as [Hforward Hbackward].
    split.
    - intro Hrun. rewrite <- (copies_run split_s p Hdestroy (2 * n) ins).
      apply Hforward. exact Hrun.
    - intro Hrun. apply Hbackward. rewrite (copies_run split_s p Hdestroy n ins).
      exact Hrun.
  Qed.
  (** * Syntax inventories and checked-move budgets *)

  Definition body_variables (body : block positive O.K O.G) :=
    params _ _ _ body ++ flat_map (fun '(x, _, ys) => x :: ys) (code _ _ _ body) ++
      exit_uses (term _ _ _ body).
  Definition block_variables (bs : list (positive * block positive O.K O.G)) :=
    flat_map (fun item => body_variables (snd item)) bs.
  Definition block_sum (weight : block positive O.K O.G -> nat)
      (bs : list (positive * block positive O.K O.G)) :=
    fold_right (fun item n => weight (snd item) + n) 0 bs.
  Definition exit_arg_count (e : exit positive O.G) :=
    match e with
    | Jump _ xs => length xs
    | Branch _ _ _ xs _ ys => length xs + length ys
    | Return _ => 0
    end.
  Definition exit_split_count (e : exit positive O.G) :=
    match e with
    | Branch _ _ _ xs _ ys =>
      (match xs with [] => 0 | _ :: _ => 1 end) +
      (match ys with [] => 0 | _ :: _ => 1 end)
    | _ => 0
    end.

  (** Variable inventories distribute over concatenated block lists. *)
  Lemma block_variables_append left right :
    block_variables (left ++ right) = block_variables left ++ block_variables right.
  Proof.
    apply flat_map_app.
  Qed.

  (** Additive block weights distribute over concatenation. *)
  Lemma block_sum_append weight left right :
    block_sum weight (left ++ right) = block_sum weight left + block_sum weight right.
  Proof.
    induction left as [|item left IH]; cbn [block_sum fold_right app]; [reflexivity|].
    unfold block_sum in IH. rewrite IH. unfold block_sum. lia.
  Qed.

  (** The public edge-argument budget is the sum of block argument weights. *)
  Lemma destroy_args_sum (s : P.t) : destroy_edge_args s =
    block_sum (fun b => exit_arg_count (term _ _ _ b)) (blocks _ _ _ s).
  Proof.
    unfold destroy_edge_args, block_sum.
    induction (blocks _ _ _ s) as [|[id body] rest IH]; [reflexivity|].
    cbn [fold_right snd]. destruct (term _ _ _ body); cbn [exit_arg_count];
      rewrite IH; reflexivity.
  Qed.

  (** The public split count is the sum of branch-edge weights. *)
  Lemma destroy_splits_sum (s : P.t) : split_count s =
    block_sum (fun b => exit_split_count (term _ _ _ b)) (blocks _ _ _ s).
  Proof.
    unfold split_count, block_sum.
    induction (blocks _ _ _ s) as [|[id body] rest IH]; [reflexivity|].
    cbn [fold_right snd]. destruct (term _ _ _ body); cbn [exit_split_count];
      rewrite IH; reflexivity.
  Qed.

  (** Splitting an exit preserves its variables and arguments and adds empty-code bridges. *)
  Lemma split_exit_inventory fresh e next ending extra :
    split_exit fresh e = (next, (ending, extra)) ->
    exit_uses ending ++ block_variables extra = exit_uses e /\
    length extra = exit_split_count e /\
    block_sum (fun b => length (code _ _ _ b)) extra = 0 /\
    exit_arg_count ending + block_sum (fun b => exit_arg_count (term _ _ _ b)) extra =
      exit_arg_count e.
  Proof.
    destruct e as [target actuals|guard operands yes yes_args no no_args|values].
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      cbn [block_variables flat_map block_sum fold_right exit_split_count exit_arg_count].
      rewrite app_nil_r. repeat split; try reflexivity; lia.
    - destruct yes_args as [|y ys], no_args as [|n ns]; cbn [split_exit split_edge];
        intro Hsplit; inversion Hsplit; subst;
        cbn [exit_uses block_variables body_variables flat_map snd params code term
          app exit_split_count exit_arg_count block_sum fold_right length];
        repeat rewrite app_nil_r; repeat rewrite app_assoc; repeat split; try reflexivity; lia.
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      cbn [block_variables flat_map block_sum fold_right exit_split_count exit_arg_count].
      rewrite app_nil_r. repeat split; try reflexivity; lia.
  Qed.

  (** Splitting preserves variables, instructions and arguments and counts all added bridges. *)
  Lemma split_blocks_inventory bs : forall fresh last out,
    split_blocks fresh bs = (last, out) ->
    block_variables out = block_variables bs /\
    length out = length bs + block_sum (fun b => exit_split_count (term _ _ _ b)) bs /\
    block_sum (fun b => length (code _ _ _ b)) out =
      block_sum (fun b => length (code _ _ _ b)) bs /\
    block_sum (fun b => exit_arg_count (term _ _ _ b)) out =
      block_sum (fun b => exit_arg_count (term _ _ _ b)) bs.
  Proof.
    induction bs as [|[id body] rest IH]; intros fresh last out Hsplit.
    - inversion Hsplit; subst. repeat split; try reflexivity; lia.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst out last.
      destruct (IH next final tail Htail) as [Hvars [Hlength [Hcode Hargs]]].
      destruct (split_exit_inventory _ _ _ _ _ Hexit)
        as [Hexit_vars [Hextra_length [Hextra_code Hexit_args]]].
      split.
      + change (body_variables (Block _ _ _ (params _ _ _ body) (code _ _ _ body) ending) ++
          block_variables (extra ++ tail) = body_variables body ++ block_variables rest).
        rewrite block_variables_append, Hvars.
        pose proof (f_equal (fun row => params _ _ _ body ++
          flat_map (fun '(x, _, ys) => x :: ys) (code _ _ _ body) ++
          row ++ block_variables rest) Hexit_vars) as Hagree.
        unfold body_variables. cbn [params code term].
        cbn beta in Hagree. repeat rewrite app_assoc in Hagree.
        repeat rewrite app_assoc. exact Hagree.
      + split.
        * cbn [length block_sum fold_right snd]. rewrite length_app, Hextra_length, Hlength.
          unfold block_sum in *. lia.
        * split.
          -- change (length (code _ _ _ body) +
              block_sum (fun b => length (code _ _ _ b)) (extra ++ tail) =
              length (code _ _ _ body) + block_sum (fun b => length (code _ _ _ b)) rest).
             rewrite block_sum_append, Hextra_code, Hcode. reflexivity.
          -- change (exit_arg_count ending +
              block_sum (fun b => exit_arg_count (term _ _ _ b)) (extra ++ tail) =
              exit_arg_count (term _ _ _ body) +
              block_sum (fun b => exit_arg_count (term _ _ _ b)) rest).
             rewrite block_sum_append, Hargs. lia.
  Qed.

  (** Splitting changes syntax size only by the number of added bridge blocks. *)
  Lemma split_inventory : forall s p, split s = Some p ->
    function_vars p = function_vars s /\
    function_size p = function_size s + split_count s /\
    destroy_edge_args p = destroy_edge_args s /\
    length (blocks _ _ _ p) = length (blocks _ _ _ s) + split_count s.
  Proof.
    intros s p Hsplit. unfold split in Hsplit.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. inversion Hsplit; subst p.
    destruct (split_blocks_inventory _ _ _ _ Hblocks) as [Hvars [Hlength [Hcode Hargs]]].
    assert (Hvars' : function_vars (Func _ _ _ (entry _ _ _ s) (inputs _ _ _ s) out) =
        function_vars s).
    { change (inputs _ _ _ s ++ block_variables out =
        inputs _ _ _ s ++ block_variables (blocks _ _ _ s)). now rewrite Hvars. }
    assert (Hlength' : length out = length (blocks _ _ _ s) + split_count s).
    { rewrite destroy_splits_sum. exact Hlength. }
    split; [exact Hvars'|]. split.
    - unfold function_size. rewrite Hvars'. cbn [blocks].
      change (length (function_vars s) + length out +
        block_sum (fun b => length (code _ _ _ b)) out =
        length (function_vars s) + length (blocks _ _ _ s) +
        block_sum (fun b => length (code _ _ _ b)) (blocks _ _ _ s) + split_count s).
      rewrite Hlength', Hcode. lia.
    - split; [|exact Hlength'].
      rewrite !destroy_args_sum. exact Hargs.
  Qed.

  Definition checks_size (checked : list move_check) :=
    fold_right (fun mc n => length (fst (fst mc)) + 1 + n) 0 checked.

  (** A checked block contributes at most its edge arguments and one check record. *)
  Lemma copy_block_check_size : forall table tmp body out one,
    copy_block table tmp body = Some (out, one) ->
    (match one with None => 0 | Some mc => length (fst (fst mc)) + 1 end) <=
      exit_arg_count (term _ _ _ body) + 1.
  Proof.
    intros table tmp [formals instructions ending] out one Hcopy.
    destruct ending as [target actuals|guard operands yes yes_args no no_args|values];
      cbn [copy_block term code] in Hcopy.
    - destruct (trie_get target table) as [target_formals|]; [|discriminate].
      destruct (pair_moves target_formals actuals) as [[|first par]|] eqn:Hpair;
        try discriminate.
      + inversion Hcopy; subst. cbn [term exit_arg_count]. lia.
      + rewrite copy_check_andb in Hcopy.
        destruct (andb (moves_ok (first :: par) tmp)
          (PM.check_moves (first :: par) tmp (PM.seq (first :: par) tmp))); [|discriminate].
        inversion Hcopy; subst. cbn [fst term exit_arg_count].
        destruct (pair_moves_rows _ _ _ Hpair) as [Hleft Hright].
        pose proof (f_equal (@length positive) Hright) as Hlength.
        rewrite length_map in Hlength. lia.
    - destruct yes_args as [|x xs]; [|discriminate].
      destruct no_args as [|x xs]; [|discriminate].
      destruct (andb (empty_params table yes) (empty_params table no)); [|discriminate].
      inversion Hcopy; subst. cbn [term exit_arg_count]. lia.
    - inversion Hcopy; subst. cbn [term exit_arg_count]. lia.
  Qed.

  (** The total size of checked problems is bounded by edge arguments and source blocks. *)
  Lemma copy_blocks_check_size : forall table tmp bs out checked,
    copy_blocks table tmp bs = Some (out, checked) ->
    checks_size checked <= block_sum (fun b => exit_arg_count (term _ _ _ b)) bs + length bs.
  Proof.
    intros table tmp bs. induction bs as [|[id body] rest IH]; intros out checked Hcopy.
    - inversion Hcopy; subst. reflexivity.
    - cbn [copy_blocks] in Hcopy.
      destruct (copy_block table tmp body) as [[body' one]|] eqn:Hbody; [|discriminate].
      destruct (copy_blocks table tmp rest) as [[tail checks]|] eqn:Htail; [|discriminate].
      inversion Hcopy; subst. specialize (IH tail checks eq_refl).
      pose proof (copy_block_check_size _ _ _ _ _ Hbody) as Hhead.
      destruct one as [mc|].
      + change (length (fst (fst mc)) + 1 + checks_size checks <=
          exit_arg_count (term _ _ _ body) +
          block_sum (fun b => exit_arg_count (term _ _ _ b)) rest + S (length rest)).
        change (length (fst (fst mc)) + 1 <= exit_arg_count (term _ _ _ body) + 1) in Hhead.
        replace (exit_arg_count (term _ _ _ body) +
          block_sum (fun b => exit_arg_count (term _ _ _ b)) rest + S (length rest))
          with ((exit_arg_count (term _ _ _ body) + 1) +
            (block_sum (fun b => exit_arg_count (term _ _ _ b)) rest + length rest)) by lia.
        exact (Nat.add_le_mono _ _ _ _ Hhead IH).
      + change (checks_size checks <= exit_arg_count (term _ _ _ body) +
          block_sum (fun b => exit_arg_count (term _ _ _ b)) rest + S (length rest)).
        lia.
  Qed.

  (** Returned checks fit the input edge-argument and block budget, including failure cases. *)
  Lemma checked_moves_size : forall s,
    checks_size (checked_moves s) <= destroy_edge_args s + length (blocks _ _ _ s).
  Proof.
    intro s. unfold checked_moves, copy_stage.
    destruct (params_index (blocks _ _ _ s)) as [table|]; [|cbn [checks_size fold_right]; lia].
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|];
      try (cbn [checks_size fold_right]; lia).
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|] eqn:Hblocks; [|cbn [checks_size fold_right]; lia].
    rewrite destroy_args_sum. exact (copy_blocks_check_size _ _ _ _ _ Hblocks).
  Qed.
  (** Every checked sequence records the producer call for the indexed target parameter row. *)
  Lemma copy_block_origin : forall table tmp body out par used sq,
    copy_block table tmp body = Some (out, Some (par, used, sq)) ->
    used = tmp /\ sq = PM.seq par tmp /\
    exists target actuals formals, term _ _ _ body = Jump target actuals /\
      trie_get target table = Some formals /\ pair_moves formals actuals = Some par.
  Proof.
    intros table tmp [params instructions ending] out par used sq Hcopy.
    destruct ending as [target actuals|guard operands yes ys no ns|values];
      cbn [copy_block term code] in Hcopy.
    - destruct (trie_get target table) as [formals|] eqn:Hrow; [|discriminate].
      destruct (pair_moves formals actuals) as [[|first rest]|] eqn:Hpair; try discriminate.
      rewrite copy_check_andb in Hcopy.
      destruct (andb (moves_ok (first :: rest) tmp)
        (PM.check_moves (first :: rest) tmp (PM.seq (first :: rest) tmp)));
        [|discriminate].
      inversion Hcopy; subst. split; [reflexivity|]. split; [reflexivity|].
      exists target, actuals, formals. repeat split; assumption.
    - destruct ys; [|discriminate]. destruct ns; [|discriminate].
      destruct (andb (empty_params table yes) (empty_params table no)); discriminate.
    - discriminate.
  Qed.

  (** Each recorded check originates in one listed source block. *)
  Lemma copy_blocks_origin : forall table tmp bs out checked mc,
    copy_blocks table tmp bs = Some (out, checked) -> In mc checked ->
    exists id body body', In (id, body) bs /\ copy_block table tmp body = Some (body', Some mc).
  Proof.
    intros table tmp bs. induction bs as [|[id body] rest IH];
      intros out checked mc Hcopy Hin.
    - inversion Hcopy; subst. contradiction.
    - cbn [copy_blocks] in Hcopy.
      destruct (copy_block table tmp body) as [[body' one]|] eqn:Hbody; [|discriminate].
      destruct (copy_blocks table tmp rest) as [[tail checks]|] eqn:Htail; [|discriminate].
      inversion Hcopy; subst. destruct one as [head|].
      + destruct Hin as [Heq|Hin].
        * subst mc. exists id, body, body'. split; [now left|exact Hbody].
        * destruct (IH tail checks mc eq_refl Hin) as [key [b [b' [Hmember Hrewrite]]]].
          exists key, b, b'. split; [now right|exact Hrewrite].
      + destruct (IH tail checks mc eq_refl Hin) as [key [b [b' [Hmember Hrewrite]]]].
        exists key, b, b'. split; [now right|exact Hrewrite].
  Qed.

  (** Every listed parameter belongs to the function variable inventory. *)
  Lemma listed_params : forall (s : P.t) id body, In (id, body) (blocks _ _ _ s) ->
    incl (params _ _ _ body) (function_vars s).
  Proof.
    intros s id body Hbody x Hx. unfold function_vars.
    apply in_or_app. right. apply in_flat_map. exists (id, body). split; [exact Hbody|].
    cbn [snd]. apply in_or_app. now left.
  Qed.

  (** Recorded moves use source variables and the single temporary allocated by the copy stage. *)
  Lemma checked_moves_origin : forall s par tmp sq, In (par, tmp, sq) (checked_moves s) ->
    tmp = fresh_after (function_vars s) /\ sq = PM.seq par tmp /\
    incl (map fst par ++ map snd par) (function_vars s).
  Proof.
    intros s par tmp sq Hin. unfold checked_moves, copy_stage in Hin.
    destruct (params_index (blocks _ _ _ s)) as [table|] eqn:Hindex; [|contradiction].
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|] eqn:Hentry; try contradiction.
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|] eqn:Hblocks; [|contradiction].
    destruct (copy_blocks_origin _ _ _ _ _ _ Hblocks Hin)
      as [id [body [body' [Hbody Hcopy]]]].
    destruct (copy_block_origin _ _ _ _ _ _ _ Hcopy)
      as [Htmp [Hsq [target [actuals [formals [Hterm [Hrow Hpair]]]]]]].
    split; [exact Htmp|]. split; [now rewrite Htmp|].
    destruct (pair_moves_rows _ _ _ Hpair) as [Hformals Hactuals].
    intros x Hx. apply in_app_or in Hx as [Hx|Hx].
    - rewrite Hformals in Hx.
      rewrite (params_index_find _ _ Hindex) in Hrow.
      destruct (find_block target (blocks _ _ _ s)) as [target_body|] eqn:Hfind;
        [|discriminate].
      injection Hrow as Hrow. subst formals.
      exact (listed_params s target target_body (find_source_block _ _ _ Hfind) x Hx).
    - rewrite Hactuals in Hx.
      apply (listed_exit_uses s id body Hbody x). now rewrite Hterm.
  Qed.

  (** The graph maximum agrees with the standard natural-number maximum. *)
  Lemma destroy_graph_max_nat a b : graph_max a b = Nat.max a b.
  Proof.
    revert b. induction a as [|a IH]; intros [|b]; cbn [graph_max Nat.max]; auto.
  Qed.

  (** Each listed identifier fits the width of its list. *)
  Lemma destroy_vertex_width_in xs x : In x xs -> Pos.size_nat x <= vertex_width xs.
  Proof.
    induction xs as [|head rest IH]; intro Hin; [contradiction|].
    cbn [vertex_width fold_right]. rewrite destroy_graph_max_nat.
    destruct Hin as [Heq|Hin].
    - subst head. apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
  Qed.

  (** Every function identifier fits the published function width. *)
  Lemma function_id_width : forall (s : P.t) x,
    In x (function_ids s) -> Pos.size_nat x <= function_width s.
  Proof.
    intros s x Hin. unfold function_width. rewrite destroy_graph_max_nat.
    eapply Nat.le_trans; [apply destroy_vertex_width_in; exact Hin|apply Nat.le_max_l].
  Qed.

  (** Every function variable fits the published function width. *)
  Lemma function_var_width : forall (s : P.t) x,
    In x (function_vars s) -> Pos.size_nat x <= function_width s.
  Proof.
    intros s x Hin. apply function_id_width. unfold function_ids. right.
    apply in_or_app. now left.
  Qed.

  (** A function has positive width because its entry identifier is positive. *)
  Lemma function_width_positive (s : P.t) : 1 <= function_width s.
  Proof.
    pose proof (function_id_width s (entry _ _ _ s) (or_introl eq_refl)) as Hentry.
    destruct (entry _ _ _ s); cbn [Pos.size_nat] in Hentry; lia.
  Qed.

  (** Taking a positive maximum preserves a common width bound. *)
  Lemma positive_max_width a b w :
    Pos.size_nat a <= w -> Pos.size_nat b <= w -> Pos.size_nat (Pos.max a b) <= w.
  Proof.
    intros Ha Hb. unfold Pos.max. destruct (Pos.compare a b); assumption.
  Qed.

  (** Allocating just above a row maximum adds at most one identifier bit. *)
  Lemma fresh_after_width xs w : 1 <= w ->
    (forall x, In x xs -> Pos.size_nat x <= w) -> Pos.size_nat (fresh_after xs) <= w + 1.
  Proof.
    intros Hpositive Hwidth.
    assert (Hmax : Pos.size_nat (fold_right Pos.max 1%positive xs) <= w).
    { induction xs as [|x rest IH].
      - exact Hpositive.
      - cbn [fold_right]. apply positive_max_width.
        + apply Hwidth. now left.
        + apply IH. intros y Hy. apply Hwidth. now right. }
    pose proof (Z.size_nat_succ (fold_right Pos.max 1%positive xs)) as Hsucc.
    unfold fresh_after. lia.
  Qed.

  (** A common width bound for move operands bounds the parallel problem width. *)
  Lemma par_bits_bound par w :
    (forall x, In x (map fst par ++ map snd par) -> Pos.size_nat x <= w) -> bits_of par <= w.
  Proof.
    induction par as [|[dst src] rest IH]; intro Hwidth; [cbn [bits_of fold_right]; lia|].
    cbn [bits_of fold_right fst snd]. apply Nat.max_lub.
    - apply Hwidth. apply in_or_app. now left; left.
    - apply Nat.max_lub.
      + apply Hwidth. apply in_or_app. now right; left.
      + apply IH. intros x Hx. apply Hwidth.
        apply in_app_or in Hx as [Hx|Hx]; apply in_or_app.
        * left. now right.
        * right. now right.
  Qed.

  (** An exit advances the fresh counter exactly once for each inserted bridge. *)
  Lemma split_exit_counter fresh e next ending extra :
    split_exit fresh e = (next, (ending, extra)) ->
    Pos.to_nat next = Pos.to_nat fresh + exit_split_count e.
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      cbn [exit_split_count]. lia.
    - destruct ys, ns; cbn [split_exit split_edge]; intro Hsplit;
        inversion Hsplit; subst; cbn [exit_split_count];
        rewrite ?Pos2Nat.inj_succ; lia.
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      cbn [exit_split_count]. lia.
  Qed.

  (** At most two bridge blocks are inserted for one exit. *)
  Lemma exit_split_count_bound (e : exit positive O.G) : exit_split_count e <= 2.
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values];
      cbn [exit_split_count]; try lia.
    destruct ys, ns; lia.
  Qed.

  (** The number of inserted bridges is at most twice the number of source blocks. *)
  Lemma block_split_count_bound bs :
    block_sum (fun body => exit_split_count (term _ _ _ body)) bs <= 2 * length bs.
  Proof.
    induction bs as [|[id body] rest IH]; cbn [block_sum fold_right snd length]; [lia|].
    pose proof (exit_split_count_bound (term _ _ _ body)) as Hhead.
    unfold block_sum in IH. lia.
  Qed.

  (** The block pass advances its fresh counter by the exact number of inserted bridges. *)
  Lemma split_blocks_counter bs : forall fresh last out,
    split_blocks fresh bs = (last, out) ->
    Pos.to_nat last = Pos.to_nat fresh +
      block_sum (fun body => exit_split_count (term _ _ _ body)) bs.
  Proof.
    induction bs as [|[id body] rest IH]; intros fresh last out Hsplit.
    - inversion Hsplit; subst. cbn [block_sum fold_right]. lia.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      pose proof (split_exit_counter _ _ _ _ _ Hexit) as Hnext.
      pose proof (IH next final tail Htail) as Hlast.
      cbn [block_sum fold_right snd]. unfold block_sum in Hlast. lia.
  Qed.

  Definition block_labels (bs : list (positive * block positive O.K O.G)) :=
    flat_map (fun item => fst item :: exit_targets (term _ _ _ (snd item))) bs.

  (** The block-label inventory distributes over concatenation. *)
  Lemma block_labels_append left right :
    block_labels (left ++ right) = block_labels left ++ block_labels right.
  Proof.
    apply flat_map_app.
  Qed.

  (** A split exit uses original targets and labels from its allocated interval. *)
  Lemma split_exit_labels fresh e next ending extra :
    split_exit fresh e = (next, (ending, extra)) ->
    forall x, In x (exit_targets ending ++ block_labels extra) ->
      In x (exit_targets e) \/ Pos.to_nat fresh <= Pos.to_nat x < Pos.to_nat next.
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      intros x Hx. left. cbn [block_labels flat_map] in Hx. now rewrite app_nil_r in Hx.
    - destruct ys, ns; cbn [split_exit split_edge]; intro Hsplit;
        inversion Hsplit; subst;
        cbn [exit_targets block_labels flat_map fst snd term app In];
        intros x Hx; repeat rewrite Pos2Nat.inj_succ;
        intuition (subst; auto; lia).
    - cbn [split_exit]. intro Hsplit. inversion Hsplit; subst.
      intros x Hx. left. cbn [block_labels flat_map] in Hx. now rewrite app_nil_r in Hx.
  Qed.

  (** The split program uses original labels and labels from the allocated interval. *)
  Lemma split_blocks_labels bs : forall fresh last out,
    split_blocks fresh bs = (last, out) ->
    forall x, In x (block_labels out) ->
      In x (block_labels bs) \/ Pos.to_nat fresh <= Pos.to_nat x < Pos.to_nat last.
  Proof.
    induction bs as [|[id body] rest IH]; intros fresh last out Hsplit x Hx.
    - inversion Hsplit; subst. contradiction.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      change (In x ((id :: exit_targets ending) ++ block_labels (extra ++ tail))) in Hx.
      rewrite block_labels_append in Hx.
      change (In x ((id :: exit_targets (term _ _ _ body)) ++ block_labels rest) \/
        Pos.to_nat fresh <= Pos.to_nat x < Pos.to_nat final).
      pose proof (split_exit_counter _ _ _ _ _ Hexit) as Hnext.
      pose proof (split_blocks_counter _ _ _ _ Htail) as Hlast.
      apply in_app_or in Hx as [[Heq|Hx]|Hx].
      + left. apply in_or_app. left. now left.
      + destruct (split_exit_labels _ _ _ _ _ Hexit x (in_or_app _ _ _ (or_introl Hx)))
          as [Hold|Hfresh].
        * left. apply in_or_app. left. now right.
        * right. lia.
      + apply in_app_or in Hx as [Hx|Hx].
        * destruct (split_exit_labels _ _ _ _ _ Hexit x (in_or_app _ _ _ (or_intror Hx)))
            as [Hold|Hfresh].
          -- left. apply in_or_app. left. now right.
          -- right. lia.
        * destruct (IH next final tail Htail x Hx) as [Hold|Hfresh].
          -- left. apply in_or_app. now right.
          -- right. lia.
  Qed.
  (** A positive identifier fitting a width is numerically below that power of two. *)
  Lemma positive_width_value x w : Pos.size_nat x <= w -> Pos.to_nat x < 2 ^ w.
  Proof.
    intro Hwidth. pose proof (Pos.size_nat_upper x) as Hvalue.
    pose proof (Nat.pow_le_mono_r 2 (Pos.size_nat x) w ltac:(discriminate) Hwidth) as Hpow.
    lia.
  Qed.

  (** Function syntax size fits below the power of two recorded by its width. *)
  Lemma function_size_value (s : P.t) : function_size s < 2 ^ function_width s.
  Proof.
    assert (Hwidth : Pos.size_nat (Pos.of_succ_nat (function_size s)) <= function_width s).
    { unfold function_width. rewrite destroy_graph_max_nat. apply Nat.le_max_r. }
    pose proof (positive_width_value _ _ Hwidth) as Hvalue.
    rewrite SuccNat2Pos.id_succ in Hvalue. lia.
  Qed.

  (** All possible bridge allocations fit within two extra identifier bits. *)
  Lemma split_counter_budget (s : P.t) :
    Pos.to_nat (fresh_after (function_ids s)) + 2 * length (blocks _ _ _ s) <
      2 ^ (function_width s + 2).
  Proof.
    pose proof (fresh_after_width (function_ids s) (function_width s)
      (function_width_positive s) (function_id_width s)) as Hfresh.
    pose proof (positive_width_value _ _ Hfresh) as Hfresh_value.
    pose proof (function_size_value s) as Hsize.
    assert (Hblocks : length (blocks _ _ _ s) <= function_size s).
    { unfold function_size. lia. }
    rewrite Nat.pow_add_r in Hfresh_value |- *. cbn [Nat.pow] in Hfresh_value |- *. nia.
  Qed.

  (** Every identifier after splitting fits within two extra bits of the source width. *)
  Lemma split_ids_width : forall s split_s, split s = Some split_s ->
    forall x, In x (function_ids split_s) -> Pos.size_nat x <= function_width s + 2.
  Proof.
    intros s split_s Hsplit.
    pose proof (proj1 (split_inventory _ _ Hsplit)) as Hvars.
    unfold split in Hsplit.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. inversion Hsplit; subst split_s.
    intros x Hx. unfold function_ids in Hx. cbn [entry blocks] in Hx.
    rewrite Hvars in Hx. destruct Hx as [Heq|Hx].
    - subst x. pose proof (function_id_width s (entry _ _ _ s) (or_introl eq_refl)). lia.
    - apply in_app_or in Hx as [Hx|Hx].
      + pose proof (function_var_width s x Hx). lia.
      + destruct (split_blocks_labels _ _ _ _ Hblocks x Hx) as [Hold|Hnew].
        * assert (Hwidth : Pos.size_nat x <= function_width s).
          { apply function_id_width. unfold function_ids. right. apply in_or_app. now right. }
          lia.
        * pose proof (split_blocks_counter _ _ _ _ Hblocks) as Hcounter.
          pose proof (block_split_count_bound (blocks _ _ _ s)) as Hcount.
          pose proof (split_counter_budget s) as Hbudget.
          apply Pos.size_nat_least. lia.
  Qed.

  (** * Preservation of SSA under edge splitting *)

  (** Distinct block labels make a membership witness agree with block lookup. *)
  Lemma split_lookup_member (bs : list (positive * block positive O.K O.G)) id body :
    NoDup (map fst bs) ->
    In (id, body) bs -> find_block id bs = Some body.
  Proof.
    induction bs as [|[key found] rest IH]; intros Hunique Hin; [contradiction|].
    inversion Hunique as [|head tail Hfresh Htail]; subst.
    cbn [find_block]. destruct Hin as [Hequal|Hin].
    - inversion Hequal; subst; now rewrite Pos.eqb_refl.
    - destruct (Pos.eqb id key) eqn:Hequal.
      + apply Pos.eqb_eq in Hequal; subst id. exfalso. apply Hfresh.
        apply in_map_iff. exists (key, body). auto.
      + apply IH; assumption.
  Qed.

  (** The bridge blocks allocated for one exit introduce no definitions. *)
  Lemma split_exit_definitions fresh e next ending extra :
    split_exit fresh e = (next, (ending, extra)) ->
    concat (map (fun item => block_defs (snd item)) extra) = [].
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - cbn [split_exit]. intros Hsplit. inversion Hsplit. reflexivity.
    - destruct ys, ns; cbn [split_exit split_edge]; intros Hsplit;
        inversion Hsplit; reflexivity.
    - cbn [split_exit]. intros Hsplit. inversion Hsplit. reflexivity.
  Qed.

  (** Splitting preserves the complete ordered list of block definitions. *)
  Lemma split_blocks_definitions bs : forall fresh last out,
    split_blocks fresh bs = (last, out) ->
    concat (map (fun item => block_defs (snd item)) out) =
    concat (map (fun item => block_defs (snd item)) bs).
  Proof.
    induction bs as [|[id body] rest IH]; intros fresh last out Hsplit.
    - inversion Hsplit. reflexivity.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      pose proof (split_exit_definitions _ _ _ _ _ Hexit) as Hextra.
      specialize (IH _ _ _ Htail).
      change (block_defs body ++ concat (map (fun item => block_defs (snd item))
        (extra ++ tail)) = block_defs body ++
        concat (map (fun item => block_defs (snd item)) rest)).
      now rewrite map_app, concat_app, Hextra, IH.
  Qed.

  (** Every split block label is original or belongs to the allocated interval. *)
  Lemma split_blocks_original_ids bs : forall fresh last out,
    split_blocks fresh bs = (last, out) ->
    (fresh <= last)%positive /\ forall id body, In (id, body) out ->
      In id (map fst bs) \/ (fresh <= id < last)%positive.
  Proof.
    induction bs as [|[key body] rest IH]; intros fresh last out Hsplit.
    - inversion Hsplit; subst. split; [apply Pos.le_refl|].
      intros id found Hin. contradiction.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      destruct (split_exit_spec _ _ _ _ _ Hexit) as [Hnext [Hextra Hexpands]].
      destruct (IH _ _ _ Htail) as [Hfinal Htail_ids].
      split; [lia|]. intros id found [Hequal|Hin].
      + inversion Hequal; subst id found. left. now left.
      + apply in_app_or in Hin as [Hin|Hin].
        * right. specialize (Hextra _ _ Hin). lia.
        * destruct (Htail_ids _ _ Hin) as [Hold|Hnew].
          -- left. now right.
          -- right. lia.
  Qed.

  (** The bridges allocated for one exit have distinct labels. *)
  Lemma split_exit_unique fresh e next ending extra :
    split_exit fresh e = (next, (ending, extra)) -> NoDup (map fst extra).
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - cbn [split_exit]. intros Hsplit. inversion Hsplit. constructor.
    - destruct ys, ns; cbn [split_exit split_edge]; intros Hsplit;
        inversion Hsplit; subst; cbn [map fst]; repeat constructor;
        cbn [In]; intuition lia.
    - cbn [split_exit]. intros Hsplit. inversion Hsplit. constructor.
  Qed.

  (** Fresh allocation preserves the uniqueness of source block labels. *)
  Lemma split_blocks_unique boundary bs : NoDup (map fst bs) ->
    (forall id body, In (id, body) bs -> (id < boundary)%positive) ->
    forall fresh last out, (boundary <= fresh)%positive ->
      split_blocks fresh bs = (last, out) -> NoDup (map fst out).
  Proof.
    induction bs as [|[key body] rest IH]; intros Hunique Hsmall fresh last out Hbound Hsplit.
    - inversion Hsplit; subst. constructor.
    - inversion Hunique as [|head tail Hfresh Hrest]; subst.
      cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      destruct (split_exit_spec _ _ _ _ _ Hexit) as [Hnext [Hextra Hexpands]].
      destruct (split_blocks_original_ids _ _ _ _ Htail) as [Hfinal Htail_ids].
      assert (Hkey : (key < boundary)%positive) by (apply (Hsmall key body); now left).
      assert (Htail_unique : NoDup (map fst tail)).
      { eapply IH with (fresh := next) (last := final); [exact Hrest| |lia|exact Htail].
        intros id found Hin. apply (Hsmall id found). now right. }
      cbn [map fst]. constructor.
      + rewrite map_app. intros Hin. apply in_app_or in Hin as [Hin|Hin];
          apply in_map_iff in Hin as [[id found] [Hequal Hin]]; cbn in Hequal; subst id.
        * specialize (Hextra _ _ Hin). lia.
        * destruct (Htail_ids _ _ Hin) as [Hold|Hnew]; [contradiction|lia].
      + rewrite map_app. apply NoDup_app; [now apply (split_exit_unique _ _ _ _ _ Hexit)|
          exact Htail_unique|].
        intros id Hin1 Hin2.
        apply in_map_iff in Hin1 as [[key1 body1] [Heq1 Hin1]]; cbn in Heq1; subst key1.
        apply in_map_iff in Hin2 as [[key2 body2] [Heq2 Hin2]]; cbn in Heq2; subst key2.
        specialize (Hextra _ _ Hin1).
        destruct (Htail_ids _ _ Hin2) as [Hold|Hnew]; [|lia].
        apply in_map_iff in Hold as [[key2 found] [Hequal Hold]]; cbn in Hequal; subst key2.
        specialize (Hsmall id found (or_intror Hold)). lia.
  Qed.
  (** Each transformed successor is direct or crosses one fresh bridge. *)
  Lemma split_exit_successor lower bs ending ending' next :
    exit_expands lower bs ending ending' ->
    (forall target, successor ending target -> (target < lower)%positive) ->
    successor ending' next ->
    (successor ending next /\ (next < lower)%positive) \/
    exists target args, successor ending target /\ (target < lower)%positive /\
      (lower <= next)%positive /\
      find_block next bs = Some (Block _ _ _ [] [] (Jump target args)).
  Proof.
    intros [Hequal|Hbranch] Hsmall Hnext.
    - subst ending'. left. split; [exact Hnext|now apply Hsmall].
    - destruct Hbranch as [guard [operands [yes [ys [no [ns [yes' [no'
        [Hold [Hnew [Hyes Hno]]]]]]]]]]].
      subst ending ending'. cbn [successor] in Hsmall, Hnext.
      destruct Hnext as [Hequal|Hequal]; subst next.
      + destruct Hyes as [[Hequal Hempty]|[Hlarge Hbridge]].
        * subst yes'. left. split; [now left|apply Hsmall; now left].
        * right. exists yes, ys. repeat split; try assumption.
          -- now left.
          -- apply Hsmall. now left.
      + destruct Hno as [[Hequal Hempty]|[Hlarge Hbridge]].
        * subst no'. left. split; [now right|apply Hsmall; now right].
        * right. exists no, ns. repeat split; try assumption.
          -- now right.
          -- apply Hsmall. now right.
  Qed.

  (** A split path between original labels contracts to a source path within it. *)
  Lemma split_path_contract (source target : P.t) lower :
    NoDup (map fst (blocks _ _ _ target)) ->
    (forall id body, In (id, body) (blocks _ _ _ target) -> (id < lower)%positive ->
      exists original, In (id, original) (blocks _ _ _ source) /\
        exit_expands lower (blocks _ _ _ target)
          (term _ _ _ original) (term _ _ _ body)) ->
    (forall id body next, In (id, body) (blocks _ _ _ source) ->
      successor (term _ _ _ body) next -> (next < lower)%positive) ->
    forall route first last, path target first route last ->
      (first < lower)%positive -> (last < lower)%positive ->
      exists old_route, path source first old_route last /\ incl old_route route.
  Proof.
    intros Hunique Horiginal Htargets.
    assert (Hbounded : forall n route first last, length route <= n ->
      path target first route last -> (first < lower)%positive -> (last < lower)%positive ->
      exists old_route, path source first old_route last /\ incl old_route route).
    { induction n as [|n IH]; intros route first last Hlength Hpath Hfirst Hlast.
      - inversion Hpath; subst; cbn [length] in Hlength; lia.
      - destruct Hpath as [id|id body next rest last Hbody Hedge Hpath].
        + exists [id]. split; [constructor|apply incl_refl].
        + destruct (Horiginal id body Hbody Hfirst) as [original [Hold Hexpands]].
          destruct (split_exit_successor _ _ _ _ _ Hexpands
            (fun next Hnext => Htargets id original next Hold Hnext) Hedge)
            as [[Hedge_old Hnext]|Hbridge].
          * destruct (IH rest next last ltac:(cbn [length] in Hlength; lia)
              Hpath Hnext Hlast) as [old_route [Hroute Hin]].
            exists (id :: old_route). split.
            -- econstructor; eassumption.
            -- intros x [Hequal|Hx]; [now left|right; now apply Hin].
          * destruct Hbridge as [dest [args [Hedge_old [Hdest [Hlarge Hfind]]]]].
            destruct Hpath as [id'|id' bridge next' rest' last' Hbridge Hedge' Hpath'].
            -- lia.
            -- pose proof (split_lookup_member _ _ _ Hunique Hbridge) as Hselected.
               rewrite Hfind in Hselected. inversion Hselected; subst bridge.
               cbn [term successor] in Hedge'. subst next'.
               destruct (IH rest' dest last' ltac:(cbn [length] in Hlength; lia)
                 Hpath' Hdest Hlast) as [old_route [Hroute Hin]].
               exists (id :: old_route). split.
               ++ econstructor; eassumption.
               ++ intros x [Hequal|Hx]; [now left|right; right; now apply Hin]. }
    intros route first last Hpath Hfirst Hlast.
    eapply Hbounded; [apply Nat.le_refl|eassumption|eassumption|eassumption].
  Qed.

  (** Original blocks retain their parameters, instructions and expanded exits. *)
  Lemma split_block_data s p : NoDup (map fst (blocks _ _ _ s)) -> split s = Some p ->
    NoDup (map fst (blocks _ _ _ p)) /\
    concat (map (fun item => block_defs (snd item)) (blocks _ _ _ p)) =
      concat (map (fun item => block_defs (snd item)) (blocks _ _ _ s)) /\
    (forall id body, In (id, body) (blocks _ _ _ s) ->
      exists body', In (id, body') (blocks _ _ _ p) /\
        block_expands (fresh_after (function_ids s)) (blocks _ _ _ p) body body') /\
    (forall id body', In (id, body') (blocks _ _ _ p) ->
      (id < fresh_after (function_ids s))%positive ->
      exists body, In (id, body) (blocks _ _ _ s) /\
        block_expands (fresh_after (function_ids s)) (blocks _ _ _ p) body body').
  Proof.
    intros Hsource_unique Hsplit. unfold split in Hsplit.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. inversion Hsplit; subst p.
    cbn [blocks].
    assert (Hsmall : forall id body, In (id, body) (blocks _ _ _ s) ->
      (id < fresh_after (function_ids s))%positive).
    { intros id body Hin. apply fresh_after_gt. now apply (split_block_id_in s id body). }
    assert (Hunique : NoDup (map fst out)).
    { eapply split_blocks_unique; [exact Hsource_unique|exact Hsmall|
        apply Pos.le_refl|exact Hblocks]. }
    destruct (split_blocks_spec (fresh_after (function_ids s)) (blocks _ _ _ s)
      _ _ _ (Pos.le_refl _) Hsmall Hblocks) as [Hlast [Hids Hlookup]].
    split; [exact Hunique|]. split; [now apply (split_blocks_definitions _ _ _ _ Hblocks)|].
    split.
    - intros id body Hin. specialize (Hlookup id (Hsmall id body Hin)).
      rewrite (split_lookup_member _ _ _ Hsource_unique Hin) in Hlookup.
      destruct Hlookup as [body' [Hfind Hexpand]]. exists body'. split; [|exact Hexpand].
      now apply (find_source_block out id body').
    - intros id body' Hin Hbound. specialize (Hlookup id Hbound).
      pose proof (split_lookup_member _ _ _ Hunique Hin) as Hfind.
      destruct (find_block id (blocks _ _ _ s)) as [body|] eqn:Hsource.
      + destruct Hlookup as [found [Hfound Hexpand]].
        rewrite Hfind in Hfound. inversion Hfound; subst found.
        exists body. split; [|exact Hexpand]. now apply (find_source_block _ _ _ Hsource).
      + rewrite Hfind in Hlookup. discriminate.
  Qed.

  (** Every successor occurs in the exit target list. *)
  Lemma split_successor_listed (ending : exit positive O.G) target :
    successor ending target -> In target (exit_targets ending).
  Proof.
    destruct ending; cbn [successor exit_targets In]; intuition congruence.
  Qed.

  (** Splitting preserves domination of original block labels. *)
  Lemma split_dominates_old s p : NoDup (map fst (blocks _ _ _ s)) ->
    split s = Some p -> forall d b, (b < fresh_after (function_ids s))%positive ->
      dominates s d b -> dominates p d b.
  Proof.
    intros Hunique Hsplit d b Hb Hdom route Hpath.
    destruct (split_block_data s p Hunique Hsplit) as [Hout [_ [_ Hback]]].
    destruct (split_shape s p Hsplit) as [_ Hentry].
    assert (Htargets : forall id body next, In (id, body) (blocks _ _ _ s) ->
      successor (term _ _ _ body) next -> (next < fresh_after (function_ids s))%positive).
    { intros id body next Hin Hnext. apply fresh_after_gt.
      apply (split_target_id_in s id body next Hin). now apply split_successor_listed. }
    assert (Hentered : (entry _ _ _ p < fresh_after (function_ids s))%positive).
    { rewrite Hentry. apply fresh_after_gt. now left. }
    destruct (split_path_contract s p (fresh_after (function_ids s)) Hout
      ltac:(intros id body Hin Hsmall; destruct (Hback id body Hin Hsmall)
        as [original [Hold [_ [_ Hexit]]]]; exists original; now split)
      Htargets route (entry _ _ _ p) b Hpath Hentered Hb) as [old_route [Hold Hincl]].
    rewrite Hentry in Hold. apply Hincl. now apply Hdom.
  Qed.

  (** A visited path label has a prefix path whose labels occur in the whole route. *)
  Lemma split_path_prefix (p : P.t) first route last : path p first route last ->
    forall middle, In middle route ->
      exists prefix, path p first prefix middle /\ incl prefix route.
  Proof.
    intro Hpath. induction Hpath as [id|id body next rest last Hbody Hedge Hpath IH];
      intros middle Hin.
    - destruct Hin as [Hequal|Hin]; [subst middle|contradiction].
      exists [id]. split; [constructor|apply incl_refl].
    - destruct Hin as [Hequal|Hin].
      + subst middle. exists [id]. split; [constructor|].
        intros x [Hequal|Hx]; [now left|contradiction].
      + destruct (IH middle Hin) as [prefix [Hprefix Hincl]].
        exists (id :: prefix). split; [econstructor; eassumption|].
        intros x [Hequal|Hx]; [now left|right; now apply Hincl].
  Qed.

  (** Block domination composes through an intermediate block. *)
  Lemma split_dominates_trans (p : P.t) a b c :
    dominates p a b -> dominates p b c -> dominates p a c.
  Proof.
    intros Hab Hbc route Hpath.
    destruct (split_path_prefix _ _ _ _ Hpath b (Hbc route Hpath))
      as [prefix [Hprefix Hincl]].
    apply Hincl. now apply Hab.
  Qed.

  (** A private bridge is dominated by its unique predecessor. *)
  Lemma split_private_predecessor (p : P.t) owner bridge : entry _ _ _ p <> bridge ->
    (forall id body, In (id, body) (blocks _ _ _ p) ->
      successor (term _ _ _ body) bridge -> id = owner) -> dominates p owner bridge.
  Proof.
    intros Hentry Hpredecessor.
    assert (Htrace : forall first route last, path p first route last -> last = bridge ->
      first = bridge \/ In owner route).
    { intros first route last Hpath. induction Hpath as
        [id|id body next rest last Hbody Hedge Hpath IH]; intro Hlast.
      - now left.
      - destruct (IH Hlast) as [Hequal|Hin].
        + subst next. right. left. now apply (Hpredecessor id body).
        + right. now right. }
    intros route Hpath. destruct (Htrace _ _ _ Hpath eq_refl) as [Hequal|Hin];
      [contradiction|exact Hin].
  Qed.
  (** Each allocated bridge jumps with operands from its original exit. *)
  Lemma split_exit_auxiliary fresh e next ending extra id body :
    split_exit fresh e = (next, (ending, extra)) -> In (id, body) extra ->
    exists target args, body = Block _ _ _ [] [] (Jump target args) /\
      incl args (exit_uses e) /\ successor e target.
  Proof.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - cbn [split_exit]. intros Hsplit. inversion Hsplit; subst. contradiction.
    - destruct ys as [|y ys], ns as [|n ns]; cbn [split_exit split_edge];
        intros Hsplit Hin; inversion Hsplit; subst next ending extra.
      + contradiction.
      + destruct Hin as [Hequal|Hin]; [inversion Hequal; subst id body|contradiction].
        exists no, (n :: ns). split; [reflexivity|]. split; [|now right].
        intros x Hx. cbn [exit_uses]. apply in_or_app. now right.
      + destruct Hin as [Hequal|Hin]; [inversion Hequal; subst id body|contradiction].
        exists yes, (y :: ys). split; [reflexivity|]. split; [|now left].
        intros x Hx. cbn [exit_uses]. apply in_or_app. right. apply in_or_app. now left.
      + destruct Hin as [Hequal|[Hequal|Hin]]; try contradiction;
          inversion Hequal; subst id body.
        * exists yes, (y :: ys). split; [reflexivity|]. split; [|now left].
          intros x Hx. cbn [exit_uses]. apply in_or_app. right. apply in_or_app. now left.
        * exists no, (n :: ns). split; [reflexivity|]. split; [|now right].
          intros x Hx. cbn [exit_uses]. apply in_or_app. right. apply in_or_app. now right.
    - cbn [split_exit]. intros Hsplit. inversion Hsplit; subst. contradiction.
  Qed.

  (** Exit splitting uses original targets and labels in its fresh interval. *)
  Lemma split_exit_target_range fresh e next ending extra x :
    split_exit fresh e = (next, (ending, extra)) ->
    In x (exit_targets ending ++ block_labels extra) ->
    In x (exit_targets e) \/ (fresh <= x < next)%positive.
  Proof.
    intros Hsplit Hin. destruct (split_exit_labels _ _ _ _ _ Hsplit x Hin) as [Hold|Hnew].
    - now left.
    - right. split; [apply Pos2Nat.inj_le|apply Pos2Nat.inj_lt]; lia.
  Qed.

  (** Split-program targets are original or freshly allocated. *)
  Lemma split_blocks_target_range boundary bs :
    (forall x, In x (block_labels bs) -> (x < boundary)%positive) ->
    forall fresh last out x, split_blocks fresh bs = (last, out) ->
      In x (block_labels out) -> (x < boundary)%positive \/ (fresh <= x < last)%positive.
  Proof.
    intros Hsmall fresh last out x Hsplit Hin.
    destruct (split_blocks_labels _ _ _ _ Hsplit x Hin) as [Hold|Hnew].
    - left. now apply Hsmall.
    - right. split; [apply Pos2Nat.inj_le|apply Pos2Nat.inj_lt]; lia.
  Qed.

  (** The block-label inventory contains every listed outgoing target. *)
  Lemma split_block_target_labels bs id body next : In (id, body) bs ->
    successor (term _ _ _ body) next -> In next (block_labels bs).
  Proof.
    intros Hin Hnext. unfold block_labels. apply in_flat_map.
    exists (id, body). split; [exact Hin|]. cbn [fst snd].
    right. now apply split_successor_listed.
  Qed.

  (** Every allocated bridge has one original predecessor identifier. *)
  Lemma split_blocks_bridge_owner boundary bs :
    (forall x, In x (block_labels bs) -> (x < boundary)%positive) ->
    forall fresh last out, (boundary <= fresh)%positive ->
      split_blocks fresh bs = (last, out) ->
      forall id bridge, In (id, bridge) out -> (fresh <= id)%positive ->
      exists owner original target args,
        In (owner, original) bs /\ bridge = Block _ _ _ [] [] (Jump target args) /\
        incl args (exit_uses (term _ _ _ original)) /\
        successor (term _ _ _ original) target /\
        forall predecessor body, In (predecessor, body) out ->
          successor (term _ _ _ body) id -> predecessor = owner.
  Proof.
    induction bs as [|[key original] rest IH]; intros Hsmall fresh last out Hlower Hsplit
      id bridge Hin Hlarge.
    - inversion Hsplit; subst. contradiction.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ original)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      destruct (split_exit_spec _ _ _ _ _ Hexit) as [Hnext [Hextra Hexpands]].
      assert (Hkey : (key < boundary)%positive).
      { apply Hsmall. unfold block_labels. cbn [flat_map fst snd]. now left. }
      assert (Htargets : forall target, successor (term _ _ _ original) target ->
        (target < boundary)%positive).
      { intros target Htarget. apply Hsmall.
        apply (split_block_target_labels ((key, original) :: rest) key original target);
          [now left|exact Htarget]. }
      assert (Hrest : forall x, In x (block_labels rest) -> (x < boundary)%positive).
      { intros x Hx. apply Hsmall. change (In x
          ((key :: exit_targets (term _ _ _ original)) ++ block_labels rest)).
        apply in_or_app. now right. }
      destruct Hin as [Hequal|Hin].
      + inversion Hequal; subst id bridge. lia.
      + apply in_app_or in Hin as [Hin|Hin].
        * destruct (split_exit_auxiliary _ _ _ _ _ _ _ Hexit Hin)
            as [target [args [Hbridge [Huses Htarget]]]].
          pose proof (Hextra id bridge Hin) as Hidrange.
          exists key, original, target, args. split; [now left|].
          split; [exact Hbridge|]. split; [exact Huses|]. split; [exact Htarget|].
          intros predecessor body [Hequal|Hpredecessor] Hedge.
          -- now inversion Hequal.
          -- apply in_app_or in Hpredecessor as [Hpredecessor|Hpredecessor].
             ++ destruct (split_exit_auxiliary _ _ _ _ _ _ _ Hexit Hpredecessor)
                  as [dest [passed [Hbody [_ Hdest]]]].
                subst body. cbn [term successor] in Hedge. subst id.
                specialize (Htargets dest Hdest). lia.
             ++ pose proof (split_block_target_labels _ _ _ _ Hpredecessor Hedge) as Hlabel.
                destruct (split_blocks_target_range boundary rest Hrest _ _ _ _ Htail Hlabel)
                  as [Hold|Hnew]; lia.
        * destruct (split_blocks_original_ids _ _ _ _ Htail) as [Hfinal Htail_ids].
          assert (Hid : (next <= id)%positive).
          { destruct (Htail_ids id bridge Hin) as [Hold|Hnew]; [|lia].
            apply in_map_iff in Hold as [[old found] [Hequal Hold]]; cbn in Hequal; subst old.
            assert (Hid_old : (id < boundary)%positive).
            { apply Hrest. unfold block_labels. apply in_flat_map.
              exists (id, found). split; [exact Hold|]. cbn [fst snd]. now left. }
            lia. }
          destruct (IH Hrest next final tail ltac:(lia) Htail id bridge Hin Hid)
            as [owner [old [target [args [Howner [Hbridge [Huses [Htarget Hparents]]]]]]]].
          exists owner, old, target, args. split; [now right|].
          split; [exact Hbridge|]. split; [exact Huses|]. split; [exact Htarget|].
          intros predecessor body [Hequal|Hpredecessor] Hedge.
          -- inversion Hequal; subst predecessor body.
             cbn [term] in Hedge.
             assert (Hlabel : In id (exit_targets ending ++ block_labels extra)).
             { apply in_or_app. left. now apply split_successor_listed. }
             destruct (split_exit_target_range _ _ _ _ _ _ Hexit Hlabel) as [Hold|Hnew].
             ++ assert (Hid_old : (id < boundary)%positive).
                { apply Hsmall. change (In id
                    ((key :: exit_targets (term _ _ _ original)) ++ block_labels rest)).
                  apply in_or_app. left. now right. }
                lia.
             ++ lia.
          -- apply in_app_or in Hpredecessor as [Hpredecessor|Hpredecessor].
             ++ destruct (split_exit_auxiliary _ _ _ _ _ _ _ Hexit Hpredecessor)
                  as [dest [passed [Hbody [_ Hdest]]]].
                subst body. cbn [term successor] in Hedge. subst id.
                specialize (Htargets dest Hdest). lia.
             ++ now apply (Hparents predecessor body).
  Qed.

  (** A fresh split block retains its original owner, operands and private predecessor. *)
  Lemma split_bridge_owner s p : split s = Some p ->
    forall id bridge, In (id, bridge) (blocks _ _ _ p) ->
      (fresh_after (function_ids s) <= id)%positive ->
      exists owner original target args,
        In (owner, original) (blocks _ _ _ s) /\
        bridge = Block _ _ _ [] [] (Jump target args) /\
        incl args (exit_uses (term _ _ _ original)) /\
        successor (term _ _ _ original) target /\
        forall predecessor body, In (predecessor, body) (blocks _ _ _ p) ->
          successor (term _ _ _ body) id -> predecessor = owner.
  Proof.
    unfold split. destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. intros Hsplit. inversion Hsplit; subst p.
    cbn [blocks]. eapply split_blocks_bridge_owner; [|apply Pos.le_refl|exact Hblocks].
    intros x Hx. apply fresh_after_gt. unfold function_ids.
    right. apply in_or_app. now right.
  Qed.

  (** A transformed original exit uses only operands of its source exit. *)
  Lemma split_exit_uses_subset lower bs ending ending' :
    exit_expands lower bs ending ending' -> incl (exit_uses ending') (exit_uses ending).
  Proof.
    intros [Hequal|Hbranch]; [subst ending'; apply incl_refl|].
    destruct Hbranch as [guard [operands [yes [ys [no [ns [yes' [no'
      [Hold [Hnew Hedges]]]]]]]]]].
    subst ending ending'. intros x Hx. cbn [exit_uses] in *.
    rewrite app_nil_r in Hx. apply in_or_app. now left.
  Qed.

  (** Uses retained in an original block remain source uses at the same instruction index. *)
  Lemma split_block_use lower bs body body' : block_expands lower bs body body' ->
    forall x i, use_at body' x i -> use_at body x i.
  Proof.
    intros [Hparams [Hcode Hexit]] x i Huse.
    destruct Huse as [[op [args [dst [Hnth Hin]]]]|[Hlength Hin]].
    - left. exists op, args, dst. now rewrite Hcode in Hnth.
    - right. rewrite Hcode in Hlength. split; [exact Hlength|].
      now apply (split_exit_uses_subset _ _ _ _ Hexit).
  Qed.

  (** Definitions before a retained use stay before that use after splitting. *)
  Lemma split_block_before lower bs body body' : block_expands lower bs body body' ->
    forall x i, def_before body x i -> def_before body' x i.
  Proof.
    intros [Hparams [Hcode Hexit]] x i Hbefore.
    unfold def_before. rewrite Hparams, Hcode. exact Hbefore.
  Qed.

  (** An original block retains exactly its parameter and instruction definitions. *)
  Lemma split_block_definitions lower bs body body' : block_expands lower bs body body' ->
    block_defs body' = block_defs body.
  Proof.
    intros [Hparams [Hcode Hexit]]. unfold block_defs. now rewrite Hparams, Hcode.
  Qed.

  (** A definition before a use belongs to the block definition list. *)
  Lemma split_before_definition (body : block positive O.K O.G) x i :
    def_before body x i -> In x (block_defs body).
  Proof.
    intros [Hin|[j [op [args [Hlt Hnth]]]]]; unfold block_defs; apply in_or_app.
    - now left.
    - right. apply in_map_iff. exists (x, op, args). split; [reflexivity|].
      now apply nth_error_In in Hnth.
  Qed.

  (** An edge split preserves target arities and gives its bridge empty parameters. *)
  Lemma split_edge_shapes (source target : P.t) fresh dest args next dest' extra :
    (forall b xs, edge_shape source b xs -> edge_shape target b xs) ->
    split_edge fresh dest args = (next, (dest', extra)) ->
    incl extra (blocks _ _ _ target) -> edge_shape source dest args ->
    edge_shape target dest' [] /\ forall id body, In (id, body) extra ->
      exit_shape target (term _ _ _ body).
  Proof.
    intros Htargets Hsplit Hin Hshape. destruct args as [|x xs].
    - cbn [split_edge] in Hsplit. inversion Hsplit; subst.
      split; [now apply Htargets|]. intros id body Hbody. contradiction.
    - cbn [split_edge] in Hsplit. inversion Hsplit; subst.
      split.
      + exists (Block _ _ _ [] [] (Jump dest (x :: xs))). split.
        * apply Hin. now left.
        * reflexivity.
      + intros id body [Hequal|Hbody]; [inversion Hequal; subst|contradiction].
        cbn [term exit_shape]. now apply Htargets.
  Qed.

  (** Exit splitting preserves the arity of every direct and bridge edge. *)
  Lemma split_exit_shapes (source target : P.t) fresh ending next ending' extra :
    (forall b xs, edge_shape source b xs -> edge_shape target b xs) ->
    split_exit fresh ending = (next, (ending', extra)) ->
    incl extra (blocks _ _ _ target) -> exit_shape source ending ->
    exit_shape target ending' /\ forall id body, In (id, body) extra ->
      exit_shape target (term _ _ _ body).
  Proof.
    intros Htargets Hsplit Hin Hshape.
    destruct ending as [dest args|guard operands yes ys no ns|values].
    - cbn [split_exit] in Hsplit. inversion Hsplit; subst.
      split; [now apply Htargets|]. intros id body Hbody. contradiction.
    - cbn [split_exit] in Hsplit.
      destruct (split_edge fresh yes ys) as [middle [yes' yes_blocks]] eqn:Hyes.
      destruct (split_edge middle no ns) as [last [no' no_blocks]] eqn:Hno.
      inversion Hsplit; subst next ending' extra.
      destruct Hshape as [Hshape_yes Hshape_no].
      destruct (split_edge_shapes source target _ _ _ _ _ _ Htargets Hyes
        ltac:(intros row Hrow; apply Hin; apply in_or_app; now left) Hshape_yes)
        as [Hyes_target Hyes_extra].
      destruct (split_edge_shapes source target _ _ _ _ _ _ Htargets Hno
        ltac:(intros row Hrow; apply Hin; apply in_or_app; now right) Hshape_no)
        as [Hno_target Hno_extra].
      split; [now split|]. intros id body Hbody. apply in_app_or in Hbody as [Hbody|Hbody].
      + now apply (Hyes_extra id body).
      + now apply (Hno_extra id body).
    - cbn [split_exit] in Hsplit. inversion Hsplit; subst.
      split; [exact I|]. intros id body Hbody. contradiction.
  Qed.

  (** Splitting preserves every exit shape when original target parameters agree. *)
  Lemma split_blocks_shapes (source target : P.t) bs :
    (forall b xs, edge_shape source b xs -> edge_shape target b xs) ->
    (forall id body, In (id, body) bs -> exit_shape source (term _ _ _ body)) ->
    forall fresh last out, split_blocks fresh bs = (last, out) ->
      incl out (blocks _ _ _ target) ->
      forall id body, In (id, body) out -> exit_shape target (term _ _ _ body).
  Proof.
    intros Htargets. induction bs as [|[key original] rest IH];
      intros Hshapes fresh last out Hsplit Hin id body Hbody.
    - inversion Hsplit; subst. contradiction.
    - cbn [split_blocks] in Hsplit.
      destruct (split_exit fresh (term _ _ _ original)) as [next [ending extra]] eqn:Hexit.
      destruct (split_blocks next rest) as [final tail] eqn:Htail.
      inversion Hsplit; subst last out.
      destruct (split_exit_shapes source target _ _ _ _ _ Htargets Hexit
        ltac:(intros row Hrow; apply Hin; right; apply in_or_app; now left)
        (Hshapes key original (or_introl eq_refl))) as [Hending Hextra].
      destruct Hbody as [Hequal|Hbody].
      + inversion Hequal; subst id body. exact Hending.
      + apply in_app_or in Hbody as [Hbody|Hbody].
        * now apply (Hextra id body).
        * eapply IH; [|exact Htail| |exact Hbody].
          -- intros label found Hfound. apply (Hshapes label found). now right.
          -- intros row Hrow. apply Hin. right. apply in_or_app. now right.
  Qed.

  (** Splitting preserves listed targets and argument arities throughout the program. *)
  Lemma split_shapes s p : NoDup (map fst (blocks _ _ _ s)) ->
    (forall id body, In (id, body) (blocks _ _ _ s) -> exit_shape s (term _ _ _ body)) ->
    split s = Some p ->
    forall id body, In (id, body) (blocks _ _ _ p) -> exit_shape p (term _ _ _ body).
  Proof.
    intros Hunique Hshapes Hsplit.
    destruct (split_block_data s p Hunique Hsplit) as [_ [_ [Hforward _]]].
    assert (Htargets : forall b xs, edge_shape s b xs -> edge_shape p b xs).
    { intros b xs [body [Hin Hlength]].
      destruct (Hforward b body Hin) as [body' [Hin' [Hparams Hrest]]].
      exists body'. split; [exact Hin'|]. now rewrite Hparams. }
    unfold split in Hsplit.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s))
      as [last out] eqn:Hblocks. inversion Hsplit; subst p.
    eapply split_blocks_shapes; [exact Htargets|exact Hshapes|exact Hblocks|apply incl_refl].
  Qed.

  (** Splitting preserves unique definitions, dominating uses, entry membership and exit arities. *)
  Lemma split_ssa_wf s p : ssa_wf s -> split s = Some p -> ssa_wf p.
  Proof.
    intros [Hunique [Hdefinitions [Huses [Hentry Hshapes]]]] Hsplit.
    destruct (split_block_data s p Hunique Hsplit)
      as [Hout [Hdefinitions_eq [Hforward Hback]]].
    destruct (split_shape s p Hsplit) as [Hinputs Hentry_eq].
    split; [exact Hout|]. split.
    - now rewrite Hinputs, Hdefinitions_eq.
    - split.
      + intros id body x i Hin Huse.
        destruct (Nat.lt_ge_cases (Pos.to_nat id)
          (Pos.to_nat (fresh_after (function_ids s)))) as [Hsmall|Hlarge].
        * apply Pos2Nat.inj_lt in Hsmall.
          destruct (Hback id body Hin Hsmall) as [original [Hold Hexpand]].
          destruct (Huses id original x i Hold (split_block_use _ _ _ _ Hexpand x i Huse))
            as [Hinput|[Hbefore|[def_id [def_body [Hdef [Hdifferent [Hdefined Hdom]]]]]]].
          -- left. now rewrite Hinputs.
          -- right. left. now apply (split_block_before _ _ _ _ Hexpand).
          -- right. right. destruct (Hforward def_id def_body Hdef)
               as [new_def [Hnew_def Hdef_expand]].
             exists def_id, new_def. split; [exact Hnew_def|].
             split; [exact Hdifferent|]. split.
             ++ now rewrite (split_block_definitions _ _ _ _ Hdef_expand).
             ++ exact (split_dominates_old s p Hunique Hsplit def_id id Hsmall Hdom).
        * apply Pos2Nat.inj_le in Hlarge.
          destruct (split_bridge_owner s p Hsplit id body Hin Hlarge)
            as [owner [original [target [args [Howner [Hbody [Hargs [Htarget Hparents]]]]]]]].
          subst body.
          assert (Howner_small : (owner < fresh_after (function_ids s))%positive).
          { apply fresh_after_gt. now apply (split_block_id_in s owner original). }
          assert (Howner_dom : dominates p owner id).
          { apply split_private_predecessor; [|exact Hparents].
            rewrite Hentry_eq. pose proof (fresh_after_gt (function_ids s)
              (entry _ _ _ s) (or_introl eq_refl)) as Hentry_small. lia. }
          assert (Hx : In x args).
          { destruct Huse as [[op [passed [dst [Hnth Hoperand]]]]|[Hlength Hoperand]].
            - cbn [code] in Hnth. destruct i; discriminate.
            - exact Hoperand. }
          assert (Horiginal_use : use_at original x (length (code _ _ _ original))).
          { right. split; [reflexivity|now apply Hargs]. }
          destruct (Huses owner original x (length (code _ _ _ original)) Howner Horiginal_use)
            as [Hinput|[Hbefore|[def_id [def_body [Hdef [Hdifferent [Hdefined Hdom]]]]]]].
          -- left. now rewrite Hinputs.
          -- right. right. destruct (Hforward owner original Howner)
               as [new_owner [Hnew_owner Howner_expand]].
             exists owner, new_owner. split; [exact Hnew_owner|].
             split; [lia|]. split; [|exact Howner_dom].
             rewrite (split_block_definitions _ _ _ _ Howner_expand).
             now apply (split_before_definition original x (length (code _ _ _ original))).
          -- right. right. destruct (Hforward def_id def_body Hdef)
               as [new_def [Hnew_def Hdef_expand]].
             exists def_id, new_def. split; [exact Hnew_def|]. split.
             ++ pose proof (fresh_after_gt (function_ids s) def_id
                  (split_block_id_in s def_id def_body Hdef)) as Hdef_small. lia.
             ++ split.
                ** now rewrite (split_block_definitions _ _ _ _ Hdef_expand).
                ** exact (split_dominates_trans p def_id owner id
                     (split_dominates_old s p Hunique Hsplit def_id owner Howner_small Hdom)
                     Howner_dom).
      + split.
        * destruct Hentry as [body Hin]. destruct (Hforward (entry _ _ _ s) body Hin)
            as [body' [Hin' Hexpand]]. exists body'. now rewrite Hentry_eq.
        * now apply (split_shapes s p Hunique Hshapes Hsplit).
  Qed.

  (** Splitting preserves SSA and finite observations with at most one extra step per block. *)
  Lemma split_preserves_complete : forall s split_s, ssa_wf s -> split s = Some split_s ->
    ssa_wf split_s /\ forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) split_s ins = r) /\
      (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  Proof.
    intros s split_s Hwf Hsplit. split.
    - now apply (split_ssa_wf s split_s Hwf Hsplit).
    - now apply (split_run s split_s Hsplit).
  Qed.
End Destroy.

(** Flattening charges list cells, output cells and the callback budget. *)
Lemma destroy_flat_map_clock {A B} (f : A -> list B) Tf k xs :
  (forall x, In x xs -> (Tf x <= k * N.of_nat (length (f x) + 1))%N) ->
  (Code.List.T_flat_map f Tf xs <=
    (k + 4) * N.of_nat (length xs + length (flat_map f xs) + 1))%N.
Proof.
  induction xs as [|x rest IH]; intro Hcallback.
  - time_unfold Code.List.T_flat_map. cbn [length flat_map]. nia.
  - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y Hy => Hcallback y (or_intror Hy))).
    pose proof (Datatypes.T_app_le (f x) (flat_map f rest)) as Happend.
    time_unfold Code.List.T_flat_map. cbn [flat_map length]. rewrite length_app.
    rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
Qed.

(** The variable inventory contains at least the destination of every instruction. *)
Lemma destroy_instruction_count {K} (instructions : list (positive * K * list positive)) :
  length instructions <= length (flat_map (fun '(dst, _, args) => dst :: args) instructions).
Proof.
  induction instructions as [|[[dst op] args] rest IH]; cbn [flat_map length]; [lia|].
  rewrite length_app. cbn [length]. lia.
Qed.

(** Collecting an exit row costs at most a constant times its length. *)
Lemma destroy_exit_uses_clock {G} (e : exit positive G) :
  (T_exit_uses e <= 4 * N.of_nat (length (exit_uses e) + 1))%N.
Proof.
  destruct e as [target actuals|guard operands yes ys no ns|values].
  - unfold T_exit_uses. cbn [exit_uses]. nia.
  - pose proof (Datatypes.T_app_le ys ns) as Hargs.
    pose proof (Datatypes.T_app_le operands (ys ++ ns)) as Hoperands.
    unfold T_exit_uses. cbn [exit_uses]. rewrite !length_app.
    rewrite !Nat2N.inj_add in *. nia.
  - unfold T_exit_uses. cbn [exit_uses]. nia.
Qed.

(** Collecting all function variables costs at most a constant times syntax size. *)
Lemma destroy_function_vars_clock {K G} (s : func positive K G) :
  (T_function_vars s <= 128 * N.of_nat (function_size s + 1))%N.
Proof.
  set (row := fun item : positive * block positive K G =>
    params _ _ _ (snd item) ++
    flat_map (fun '(dst, _, args) => dst :: args) (code _ _ _ (snd item)) ++
    exit_uses (term _ _ _ (snd item))).
  set (callback := fun item : positive * block positive K G =>
    (1 + (Datatypes.T_snd item + T_params _ _ _ (snd item) +
      (Datatypes.T_snd item + T_code _ _ _ (snd item) +
        Code.List.T_flat_map (fun '(dst, _, args) => dst :: args) (fun _ => 1%N)
          (code _ _ _ (snd item)) +
        (Datatypes.T_snd item + T_term _ _ _ (snd item) +
          T_exit_uses (term _ _ _ (snd item))) +
        Datatypes.T_app
          (flat_map (fun '(dst, _, args) => dst :: args) (code _ _ _ (snd item)))
          (exit_uses (term _ _ _ (snd item)))) +
      Datatypes.T_app (params _ _ _ (snd item))
        (flat_map (fun '(dst, _, args) => dst :: args) (code _ _ _ (snd item)) ++
          exit_uses (term _ _ _ (snd item)))))%N).
  assert (Hcallback : forall item, (callback item <= 64 * N.of_nat (length (row item) + 1))%N).
  { intros [id [formals instructions ending]].
    pose proof (destroy_flat_map_clock (fun '(dst, _, args) => dst :: args)
      (fun _ : positive * K * list positive => 1%N) 1%N instructions
      ltac:(intros; rewrite Nat2N.inj_add; nia)) as Hcode.
    pose proof (destroy_instruction_count instructions) as Hcount.
    pose proof (destroy_exit_uses_clock ending) as Hexit.
    pose proof (Datatypes.T_app_le
      (flat_map (fun '(dst, _, args) => dst :: args) instructions) (exit_uses ending)) as Happend.
    pose proof (Datatypes.T_app_le formals
      (flat_map (fun '(dst, _, args) => dst :: args) instructions ++ exit_uses ending)) as Hparams.
    unfold callback, row, Datatypes.T_snd, T_params, T_code, T_term.
    time_cbn. rewrite !length_app.
    apply time_of_nat_le in Hcount. rewrite !Nat2N.inj_add in *. nia. }
  pose proof (destroy_flat_map_clock row callback 64%N (blocks _ _ _ s)
    (fun item _ => Hcallback item)) as Hrows.
  pose proof (Datatypes.T_app_le (inputs _ _ _ s)
    (flat_map row (blocks _ _ _ s))) as Hinputs.
  unfold T_function_vars. fold row callback. unfold T_inputs, T_blocks. time_cbn.
  unfold function_size, function_vars. fold row. rewrite length_app.
  rewrite !Nat2N.inj_add in *. nia.
Qed.

(** Each exit has at most two target identifiers. *)
Lemma destroy_target_count {G} (e : exit positive G) : length (exit_targets e) <= 2.
Proof.
  destruct e; cbn [exit_targets length]; lia.
Qed.

(** Listed block labels and targets occupy at most three cells per source block. *)
Lemma destroy_id_rows_length {K G} (bs : list (positive * block positive K G)) :
  length (flat_map (fun item => fst item :: exit_targets (term _ _ _ (snd item))) bs) <=
    3 * length bs.
Proof.
  induction bs as [|[id body] rest IH]; cbn [flat_map fst snd length]; [lia|].
  rewrite length_app. cbn [length]. pose proof (destroy_target_count (term _ _ _ body)). lia.
Qed.

(** The full identifier inventory is linear in function syntax size. *)
Lemma destroy_function_ids_length {K G} (s : func positive K G) :
  length (function_ids s) <= 3 * (function_size s + 1).
Proof.
  pose proof (destroy_id_rows_length (blocks _ _ _ s)) as Hrows.
  unfold function_ids, function_size. cbn [length]. rewrite length_app. lia.
Qed.

(** Collecting identifiers costs at most a constant times function syntax size. *)
Lemma destroy_function_ids_clock {K G} (s : func positive K G) :
  (T_function_ids s <= 256 * N.of_nat (function_size s + 1))%N.
Proof.
  pose proof (destroy_function_vars_clock s) as Hvars.
  pose proof (destroy_id_rows_length (blocks _ _ _ s)) as Hlength.
  set (row := fun item : positive * block positive K G =>
    fst item :: exit_targets (term _ _ _ (snd item))).
  set (callback := fun item : positive * block positive K G =>
    (1 + (Datatypes.T_fst item +
      (Datatypes.T_snd item + T_term _ _ _ (snd item) +
        T_exit_targets (term _ _ _ (snd item)))))%N).
  assert (Hcallback : forall item, (callback item <= 8 * N.of_nat (length (row item) + 1))%N).
  { intros [id [formals instructions ending]].
    unfold callback, row, Datatypes.T_fst, Datatypes.T_snd, T_term, T_exit_targets.
    destruct ending; time_cbn; nia. }
  pose proof (destroy_flat_map_clock row callback 8%N (blocks _ _ _ s)
    (fun item _ => Hcallback item)) as Hrows.
  pose proof (Datatypes.T_app_le (function_vars s)
    (flat_map row (blocks _ _ _ s))) as Happend.
  unfold T_function_ids. fold row callback. unfold T_entry, T_blocks. time_cbn.
  apply time_of_nat_le in Hlength. fold row in Hlength.
  unfold function_size in *. rewrite !Nat2N.inj_add in *. nia.
Qed.

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
  Definition c_ds : N := 4097 + 16384 * (PTrieT.c_trie + PM.c_pm + 1).
  Definition destroy_work (s : P.t) :=
    function_size s + destroy_edge_args s + split_count s + 1.
  (** The maximum comparison pays only for the width of its first identifier. *)
  Lemma positive_max_clock a b :
    (Pos.T_max a b <= N.of_nat (Pos.size_nat a) + 2)%N.
  Proof.
    pose proof (Pos.T_compare_le a b) as Hcompare.
    time_unfold Pos.T_max. nia.
  Qed.

  (** Finding an identifier maximum is linear in row length and row width. *)
  Lemma positive_fold_max_clock xs w :
    (forall x, In x xs -> Pos.size_nat x <= w) ->
    (List.T_fold_right Pos.max Pos.T_max 1%positive xs <=
      4 * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction xs as [|x rest IH]; intro Hwidth.
    - time_unfold List.T_fold_right. cbn [length]. rewrite Nat2N.inj_add. nia.
    - pose proof (Hwidth x (or_introl eq_refl)) as Hx.
      specialize (IH (fun y Hy => Hwidth y (or_intror Hy))).
      pose proof (positive_max_clock x (fold_right Pos.max 1%positive rest)) as Hmax.
      apply time_of_nat_le in Hx.
      time_unfold List.T_fold_right. cbn [length].
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** Allocating above a row maximum is linear in its length and identifier width. *)
  Lemma fresh_after_clock xs w : 1 <= w ->
    (forall x, In x xs -> Pos.size_nat x <= w) ->
    (T_fresh_after xs <= 8 * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hpositive Hwidth.
    assert (Hmax : Pos.size_nat (fold_right Pos.max 1%positive xs) <= w).
    { induction xs as [|x rest IH].
      - exact Hpositive.
      - cbn [fold_right]. apply positive_max_width.
        + apply Hwidth. now left.
        + apply IH. intros y Hy. apply Hwidth. now right. }
    pose proof (Pos.T_succ_le (fold_right Pos.max 1%positive xs)) as Hsucc.
    pose proof (positive_fold_max_clock xs w Hwidth) as Hfold.
    change (List.T_fold_right Pos.max (fun x acc => Pos.T_max x acc) 1%positive xs <=
      4 * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N in Hfold.
    apply time_of_nat_le in Hmax. time_unfold T_fresh_after.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Splitting an exit performs at most two fresh-counter increments. *)
  Lemma split_exit_clock fresh e :
    (T_split_exit fresh e <= 16 * N.of_nat (Pos.size_nat fresh + 2))%N.
  Proof.
    pose proof (Pos.T_succ_le fresh) as Hfirst.
    pose proof (Pos.T_succ_le (Pos.succ fresh)) as Hsecond.
    pose proof (Z.size_nat_succ fresh) as Hwidth.
    apply time_of_nat_le in Hwidth.
    destruct e as [target actuals|guard operands yes ys no ns|values].
    - time_unfold T_split_exit. rewrite Nat2N.inj_add. nia.
    - destruct ys, ns; unfold T_split_exit, T_split_edge; cbn [split_edge];
        unfold Datatypes.T_app; time_cbn; rewrite !Nat2N.inj_add in *; nia.
    - time_unfold T_split_exit. rewrite Nat2N.inj_add. nia.
  Qed.

  (** The split pass is linear in block count at a width containing every allocated label. *)
  Lemma split_blocks_clock bs w : forall fresh,
    Pos.to_nat fresh + 2 * length bs < 2 ^ w ->
    (T_split_blocks fresh bs <=
      64 * N.of_nat (length bs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction bs as [|[id body] rest IH]; intros fresh Hbudget.
    - time_unfold T_split_blocks. cbn [length]. rewrite Nat2N.inj_add. nia.
    - assert (Hfresh : Pos.size_nat fresh <= w).
      { apply Pos.size_nat_least. lia. }
      pose proof (split_exit_clock fresh (term _ _ _ body)) as Hexit_time.
      destruct (split_exit fresh (term _ _ _ body)) as [next [ending extra]] eqn:Hexit.
      pose proof (split_exit_counter _ _ _ _ _ Hexit) as Hnext.
      pose proof (exit_split_count_bound (term _ _ _ body)) as Hcount.
      assert (Htail_budget : Pos.to_nat next + 2 * length rest < 2 ^ w).
      { cbn [length] in Hbudget. lia. }
      specialize (IH next Htail_budget).
      destruct (split_exit_inventory _ _ _ _ _ Hexit) as [_ [Hextra _]].
      destruct (split_blocks next rest) as [last tail] eqn:Htail.
      pose proof (Datatypes.T_app_le extra tail) as Happend.
      assert (Hextra_small : length extra <= 2) by lia.
      apply time_of_nat_le in Hfresh. apply time_of_nat_le in Hextra_small.
      time_unfold T_split_blocks. rewrite Hexit, Htail.
      unfold T_term, T_params, T_code. cbn [length].
      rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** Splitting satisfies the source syntax and bit-width budget. *)
  Lemma split_source_clock s :
    (T_split s <= 4096 * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1))%N.
  Proof.
    pose proof (destroy_function_ids_clock s) as Hsyntax.
    pose proof (destroy_function_ids_length s) as Hids_length.
    pose proof (fresh_after_clock (function_ids s) (function_width s)
      (function_width_positive s) (function_id_width s)) as Hfresh.
    pose proof (split_blocks_clock (blocks _ _ _ s) (function_width s + 2)
      (fresh_after (function_ids s)) (split_counter_budget s)) as Hblocks.
    assert (Hblock_count : length (blocks _ _ _ s) <= function_size s).
    { unfold function_size. lia. }
    apply time_of_nat_le in Hids_length. apply time_of_nat_le in Hblock_count.
    time_unfold T_split. unfold T_blocks, T_entry, T_inputs.
    destruct (split_blocks (fresh_after (function_ids s)) (blocks _ _ _ s)).
    unfold destroy_work. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** Distinctness checking charges one trie lookup and update for each variable. *)
  Lemma distinct_vars_clock xs w :
    (forall x, In x xs -> Pos.size_nat x <= w) -> forall seen,
    (T_distinct_vars xs seen <=
      8 * (PTrieT.c_trie + 1) * N.of_nat (length xs + 1) * N.of_nat (w + 1))%N.
  Proof.
    induction xs as [|x rest IH]; intros Hwidth seen.
    - time_unfold T_distinct_vars. cbn [length]. rewrite Nat2N.inj_add. nia.
    - pose proof (Hwidth x (or_introl eq_refl)) as Hx.
      pose proof (PTrieT.T_trie_get_le unit x seen) as Hget.
      pose proof (PTrieT.T_set_le unit x tt seen) as Hset.
      specialize (IH (fun y Hy => Hwidth y (or_intror Hy)) (PTrieCode.set x tt seen)).
      apply time_of_nat_le in Hx.
      time_unfold T_distinct_vars.
      destruct (trie_get x seen); cbn [length];
        rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *; nia.
  Qed.

  (** Pairing rows scans no more cells than the supplied actual row. *)
  Lemma pair_moves_clock : forall formals actuals,
    (T_pair_moves formals actuals <= N.of_nat (length actuals + 1))%N.
  Proof.
    induction formals as [|x xs IH]; intros [|y ys]; time_unfold T_pair_moves;
      cbn [length]; rewrite ?Nat2N.inj_add, ?Nat2N.inj_succ;
      try specialize (IH ys); nia.
  Qed.

  (** Constructing move instructions is linear in the sequence length. *)
  Lemma move_code_clock sq :
    (T_move_code sq <= 4 * N.of_nat (length sq + 1))%N.
  Proof.
    pose proof (ListDef.T_map_le (fun '(dst, src) => (dst, O.mov, [src]))
      (fun _ : positive * positive => 1%N) 1%N sq ltac:(intro; reflexivity)) as Hmap.
    time_unfold T_move_code. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Checking destinations and temporary freshness is linear in move count and width. *)
  Lemma moves_ok_clock par tmp w :
    (forall x, In x (map fst par) -> Pos.size_nat x <= w) -> Pos.size_nat tmp <= w ->
    (T_moves_ok par tmp <=
      64 * (PTrieT.c_trie + 1) * N.of_nat (length par + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hwidth Htmp.
    pose proof (distinct_vars_clock (map fst par) w Hwidth Empty) as Hdistinct.
    pose proof (ListDef.T_map_le fst (fun pair : positive * positive => Datatypes.T_fst pair)
      1%N par ltac:(intros []; reflexivity)) as Hfst.
    pose proof (ListDef.T_map_le snd (fun pair : positive * positive => Datatypes.T_snd pair)
      1%N par ltac:(intros []; reflexivity)) as Hsnd.
    pose proof (Datatypes.T_app_le (map fst par) (map snd par)) as Happend.
    assert (Hcallback : forall x, (1 + Pos.T_eqb tmp x <= N.of_nat w + 1)%N).
    { intro x. pose proof (Pos.T_eqb_le tmp x). apply time_of_nat_le in Htmp. nia. }
    pose proof (List.T_existsb_le (fun x => Pos.eqb tmp x)
      (fun x => (1 + Pos.T_eqb tmp x)%N) (N.of_nat w + 1)%N
      (map fst par ++ map snd par) Hcallback) as Hexists.
    time_unfold T_moves_ok. unfold Datatypes.T_negb.
    rewrite !length_map in Hdistinct, Happend.
    rewrite length_app, !length_map in Hexists.
    destruct (distinct_vars (map fst par) Empty);
      rewrite !Nat2N.inj_add in *; nia.
  Qed.

  (** The producer retains the common width of its input variables and temporary. *)
  Lemma sequence_var_width par tmp w :
    (forall x, In x (map fst par ++ map snd par) -> Pos.size_nat x <= w) ->
    Pos.size_nat tmp <= w ->
    forall x, In x (map fst (PM.seq par tmp) ++ map snd (PM.seq par tmp)) ->
      Pos.size_nat x <= w.
  Proof.
    intros Hpar Htmp x Hx. apply in_app_or in Hx as [Hx|Hx];
      apply in_map_iff in Hx as [m [Heq Hm]]; subst x.
    - destruct (proj1 (PM.seq_ids par tmp m Hm)) as [Hin|Heq].
      + apply Hpar. apply in_or_app. now left.
      + now rewrite Heq.
    - destruct (proj2 (PM.seq_ids par tmp m Hm)) as [Hin|Heq].
      + apply Hpar. apply in_or_app. now right.
      + now rewrite Heq.
  Qed.

  (** The producer and checker calls satisfy a common move-count and width bound. *)
  Lemma sequence_checks_clock par tmp w :
    (forall x, In x (map fst par ++ map snd par) -> Pos.size_nat x <= w) ->
    Pos.size_nat tmp <= w ->
    (PM.T_seq par tmp + PM.T_check_moves par tmp (PM.seq par tmp) <=
      8 * (PM.c_pm + 1) * N.of_nat (length par + 1) * N.of_nat (w + 1))%N.
  Proof.
    intros Hwidth Htmp.
    pose proof (par_bits_bound par w Hwidth) as Hpar.
    assert (Hall : bits_of (par ++ PM.seq par tmp) <= w).
    { apply par_bits_bound. intros x Hx.
      rewrite !map_app in Hx. apply in_app_or in Hx as [Hx|Hx];
        apply in_app_or in Hx as [Hx|Hx].
      - apply Hwidth. apply in_or_app. now left.
      - apply (sequence_var_width par tmp w Hwidth Htmp). apply in_or_app. now left.
      - apply Hwidth. apply in_or_app. now right.
      - apply (sequence_var_width par tmp w Hwidth Htmp). apply in_or_app. now right. }
    pose proof (PM.T_seq_le par tmp) as Hseq.
    pose proof (PM.T_check_moves_le par tmp (PM.seq par tmp)) as Hcheck.
    pose proof (PM.seq_length par tmp) as Hlength.
    apply time_of_nat_le in Hpar. apply time_of_nat_le in Hall.
    apply time_of_nat_le in Hlength. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** Parameter indexing is linear in block count and parameter count at the input width. *)
  Lemma params_index_clock bs w :
    (forall id body, In (id, body) bs -> Pos.size_nat id <= w /\
      forall x, In x (params _ _ _ body) -> Pos.size_nat x <= w) ->
    (T_params_index bs <= 32 * (PTrieT.c_trie + 1) *
      N.of_nat (length bs + block_sum (fun body => length (params _ _ _ body)) bs + 1) *
      N.of_nat (w + 1))%N.
  Proof.
    induction bs as [|[id body] rest IH]; intro Hwidth.
    - time_unfold T_params_index. cbn [length block_sum fold_right].
      rewrite Nat2N.inj_add. nia.
    - destruct (Hwidth id body (or_introl eq_refl)) as [Hid Hparams].
      specialize (IH (fun key b Hin => Hwidth key b (or_intror Hin))).
      pose proof (distinct_vars_clock (params _ _ _ body) w Hparams Empty) as Hdistinct.
      apply time_of_nat_le in Hid.
      time_unfold T_params_index. unfold T_params.
      cbn [length block_sum fold_right snd]. unfold block_sum in IH.
      destruct (distinct_vars (params _ _ _ body) Empty).
      + destruct (params_index rest) as [table|].
        * pose proof (PTrieT.T_set_le (list positive) id (params _ _ _ body) table) as Hset.
          rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
        * rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
      + rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *. nia.
  Qed.

  (** An empty-parameter check performs a single trie lookup. *)
  Lemma empty_params_clock table target w : Pos.size_nat target <= w ->
    (T_empty_params table target <= 4 * N.of_nat (w + 1))%N.
  Proof.
    intro Hwidth. pose proof (PTrieT.T_trie_get_le (list positive) target table) as Hget.
    time_unfold T_empty_params.
    apply time_of_nat_le in Hwidth. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Preflight reads and emitted move instructions fit the source code and argument budget. *)
  Lemma inserted_moves_clock instructions actuals par tmp : length par = length actuals ->
    (ListDef.T_map (fun src : positive => (tmp, src)) (fun _ => 1%N) actuals +
      T_move_code (map (fun src => (tmp, src)) actuals) + T_move_code (PM.seq par tmp) +
      Datatypes.T_app (move_code (map (fun src => (tmp, src)) actuals))
        (move_code (PM.seq par tmp)) +
      Datatypes.T_app instructions (move_code (map (fun src => (tmp, src)) actuals) ++
        move_code (PM.seq par tmp)) <=
      32 * N.of_nat (length instructions + length actuals + 1))%N.
  Proof.
    intro Hlength. pose proof (PM.seq_length par tmp) as Hsequence_length.
    pose proof (ListDef.T_map_le (fun src : positive => (tmp, src))
      (fun _ : positive => 1%N) 1%N actuals ltac:(intro; reflexivity)) as Hmap.
    pose proof (move_code_clock (map (fun src => (tmp, src)) actuals)) as Hreads.
    pose proof (move_code_clock (PM.seq par tmp)) as Hsequence.
    pose proof (Datatypes.T_app_le (move_code (map (fun src => (tmp, src)) actuals))
      (move_code (PM.seq par tmp))) as Hreads_append.
    pose proof (Datatypes.T_app_le instructions
      (move_code (map (fun src => (tmp, src)) actuals) ++ move_code (PM.seq par tmp)))
      as Hcode_append.
    assert (Hreads_length : length (move_code (map (fun src => (tmp, src)) actuals)) =
        length actuals).
    { unfold move_code. now rewrite !length_map. }
    rewrite Hreads_length in Hreads_append. rewrite length_map in Hreads.
    rewrite Hlength in Hsequence_length. apply time_of_nat_le in Hsequence_length.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. lia.
  Qed.

  (** The component clock bounds combine within the declared block-copy budget. *)
  Lemma copy_move_cost_bound syntax checked pairing target n m w :
    (syntax <= 32 * (m + n + 1))%N ->
    (checked <= (8 * (PM.c_pm + 1) + 64 * (PTrieT.c_trie + 1)) *
      (n + 1) * (w + 1))%N ->
    (pairing <= n + 1)%N -> (target <= w)%N ->
    (4 + 2 * target + pairing + checked + syntax <=
      256 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1))%N.
  Proof.
    intros Hsyntax Hchecked Hpairing Htarget.
    assert (Hchecked_bound : (checked <=
        128 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1))%N).
    { eapply N.le_trans; [exact Hchecked|]. apply N.mul_le_mono_r.
      apply N.mul_le_mono; lia. }
    assert (Hoverhead : (4 + 2 * target + pairing + syntax <=
        64 * (m + n + 1) * (w + 1))%N).
    { clear -Hsyntax Hpairing Htarget. nia. }
    assert (Hoverhead_bound : (4 + 2 * target + pairing + syntax <=
        64 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1))%N).
    { eapply N.le_trans; [exact Hoverhead|]. apply N.mul_le_mono_r.
      apply N.mul_le_mono_r. lia. }
    replace (4 + 2 * target + pairing + checked + syntax)%N with
      (checked + (4 + 2 * target + pairing + syntax))%N by ring.
    eapply N.le_trans.
    - apply N.add_le_mono; [exact Hchecked_bound|exact Hoverhead_bound].
    - replace (128 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1) +
        64 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1))%N with
        (192 * (PTrieT.c_trie + PM.c_pm + 1) * (m + n + 1) * (w + 1))%N by ring.
      apply N.mul_le_mono_r. apply N.mul_le_mono_r. lia.
  Qed.

  (** Rewriting one block charges its code, edge arguments and bounded move calls. *)
  Lemma copy_block_clock table tmp body w :
    (forall x, In x (exit_targets (term _ _ _ body)) -> Pos.size_nat x <= w) ->
    (forall x, In x (exit_uses (term _ _ _ body)) -> Pos.size_nat x <= w) ->
    (forall target formals, trie_get target table = Some formals ->
      forall x, In x formals -> Pos.size_nat x <= w) ->
    Pos.size_nat tmp <= w ->
    (T_copy_block table tmp body <= 256 * (PTrieT.c_trie + PM.c_pm + 1) *
      N.of_nat (length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1) *
      N.of_nat (w + 1))%N.
  Proof.
    destruct body as [parameters instructions ending].
    intros Htargets Huses Htable Htmp.
    destruct ending as [target actuals|guard operands yes ys no ns|values];
      cbn [term code exit_targets exit_uses exit_arg_count] in *.
    - pose proof (Htargets target (or_introl eq_refl)) as Htarget.
      pose proof (PTrieT.T_trie_get_le (list positive) target table) as Hget.
      unfold T_copy_block, T_term, T_code. cbn [term code].
      destruct (trie_get target table) as [formals|] eqn:Hrow.
      + pose proof (pair_moves_clock formals actuals) as Hpairtime.
        destruct (pair_moves formals actuals) as [[|first par]|] eqn:Hpair.
        * apply time_of_nat_le in Htarget. rewrite !Nat2N.inj_add in *. nia.
        * assert (Hparwidth : forall x, In x (map fst (first :: par) ++
              map snd (first :: par)) -> Pos.size_nat x <= w).
          { destruct (pair_moves_rows _ _ _ Hpair) as [Hleft Hright].
            intros x Hx. apply in_app_or in Hx as [Hx|Hx].
            - rewrite Hleft in Hx. exact (Htable target formals Hrow x Hx).
            - rewrite Hright in Hx. exact (Huses x Hx). }
          assert (Hparlength : length (first :: par) = length actuals).
          { destruct (pair_moves_rows _ _ _ Hpair) as [Hleft Hright].
            pose proof (f_equal (@length positive) Hright) as Hlength.
            now rewrite length_map in Hlength. }
          pose proof (moves_ok_clock (first :: par) tmp w
            (fun x Hx => Hparwidth x (in_or_app _ _ _ (or_introl Hx))) Htmp) as Hmoves.
          pose proof (sequence_checks_clock (first :: par) tmp w Hparwidth Htmp) as Hcalls.
          pose proof (inserted_moves_clock instructions actuals (first :: par) tmp Hparlength)
            as Hinsert.
          pose proof (N.add_le_mono _ _ _ _ Hcalls Hmoves) as Hchecked.
          apply time_of_nat_le in Htarget. rewrite Hparlength in Hchecked.
          rewrite !Nat2N.inj_add in Hinsert.
          rewrite !Nat2N.inj_add in Hchecked.
          rewrite Nat2N.inj_add in Hpairtime. rewrite !Nat2N.inj_add.
          change (N.of_nat 1) with 1%N in Hinsert, Hchecked, Hpairtime |- *.
          assert (Hchecked' : (PM.T_seq (first :: par) tmp +
              PM.T_check_moves (first :: par) tmp (PM.seq (first :: par) tmp) +
              T_moves_ok (first :: par) tmp <=
              (8 * (PM.c_pm + 1) + 64 * (PTrieT.c_trie + 1)) *
                (N.of_nat (length actuals) + 1) * (N.of_nat w + 1))%N).
          { eapply N.le_trans; [exact Hchecked|]. apply N.eq_le_incl. ring. }
          pose proof (copy_move_cost_bound _ _ _ _ (N.of_nat (length actuals))
            (N.of_nat (length instructions)) (N.of_nat w)
            Hinsert Hchecked' Hpairtime Htarget) as Hcost.
          clear - Hcost Hget.
          destruct (moves_ok (first :: par) tmp);
            [destruct (PM.check_moves (first :: par) tmp (PM.seq (first :: par) tmp))|]; lia.
        * apply time_of_nat_le in Htarget. rewrite !Nat2N.inj_add in *. nia.
      + apply time_of_nat_le in Htarget. rewrite !Nat2N.inj_add in *. nia.
    - destruct ys as [|y ys]; [|unfold T_copy_block, T_term; cbn [term];
          rewrite !Nat2N.inj_add; nia].
      destruct ns as [|n ns]; [|unfold T_copy_block, T_term; cbn [term];
          rewrite !Nat2N.inj_add; nia].
      pose proof (empty_params_clock table yes w (Htargets yes (or_introl eq_refl))) as Hyes.
      pose proof (empty_params_clock table no w (Htargets no (or_intror (or_introl eq_refl))))
        as Hno.
      unfold T_copy_block, T_term, T_code, Datatypes.T_andb. cbn [term code].
      destruct (andb (empty_params table yes) (empty_params table no));
        rewrite !Nat2N.inj_add; nia.
    - unfold T_copy_block, T_term, T_code. cbn [term code]. rewrite !Nat2N.inj_add. nia.
  Qed.

  (** The complete copy pass sums the per-block syntax and argument budgets. *)
  Lemma copy_blocks_clock table tmp bs w :
    (forall id body, In (id, body) bs ->
      (forall x, In x (exit_targets (term _ _ _ body)) -> Pos.size_nat x <= w) /\
      (forall x, In x (exit_uses (term _ _ _ body)) -> Pos.size_nat x <= w)) ->
    (forall target formals, trie_get target table = Some formals ->
      forall x, In x formals -> Pos.size_nat x <= w) ->
    Pos.size_nat tmp <= w ->
    (T_copy_blocks table tmp bs <= 512 * (PTrieT.c_trie + PM.c_pm + 1) *
      N.of_nat (block_sum (fun body =>
        (length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1)%nat) bs + 1) *
      N.of_nat (w + 1))%N.
  Proof.
    induction bs as [|[id body] rest IH]; intros Hwidth Htable Htmp.
    - time_unfold T_copy_blocks. cbn [block_sum fold_right]. rewrite Nat2N.inj_add. nia.
    - destruct (Hwidth id body (or_introl eq_refl)) as [Htargets Huses].
      pose proof (copy_block_clock table tmp body w Htargets Huses Htable Htmp) as Hhead.
      specialize (IH (fun key b Hin => Hwidth key b (or_intror Hin)) Htable Htmp).
      time_unfold T_copy_blocks. destruct (copy_block table tmp body) as [[body' one]|];
        cbn [block_sum fold_right snd]; unfold block_sum in IH;
        rewrite !Nat2N.inj_add in *; nia.
  Qed.

  (** All listed parameters are included in the block variable inventory. *)
  Lemma block_params_budget bs :
    block_sum (fun body => length (params _ _ _ body)) bs <= length (block_variables bs).
  Proof.
    induction bs as [|[id body] rest IH]; [reflexivity|].
    change (length (params _ _ _ body) +
      block_sum (fun body => length (params _ _ _ body)) rest <=
      length (body_variables body ++ block_variables rest)).
    rewrite length_app. unfold body_variables. rewrite !length_app. lia.
  Qed.

  (** Block count and parameter count fit the function syntax budget. *)
  Lemma function_params_budget (s : P.t) :
    length (blocks _ _ _ s) +
      block_sum (fun body => length (params _ _ _ body)) (blocks _ _ _ s) <= function_size s.
  Proof.
    pose proof (block_params_budget (blocks _ _ _ s)) as Hparams.
    assert (Hvars : length (block_variables (blocks _ _ _ s)) <= length (function_vars s)).
    { change (length (block_variables (blocks _ _ _ s)) <=
        length (inputs _ _ _ s ++ block_variables (blocks _ _ _ s))).
      rewrite length_app. lia. }
    unfold function_size. lia.
  Qed.

  (** The copy-pass weight is exactly code count, edge arguments and block count. *)
  Lemma copy_weight_sum bs :
    block_sum (fun body => length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1) bs =
    block_sum (fun body => length (code _ _ _ body)) bs +
      block_sum (fun body => exit_arg_count (term _ _ _ body)) bs + length bs.
  Proof.
    induction bs as [|[id body] rest IH]; [reflexivity|].
    unfold block_sum in *. cbn [fold_right snd length]. rewrite IH. lia.
  Qed.

  (** The complete copy-pass weight fits function syntax and edge-argument counts. *)
  Lemma function_copy_budget (s : P.t) :
    block_sum (fun body => length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1)
      (blocks _ _ _ s) <= function_size s + destroy_edge_args s.
  Proof.
    rewrite copy_weight_sum, <- destroy_args_sum. unfold function_size, block_sum. lia.
  Qed.

  (** The common copy budget includes the public trie and move-operation constants. *)
  Definition copy_budget (s : P.t) w : N :=
    (PTrieT.c_trie + PM.c_pm + 1) * N.of_nat (function_size s + destroy_edge_args s + 1) *
      N.of_nat (w + 2).

  (** Smaller coefficients, syntax measures and widths fit the common copy budget. *)
  Lemma copy_budget_mono s w c n b : (c <= PTrieT.c_trie + PM.c_pm + 1)%N ->
    n <= function_size s + destroy_edge_args s + 1 -> b <= w + 2 ->
    (c * N.of_nat n * N.of_nat b <= copy_budget s w)%N.
  Proof.
    intros Hc Hn Hb. unfold copy_budget.
    apply N.mul_le_mono; [apply N.mul_le_mono; [exact Hc|]|];
      apply time_of_nat_le; assumption.
  Qed.

  (** The common copy budget is positive even for empty or malformed programs. *)
  Lemma copy_budget_positive s w : (1 <= copy_budget s w)%N.
  Proof.
    change (1 * N.of_nat 1 * N.of_nat 1 <= copy_budget s w)%N.
    apply copy_budget_mono; lia.
  Qed.

  (** Variable collection fits the common copy budget. *)
  Lemma copy_syntax_clock s w : (T_function_vars s <= 128 * copy_budget s w)%N.
  Proof.
    eapply N.le_trans; [apply destroy_function_vars_clock|].
    replace (128 * N.of_nat (function_size s + 1))%N with
      (128 * (1 * N.of_nat (function_size s + 1) * N.of_nat 1))%N
      by (cbn [N.of_nat]; ring).
    apply N.mul_le_mono_l. apply copy_budget_mono; lia.
  Qed.

  (** An identifier-width bound also bounds every function variable. *)
  Lemma bounded_function_vars (s : P.t) w :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    forall x, In x (function_vars s) -> Pos.size_nat x <= w.
  Proof.
    intros Hids x Hx. apply Hids. unfold function_ids. right. apply in_or_app. now left.
  Qed.

  (** An identifier-width bound is positive because it includes the entry identifier. *)
  Lemma bounded_function_positive (s : P.t) w :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) -> 1 <= w.
  Proof.
    intro Hids. pose proof (Hids (entry _ _ _ s) (or_introl eq_refl)) as Hentry.
    pose proof (Pos.size_nat_pos (entry _ _ _ s)). lia.
  Qed.

  (** The fresh-temporary scan fits the common copy budget. *)
  Lemma copy_fresh_clock s w :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    (T_fresh_after (function_vars s) <= 8 * copy_budget s w)%N.
  Proof.
    intro Hids. eapply N.le_trans.
    - apply fresh_after_clock; [exact (bounded_function_positive s w Hids)|].
      exact (bounded_function_vars s w Hids).
    - replace (8 * N.of_nat (length (function_vars s) + 1) * N.of_nat (w + 1))%N with
        (8 * (1 * N.of_nat (length (function_vars s) + 1) * N.of_nat (w + 1)))%N by ring.
      apply N.mul_le_mono_l. apply copy_budget_mono; try lia.
      unfold function_size. lia.
  Qed.

  (** The parameter-index pass fits the common copy budget. *)
  Lemma copy_index_clock s w :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    (T_params_index (blocks _ _ _ s) <= 32 * copy_budget s w)%N.
  Proof.
    intro Hids. eapply N.le_trans.
    - apply (params_index_clock (blocks _ _ _ s) w).
      intros id body Hbody. split.
      + apply Hids. exact (split_block_id_in s id body Hbody).
      + intros x Hx. apply (bounded_function_vars s w Hids).
        exact (listed_params s id body Hbody x Hx).
    - replace (32 * (PTrieT.c_trie + 1) *
        N.of_nat (length (blocks _ _ _ s) +
          block_sum (fun body => length (params _ _ _ body)) (blocks _ _ _ s) + 1) *
        N.of_nat (w + 1))%N with
        (32 * ((PTrieT.c_trie + 1) *
          N.of_nat (length (blocks _ _ _ s) +
            block_sum (fun body => length (params _ _ _ body)) (blocks _ _ _ s) + 1) *
          N.of_nat (w + 1)))%N by ring.
      apply N.mul_le_mono_l. apply copy_budget_mono; try lia.
      pose proof (function_params_budget s). lia.
  Qed.

  (** Looking up the entry parameter row fits the common copy budget. *)
  Lemma copy_entry_clock s w (table : ptrie (list positive)) :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    (T_trie_get (entry _ _ _ s) table <= 2 * copy_budget s w)%N.
  Proof.
    intro Hids.
    eapply N.le_trans; [apply (PTrieT.T_trie_get_le _ (entry _ _ _ s) table)|].
    replace (2 * N.of_nat (Pos.size_nat (entry _ _ _ s)))%N with
      (2 * (1 * N.of_nat 1 * N.of_nat (Pos.size_nat (entry _ _ _ s))))%N
      by (cbn [N.of_nat]; ring).
    apply N.mul_le_mono_l. apply copy_budget_mono; try lia.
    pose proof (Hids (entry _ _ _ s) (or_introl eq_refl)). lia.
  Qed.

  (** A successful parameter index stores only variables within the source width. *)
  Lemma copy_index_width s w table :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    params_index (blocks _ _ _ s) = Some table ->
    forall target formals, trie_get target table = Some formals ->
      forall x, In x formals -> Pos.size_nat x <= w + 1.
  Proof.
    intros Hids Hindex target formals Hrow x Hx.
    rewrite (params_index_find _ _ Hindex) in Hrow.
    destruct (find_block target (blocks _ _ _ s)) as [body|] eqn:Hfind; [|discriminate].
    injection Hrow as Hrow. subst formals.
    pose proof (bounded_function_vars s w Hids x
      (listed_params s target body (find_source_block _ _ _ Hfind) x Hx)). lia.
  Qed.

  (** Rewriting all indexed blocks fits the common copy budget. *)
  Lemma copy_body_clocks s w table :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    params_index (blocks _ _ _ s) = Some table ->
    (T_copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s) <=
      512 * copy_budget s w)%N.
  Proof.
    intros Hids Hindex. eapply N.le_trans.
    - apply (copy_blocks_clock table (fresh_after (function_vars s)) (blocks _ _ _ s) (w + 1)).
      + intros id body Hbody. split.
        * intros x Hx. pose proof (Hids x (split_target_id_in s id body x Hbody Hx)). lia.
        * intros x Hx. pose proof (bounded_function_vars s w Hids x
            (listed_exit_uses s id body Hbody x Hx)). lia.
      + exact (copy_index_width s w table Hids Hindex).
      + apply fresh_after_width; [exact (bounded_function_positive s w Hids)|].
        exact (bounded_function_vars s w Hids).
    - replace (512 * (PTrieT.c_trie + PM.c_pm + 1) *
        N.of_nat (block_sum (fun body =>
          (length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1)%nat)
          (blocks _ _ _ s) + 1) * N.of_nat (w + 1 + 1))%N with
        (512 * ((PTrieT.c_trie + PM.c_pm + 1) *
          N.of_nat (block_sum (fun body =>
            (length (code _ _ _ body) + exit_arg_count (term _ _ _ body) + 1)%nat)
            (blocks _ _ _ s) + 1) * N.of_nat (w + 1 + 1)))%N by ring.
      apply N.mul_le_mono_l. apply copy_budget_mono; try lia.
      pose proof (function_copy_budget s). lia.
  Qed.

  (** The copy wrapper satisfies its budget on successful and rejected inputs alike. *)
  Lemma copies_clock s w :
    (forall x, In x (function_ids s) -> Pos.size_nat x <= w) ->
    (T_copies s <= 4096 * copy_budget s w)%N.
  Proof.
    intro Hids.
    pose proof (copy_budget_positive s w) as Hpositive.
    pose proof (copy_syntax_clock s w) as Hsyntax.
    pose proof (copy_fresh_clock s w Hids) as Hfresh.
    pose proof (copy_index_clock s w Hids) as Hparams.
    time_unfold T_copies. time_unfold T_copy_stage.
    unfold T_blocks, T_entry, T_inputs.
    destruct (params_index (blocks _ _ _ s)) as [table|] eqn:Hindex; [|lia].
    pose proof (copy_entry_clock s w table Hids) as Hentry.
    pose proof (copy_body_clocks s w table Hids Hindex) as Hblocks.
    destruct (trie_get (entry _ _ _ s) table) as [[|x xs]|]; try lia.
    destruct (copy_blocks table (fresh_after (function_vars s)) (blocks _ _ _ s))
      as [[bs checked]|]; lia.
  Qed.

  (** Copy insertion after splitting fits the original function budget. *)
  Lemma copies_source_clock s split_s : split s = Some split_s ->
    (T_copies split_s <= 16384 * (PTrieT.c_trie + PM.c_pm + 1) *
      N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof.
    intro Hsplit.
    pose proof (copies_clock split_s (function_width s + 2)
      (split_ids_width s split_s Hsplit)) as Hcopies.
    assert (Hwork : function_size split_s + destroy_edge_args split_s + 1 = destroy_work s).
    { destruct (split_inventory _ _ Hsplit) as [_ [Hsize [Hargs Hblocks]]].
      rewrite Hsize, Hargs. unfold destroy_work. lia. }
    unfold copy_budget in Hcopies. rewrite Hwork in Hcopies.
    eapply N.le_trans; [exact Hcopies|].
    replace (16384 * (PTrieT.c_trie + PM.c_pm + 1) * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1))%N with
      ((4096 * (PTrieT.c_trie + PM.c_pm + 1) * N.of_nat (destroy_work s)) *
        (4 * N.of_nat (function_width s + 1)))%N by ring.
    replace (4096 * ((PTrieT.c_trie + PM.c_pm + 1) * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 2 + 2)))%N with
      ((4096 * (PTrieT.c_trie + PM.c_pm + 1) * N.of_nat (destroy_work s)) *
        N.of_nat (function_width s + 2 + 2))%N by ring.
    apply N.mul_le_mono_l. rewrite !Nat2N.inj_add. lia.
  Qed.

  (** The wrapper combines both transformation phases within the published source budget. *)
  Lemma destroy_source_clock s :
    (T_destroy s <= (4097 + 16384 * (PTrieT.c_trie + PM.c_pm + 1)) *
      N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof.
    pose proof (split_source_clock s) as Hsplit.
    assert (Hwork : (1 <= N.of_nat (destroy_work s))%N).
    { change (N.of_nat 1 <= N.of_nat (destroy_work s))%N.
      apply time_of_nat_le. unfold destroy_work. lia. }
    assert (Hwidth : (1 <= N.of_nat (function_width s + 1))%N).
    { change (N.of_nat 1 <= N.of_nat (function_width s + 1))%N.
      apply time_of_nat_le. lia. }
    assert (Hunit : (1 <= N.of_nat (destroy_work s) *
        N.of_nat (function_width s + 1))%N).
    { change (1 * 1 <= N.of_nat (destroy_work s) *
        N.of_nat (function_width s + 1))%N. apply N.mul_le_mono; assumption. }
    time_unfold T_destroy. destruct (split s) as [split_s|] eqn:Hphase.
    - pose proof (copies_source_clock s split_s Hphase) as Hcopies. nia.
    - nia.
  Qed.


  Lemma T_destroy_le : forall s,
    (T_destroy s <= c_ds * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof.
    intro s. unfold c_ds. apply destroy_source_clock.
  Qed.
  Lemma destroy_complexity : bigO (fun _ : P.t => True)
    (fun s => N.of_nat (destroy_work s * (function_width s + 1))) T_destroy.
  Proof.
    exists c_ds. intros s Htrue. pose proof (T_destroy_le s) as Hclock.
    rewrite Nat2N.inj_mul. nia.
  Qed.
  Definition k_split : N := 4096.
  Definition k_copies : N := 16384 * (PTrieT.c_trie + PM.c_pm + 1).
  Definition k_wrap : N := 1.
  Lemma destroy_def : forall s, destroy s =
    match split s with None => None | Some split_s => copies split_s end.
  Proof.
    reflexivity.
  Qed.
  (** Splitting preserves SSA and the stated finite-observation fuel bounds. *)
  Lemma split_semantics_preserved : forall s split_s, ssa_wf s -> split s = Some split_s ->
    ssa_wf split_s /\ forall n ins r, r <> Timeout ->
      (run_with O.eval O.test n s ins = r -> run_with O.eval O.test (2 * n) split_s ins = r) /\
      (run_with O.eval O.test n split_s ins = r -> run_with O.eval O.test n s ins = r).
  Proof.
    exact split_preserves_complete.
  Qed.
  Lemma checked_moves_valid : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) ->
    NoDup (map fst par) /\ ~ In tmp (map fst par ++ map snd par) /\
      PM.check_moves par tmp sq = true.
  Proof.
    intros s p par tmp sq Hcopies Hin.
    pose proof (checked_moves_good s) as Hchecked.
    rewrite Forall_forall in Hchecked. exact (Hchecked (par, tmp, sq) Hin).
  Qed.
  Lemma edge_copy_simulates : forall s p par tmp sq, copies s = Some p ->
    In (par, tmp, sq) (checked_moves s) -> forall (e : positive -> option O.C) x,
      x <> tmp -> exec_seq sq e x = exec_par par e x.
  Proof.
    intros s p par tmp sq Hcopies Hin e x Hneq.
    destruct (checked_moves_valid s p par tmp sq Hcopies Hin) as [Hdistinct [Hfresh Hchecked]].
    exact (PM.check_moves_sound par tmp sq Hdistinct Hfresh Hchecked O.C e x Hneq).
  Qed.
  Lemma block_copies_simulate : forall s p ss sp, ssa_wf s -> copies s = Some p ->
    entered_agree s p ss sp ->
    copy_outcomes s p (step O.eval O.test s ss) (step O.eval O.test p sp).
  Proof.
    intros s p ss sp Hssa Hcopies Hagree. exact (copies_block_sim s p ss sp Hcopies Hagree).
  Qed.
  Lemma copies_run_agrees : forall s p, ssa_wf s -> copies s = Some p ->
    forall n ins, run_with O.eval O.test n s ins = run_with O.eval O.test n p ins.
  Proof.
    intros s p Hssa Hcopies. exact (copies_run s p Hcopies).
  Qed.
  Lemma copies_imp_form : forall s p, copies s = Some p -> imp_form p.
  Proof.
    intros s p Hcopies. exact (proj2 (proj2 (copies_shape s p Hcopies))).
  Qed.
  Lemma run_fuel_mono : forall (p : P.t) n m ins r, n <= m -> r <> Timeout ->
    run_with O.eval O.test n p ins = r -> run_with O.eval O.test m p ins = r.
  Proof.
    apply run_with_mono.
  Qed.
  Lemma T_split_le : forall s,
    (T_split s <= k_split * N.of_nat (destroy_work s) * N.of_nat (function_width s + 1))%N.
  Proof.
    intro s. unfold k_split. apply split_source_clock.
  Qed.
  Lemma checked_moves_size_le : forall s split_s, split s = Some split_s ->
    fold_right (fun mc n => length (fst (fst mc)) + 1 + n) 0 (checked_moves split_s) <=
      destroy_work s /\
    forall par tmp sq, In (par, tmp, sq) (checked_moves split_s) ->
      sq = PM.seq par tmp /\ bits_of par + Pos.size_nat tmp <= 2 * (function_width s + 1).
  Proof.
    intros s split_s Hsplit.
    destruct (split_inventory _ _ Hsplit) as [Hvars [Hsize [Hargs Hlength]]].
    split.
    - change (checks_size (checked_moves split_s) <= destroy_work s).
      pose proof (checked_moves_size split_s) as Hchecks.
      assert (Hblocks : length (blocks _ _ _ s) <= function_size s).
      { unfold function_size. lia. }
      rewrite Hargs, Hlength in Hchecks. unfold destroy_work. lia.
    - intros par tmp sq Hin.
      destruct (checked_moves_origin _ _ _ _ Hin) as [Htmp [Hseq Hids]].
      split; [exact Hseq|].
      assert (Hwidth : forall x, In x (function_vars split_s) ->
          Pos.size_nat x <= function_width s).
      { intros x Hx. rewrite Hvars in Hx. exact (function_var_width s x Hx). }
      pose proof (par_bits_bound par (function_width s)
        (fun x Hx => Hwidth x (Hids x Hx))) as Hpar.
      pose proof (fresh_after_width (function_vars split_s) (function_width s)
        (function_width_positive s) Hwidth) as Hfresh.
      rewrite Htmp. lia.
  Qed.
  Lemma T_copies_split : forall s split_s, split s = Some split_s ->
    (T_copies split_s <= k_copies * N.of_nat (destroy_work s) *
      N.of_nat (function_width s + 1) +
      fold_right N.add 0%N (map (fun mc =>
        PM.T_seq (fst (fst mc)) (snd (fst mc)) +
        PM.T_check_moves (fst (fst mc)) (snd (fst mc)) (snd mc))%N
        (checked_moves split_s)))%N.
  Proof.
    intros s split_s Hsplit. pose proof (copies_source_clock s split_s Hsplit) as Hcopies.
    unfold k_copies. lia.
  Qed.
  Lemma T_destroy_split : forall s,
    (T_destroy s <= T_split s +
      match split s with None => k_wrap | Some split_s => T_copies split_s + k_wrap end)%N.
  Proof.
    intro s. unfold k_wrap. time_unfold T_destroy. destruct (split s); time_cbn; lia.
  Qed.
End DestroyT.
