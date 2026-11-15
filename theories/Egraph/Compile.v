(** * Flat rewrite compilation

    Compilation names constructor nodes, queries the left side and builds the right side.
    For example, the rewrite [f(x) = x] queries [f] and joins its result with [x].
    Builds on: CompileSig. *)

From Stdlib Require Import List PArith NArith Arith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Egglog Require Import ValueSig DatabaseSig Syntax Model Sorts.
From Galois.Egraph Require Import Syntax CompileSig.

Import List.ListNotations.

Definition name_max (x y : positive) : positive :=
  match Pos.compare x y with
  | Lt => y
  | _ => x
  end.
TimeFun name_max.

(** The largest hole name in a pattern bounds the names that compilation must preserve. *)
Fixpoint pattern_max {A} (ns : list (pnode A)) : positive :=
  match ns with
  | [] => 1%positive
  | PHole h :: rest => name_max h (pattern_max rest)
  | _ :: rest => pattern_max rest
  end.
TimeFun pattern_max.

Definition term_name {A} (t : term A) : positive :=
  match t with
  | Var x => x
  | Lit _ => 1%positive
  end.
TimeFun term_name.

Definition atom_name_max {A} (a : atom A) : positive :=
  match a with
  | Fun _ _ args res =>
    fold_right (fun t m => name_max (term_name t) m)
      (match res with Some t => term_name t | None => 1%positive end) args
  | Prim _ _ args res =>
    fold_right (fun t m => name_max (term_name t) m) (term_name res) args
  end.
TimeFun atom_name_max.

(** The root countdown distinguishes the root without rescanning its prefix. *)
Definition next_root (r : option nat) : option nat :=
  match r with
  | Some (S n) => Some n
  | _ => None
  end.
TimeFun next_root.

(** A table keeps hole and literal terms and gives every constructor a fresh variable. *)
Fixpoint pattern_terms {A} (ns : list (pnode A)) (r : option nat)
    (root_name fresh : positive) : list (term A) * positive :=
  match ns with
  | [] => ([], fresh)
  | n :: rest =>
    let '(t, fresh') :=
      match n with
      | PHole h => (Var h, fresh)
      | PLit v => (Lit v, fresh)
      | PApp _ _ =>
        match r with
        | Some 0 => (Var root_name, fresh)
        | _ => (Var fresh, Pos.succ fresh)
        end
      end in
    let '(ts, last) := pattern_terms rest (next_root r) root_name fresh' in
    (t :: ts, last)
  end.
TimeFun pattern_terms.

Definition pattern_table {A} (p : fpat A) (root_name : positive)
    : list (term A) * positive :=
  match p with
  | FPat _ ns r => pattern_terms ns (Some r) root_name (Pos.succ root_name)
  end.
TimeFun pattern_table.

Definition pattern_get {A} (default : term A) (j : nat) (ts : list (term A)) : term A :=
  match nth_error ts j with
  | Some t => t
  | None => default
  end.
TimeFun pattern_get.

(** Each constructor contributes one query atom whose children read the term table. *)
Fixpoint pattern_atoms {A} (ns : list (pnode A)) (ts all : list (term A))
    : list (atom A) :=
  match ns, ts with
  | n :: rest, t :: tail =>
    match n with
    | PApp f children =>
      Fun A f (map (fun j => pattern_get (Var 1%positive) j all) children) (Some t) ::
        pattern_atoms rest tail all
    | _ => pattern_atoms rest tail all
    end
  | _, _ => []
  end.
TimeFun pattern_atoms.

(** Right-side constructors become ordered allocations with the same table references. *)
Fixpoint pattern_actions {A} (ns : list (pnode A)) (ts all : list (term A))
    : list (action A) :=
  match ns, ts with
  | n :: rest, t :: tail =>
    match n, t with
    | PApp f children, Var x =>
      Make x f (map (fun j => pattern_get (Var 1%positive) j all) children) ::
        pattern_actions rest tail all
    | _, _ => pattern_actions rest tail all
    end
  | _, _ => []
  end.
TimeFun pattern_actions.

Module CompileCode (V : VALUE_OPS) <: COMPILE_OPS V.
  Definition root_var (rw : rewrite V.t) : positive :=
    match rw with
    | Rewrite _ (FPat _ lnodes _) (FPat _ rnodes _) conditions =>
      Pos.succ (name_max (pattern_max lnodes)
        (name_max (pattern_max rnodes)
          (fold_right (fun a m => name_max (atom_name_max a) m) 1%positive conditions)))
    end.

  Definition flatten_pat (p : fpat V.t) (x : positive) : list (atom V.t) :=
    match p with
    | FPat _ ns _ => let ts := fst (pattern_table p x) in pattern_atoms ns ts ts
    end.

  Definition flatten_lhs (rw : rewrite V.t) : list (atom V.t) :=
    match rw with
    | Rewrite _ lp _ conditions => flatten_pat lp (root_var rw) ++ conditions
    end.

  Definition compile_rule (rw : rewrite V.t) : rule V.t :=
    match rw with
    | Rewrite _ lp (FPat _ ns r as rp) _ =>
      let x := root_var rw in
      let next := snd (pattern_table lp x) in
      let ts := fst (pattern_table rp next) in
      Rule V.t (flatten_lhs rw)
        (pattern_actions ns ts ts ++ [Union (Var x) (pattern_get (Var next) r ts)])
    end.

  Definition compile (ds : list decl) (rws : list (rewrite V.t)) (ans : list (rule V.t))
      : program V.t := Program V.t ds (map compile_rule rws ++ ans).
End CompileCode.

Module Compile (V : VALUE) <: COMPILE V.
  Include CompileCode V.
  Include COMPILE_SPEC V.

  (** A cell occurs when some stored row contains it in its key or output. *)
  Definition row_cell (w : Model.view (V := V.t)) (c : cell V.t) : Prop :=
    exists f k o, row w f k o /\ In c (k ++ option_list o).

  (** Equal identifiers occurring in canonical rows are the same stored cell. *)
  Lemma canonical_cell_unique : forall w c d, canonical_view w ->
    row_cell w c -> row_cell w d -> cell_rel (same w) c d -> c = d.
  Proof.
    intros w c d [_ [_ [_ [_ Hcanonical]]]] Hc Hd Hsame.
    destruct Hsame as [i j Hij | v]; [| reflexivity].
    destruct Hc as [f [k [o [Hrow Hin]]]].
    destruct Hd as [f' [k' [o' [Hrow' Hin']]]].
    f_equal. exact (Hcanonical f k o f' k' o' i j Hrow Hrow' Hin Hin' Hij).
  Qed.

  (** Every key cell occurs in the row that owns that key. *)
  Lemma row_key_cells : forall w f k o, row w f k o -> Forall (row_cell w) k.
  Proof.
    intros w f k o Hrow. apply Forall_forall. intros c Hin.
    exists f, k, o. split; [exact Hrow |]. apply in_or_app. now left.
  Qed.

  (** Related canonical keys agree cell by cell. *)
  Lemma canonical_keys_unique : forall w k k', canonical_view w ->
    Forall (row_cell w) k -> Forall (row_cell w) k' ->
    Forall2 (cell_rel (same w)) k k' -> k = k'.
  Proof.
    intros w k k' Hcanonical Hleft Hright Hrelated.
    induction Hrelated as [| c d cs ds Hcd Htail IH].
    - reflexivity.
    - inversion Hleft as [| c' cs' Hc Hcs]; subst.
      inversion Hright as [| d' ds' Hd Hds]; subst.
      f_equal.
      + exact (canonical_cell_unique w c d Hcanonical Hc Hd Hcd).
      + exact (IH Hcs Hds).
  Qed.

  (** A represented expression determines its cell up to identifier equality. *)
  Lemma represents_unique : forall w c e, canonical_view w -> represents w c e ->
    forall d, represents w d e -> cell_rel (same w) c d.
  Proof.
    intros w c e Hcanonical Hrep.
    destruct Hcanonical as [Hrefl [Hsym [Htrans [Hfunctional Hstored]]]].
    assert (Hcanonical : canonical_view w) by (repeat split; assumption).
    induction Hrep as [v | f k i j args Hrow Hsame Hargs IHargs].
    - intros d Hother. inversion Hother; subst. constructor.
    - intros d Hother.
      inversion Hother as [v | f' k' i' j' args' Hrow' Hsame' Hargs']; subst.
      assert (Hrelated : Forall2 (cell_rel (same w)) k k').
      { clear Hrow Hsame Hrow' Hsame' Hother. revert k' Hargs'.
        induction IHargs as [| c0 e0 cs es Hrep0 IHhead Hrest IHrest IH];
          intros k' Hargs'.
        - inversion Hargs'; constructor.
        - inversion Hargs' as [| d0 e1 ds es' Hhead Htail]; subst.
          constructor; [exact (IHhead d0 Hhead) | exact (IH ds Htail)]. }
      assert (Hkeys : k = k').
      { eapply canonical_keys_unique; [exact Hcanonical | | | exact Hrelated];
          eapply row_key_cells; eassumption. }
      subst k'.
      assert (Houtput : j = j').
      { pose proof (Hfunctional f k _ _ Hrow Hrow') as Heq. congruence. }
      subst j'. constructor. eapply Htrans; [exact Hsame |].
      exact (Hsym i' j Hsame').
  Qed.

  (** A fixed substitution gives each flat pattern node at most one unfolding. *)
  Lemma unfolds_pat_unique : forall tau ns i e,
    @unfolds_pat V.t tau ns i e ->
    forall e', unfolds_pat tau ns i e' -> e = e'.
  Proof.
    intros tau ns i e Hunfold.
    induction Hunfold as [i h e Hnth Htau | i v Hnth |
      i f children args Hnth Hbefore Hargs IHargs]; intros e' Hother.
    - inversion Hother as [i' h' e'' Hnth' Htau' | i' v' Hnth' |
        i' f' children' args' Hnth' Hbefore' Hargs']; subst; try congruence.
    - inversion Hother as [i' h' e'' Hnth' Htau' | i' v' Hnth' |
        i' f' children' args' Hnth' Hbefore' Hargs']; subst; try congruence.
    - inversion Hother as [i' h' e'' Hnth' Htau' | i' v' Hnth' |
        i' f' children' args' Hnth' Hbefore' Hargs']; subst; try congruence.
      assert (f' = f /\ children' = children) as [-> ->] by (split; congruence).
      f_equal. clear Hnth Hnth' Hbefore Hbefore' Hother.
      revert args' Hargs'.
      induction IHargs as [| j e0 js es Hchild IHchild Htail IHtail IH];
        intros args' Hargs'.
      + inversion Hargs'; reflexivity.
      + inversion Hargs' as [| j' e1 js' es' Hhead Hrest]; subst.
        f_equal; [exact (IHchild e1 Hhead) | exact (IH es' Hrest)].
  Qed.

  (** Aligned unfolding and representation lists supply each referenced child. *)
  Lemma represented_children : forall tau ns w children args,
    Forall2 (@unfolds_pat V.t tau ns) children args ->
    forall cells, Forall2 (represents w) cells args -> forall j, In j children ->
      exists c e, In c cells /\ unfolds_pat tau ns j e /\ represents w c e.
  Proof.
    intros tau ns w children args Hunfold.
    induction Hunfold as [| j e js es Hchild Htail IH]; intros cells Hrep k Hin.
    - contradiction.
    - inversion Hrep as [| c e' cs es' Hhead Hrest]; subst.
      destruct Hin as [<- | Hin].
      + exists c, e. split; [now left |]. split; assumption.
      + destruct (IH cs Hrest k Hin) as [d [t [Hmember [Hu Hr]]]].
        exists d, t. split; [now right |]. split; assumption.
  Qed.

  (** A represented constructor supplies a row occurrence for every child node. *)
  Lemma represented_pattern_child : forall tau ns w i f children c e,
    nth_error ns i = Some (PApp f children) -> unfolds_pat tau ns i e ->
    represents w c e -> forall j, In j children ->
      exists d t, row_cell w d /\ unfolds_pat tau ns j t /\ represents w d t.
  Proof.
    intros tau ns w i f children c e Hnth Hunfold Hrep j Hin.
    inversion Hunfold as [i' h e' Hnth' Htau | i' v Hnth' |
      i' f' children' args Hnth' Hbefore Hargs]; subst; try congruence.
    assert (f' = f /\ children' = children) as [-> ->] by (split; congruence).
    inversion Hrep as [v | f' cells a b args' Hrow Hsame Hreps]; subst.
    destruct (represented_children tau ns w children args Hargs cells Hreps j Hin)
      as [d [t [Hmember [Hu Hr]]]].
    exists d, t. split.
    - exists f, cells, (Some (Id b)). split; [exact Hrow |].
      apply in_or_app. now left.
    - split; assumption.
  Qed.

  (** The pattern's coverage condition carries root representation to every stored node. *)
  Lemma represented_pattern_nodes : forall sorts kinds g (p : fpat V.t) tau w c e,
    canonical_view w -> pat_ok sorts kinds g p ->
    unfolds_pat tau (nodes V.t p) (root V.t p) e -> represents w (Id c) e ->
    forall j, j < length (nodes V.t p) -> exists d t,
      row_cell w d /\ unfolds_pat tau (nodes V.t p) j t /\ represents w d t.
  Proof.
    intros sorts kinds g [ns r] tau w c e Hcanonical
      [Hlength [Hsort [Hcovered Hnodes]]] Hunfold Hrep.
    cbn [nodes root] in *.
    assert (Hroot : exists d t, row_cell w d /\ unfolds_pat tau ns r t /\ represents w d t).
    { inversion Hrep as [v | f k i b args Hrow Hsame Hargs]; subst.
      exists (Id b), (Model.EApp f args). split.
      - exists f, k, (Some (Id b)). split; [exact Hrow |].
        apply in_or_app. right. now left.
      - split; [exact Hunfold |]. eapply rep_app; [exact Hrow | | exact Hargs].
        exact (proj1 Hcanonical b). }
    assert (Hdown : forall fuel j, r - j <= fuel -> j <= r -> exists d t,
      row_cell w d /\ unfolds_pat tau ns j t /\ represents w d t).
    { induction fuel as [| fuel IH]; intros j Hgap Hj.
      - assert (j = r) by lia. subst j. exact Hroot.
      - destruct (Nat.eq_dec j r) as [-> | Hneq]; [exact Hroot |].
        destruct (Hcovered j ltac:(lia)) as [i [f [children [Hji [Hnth Hin]]]]].
        assert (Hi : i < length ns).
        { apply nth_error_Some. rewrite Hnth. discriminate. }
        destruct (IH i ltac:(lia) ltac:(lia)) as [d [t [Hcell [Hu Hr]]]].
        exact (represented_pattern_child tau ns w i f children d t Hnth Hu Hr j Hin). }
    intros j Hj. apply (Hdown r j); lia.
  Qed.

  (** A canonical row occurrence represents the unfolding of a named pattern node. *)
  Definition represents_node (w : Model.view (V := V.t)) tau ns j c : Prop :=
    row_cell w c /\ exists e, unfolds_pat tau ns j e /\ represents w c e.

  (** Finite pointwise witnesses can be collected without a choice axiom. *)
  Lemma finite_cell_witnesses : forall n (P : nat -> cell V.t -> Prop),
    (forall j, j < n -> exists c, P j c) ->
    exists cs, length cs = n /\ forall j c, nth_error cs j = Some c -> P j c.
  Proof.
    induction n as [| n IH]; intros P Hexists.
    - exists []. split; [reflexivity |]. intros [|j] c Hnth; discriminate.
    - destruct (Hexists 0 ltac:(lia)) as [c Hc].
      destruct (IH (fun j => P (S j)) ltac:(intros j Hj; apply Hexists; lia))
        as [cs [Hlength Hall]].
      exists (c :: cs). split; [cbn [length]; congruence |].
      intros [|j] d Hnth; cbn [nth_error] in Hnth.
      + injection Hnth as <-. exact Hc.
      + exact (Hall j d Hnth).
  Qed.

  (** Every covered pattern has a complete table of represented cells. *)
  Lemma pattern_cell_table : forall sorts kinds g (p : fpat V.t) tau w c e,
    canonical_view w -> pat_ok sorts kinds g p ->
    unfolds_pat tau (nodes V.t p) (root V.t p) e -> represents w (Id c) e ->
    exists cs, length cs = length (nodes V.t p) /\
      forall j d, nth_error cs j = Some d -> represents_node w tau (nodes V.t p) j d.
  Proof.
    intros sorts kinds g p tau w c e Hcanonical Hpat Hunfold Hrep.
    apply finite_cell_witnesses. intros j Hj.
    destruct (represented_pattern_nodes sorts kinds g p tau w c e
      Hcanonical Hpat Hunfold Hrep j Hj) as [d [t [Hcell [Hu Hr]]]].
    exists d. split; [exact Hcell |]. exists t. split; assumption.
  Qed.

  (** A node's canonical representing cell is unique. *)
  Lemma represents_node_unique : forall w tau ns j c d,
    canonical_view w -> represents_node w tau ns j c -> represents_node w tau ns j d ->
    c = d.
  Proof.
    intros w tau ns j c d Hcanonical [Hc [e [Hu Hr]]] [Hd [e' [Hu' Hr']]].
    assert (e = e') by (eapply unfolds_pat_unique; eassumption). subst e'.
    apply (canonical_cell_unique w c d Hcanonical Hc Hd).
    exact (represents_unique w c e Hcanonical Hr d Hr').
  Qed.

  (** Literal nodes are represented by their literal cell. *)
  Lemma represents_node_literal : forall w tau ns j c v,
    nth_error ns j = Some (PLit v) -> represents_node w tau ns j c -> c = Val v.
  Proof.
    intros w tau ns j c v Hnth [_ [e [Hu Hr]]].
    inversion Hu as [i h t Hnth' Htau | i v' Hnth' |
      i f ch args Hnth' Hbefore Hargs]; subst; try congruence.
    assert (v' = v) by congruence. subst v'. inversion Hr. reflexivity.
  Qed.

  (** Hole nodes keep the tree assigned by the supplied substitution. *)
  Lemma represents_node_hole : forall w tau ns j c h,
    nth_error ns j = Some (PHole h) -> represents_node w tau ns j c ->
    exists e, tau h = Some e /\ represents w c e.
  Proof.
    intros w tau ns j c h Hnth [_ [e [Hu Hr]]].
    inversion Hu as [i h' t Hnth' Htau | i v Hnth' |
      i f ch args Hnth' Hbefore Hargs]; subst; try congruence.
    assert (h' = h) by congruence. subst h'. exists e. split; assumption.
  Qed.

  (** A constructor's aligned child lists give represented cells at all child positions. *)
  Lemma represented_children_nodes : forall tau ns w children args,
    Forall2 (@unfolds_pat V.t tau ns) children args ->
    forall cells, Forall (row_cell w) cells -> Forall2 (represents w) cells args ->
      Forall2 (represents_node w tau ns) children cells.
  Proof.
    intros tau ns w children args Hunfold.
    induction Hunfold as [|j e js es Hchild Htail IH]; intros cells Hcells Hrep.
    - inversion Hrep; constructor.
    - inversion Hrep as [|c e' cs es' Hhead Hrest]; subst.
      inversion Hcells as [|c' cs' Hc Hcs]; subst. constructor.
      + split; [exact Hc |]. exists e. split; assumption.
      + exact (IH cs Hcs Hrest).
  Qed.

  (** A constructor node's cell is the output of a row representing all its children. *)
  Lemma represents_node_constructor : forall w tau ns j c f children,
    canonical_view w -> nth_error ns j = Some (PApp f children) ->
    represents_node w tau ns j c ->
    exists cells, row w f cells (Some c) /\
      Forall2 (represents_node w tau ns) children cells.
  Proof.
    intros w tau ns j c f children Hcanonical Hnth [Hc [e [Hu Hr]]].
    inversion Hu as [i h t Hnth' Htau | i v Hnth' |
      i f' ch args Hnth' Hbefore Hargs]; subst; try congruence.
    assert (f' = f /\ ch = children) as [-> ->] by (split; congruence).
    inversion Hr as [v | f' cells a b args' Hrow Hsame Hreps]; subst.
    assert (Hb : row_cell w (Id b)).
    { exists f, cells, (Some (Id b)). split; [exact Hrow |].
      apply in_or_app. right. now left. }
    assert (Hab : @Id V.t a = Id b).
    { eapply canonical_cell_unique; [exact Hcanonical | exact Hc | exact Hb |].
      constructor. exact Hsame. }
    injection Hab as <-. exists cells. split; [exact Hrow |].
    eapply represented_children_nodes; [exact Hargs | | exact Hreps].
    exact (row_key_cells w f cells (Some (Id a)) Hrow).
  Qed.

  (** Compilation preserves holes and literals and names each constructor by a variable. *)
  Definition node_term (n : pnode V.t) (t : term V.t) : Prop :=
    match n with
    | PHole h => t = Var h
    | PLit v => t = Lit v
    | PApp _ _ => exists x, t = Var x
    end.

  (** Constructor names omit the unchanged hole and literal positions. *)
  Fixpoint constructor_names (ns : list (pnode V.t)) (ts : list (term V.t))
      : list positive :=
    match ns, ts with
    | PApp _ _ :: rest, Var x :: tail => x :: constructor_names rest tail
    | _ :: rest, _ :: tail => constructor_names rest tail
    | _, _ => []
    end.

  (** The term table preserves node forms and assigns distinct fresh constructor names. *)
  Lemma pattern_terms_info : forall ns r rn fresh, (rn < fresh)%positive ->
    let '(ts, last) := pattern_terms ns r rn fresh in
    Forall2 node_term ns ts /\ (fresh <= last)%positive /\
    (forall x, In x (constructor_names ns ts) ->
      (x = rn /\ r <> None) \/ (fresh <= x < last)%positive) /\
    NoDup (constructor_names ns ts).
  Proof.
    induction ns as [| n ns IH]; intros r rn fresh Hfresh.
    - cbn [pattern_terms constructor_names]. split; [constructor |].
      split; [lia |]. split; [intros x Hin; contradiction | constructor].
    - destruct n as [h | f children | v].
      + pose proof (IH (next_root r) rn fresh Hfresh) as Htail.
        destruct (pattern_terms ns (next_root r) rn fresh) as [ts last] eqn:Hrun.
        destruct Htail as [Hforms [Hlast [Hrange Hdistinct]]].
        cbn [pattern_terms]. rewrite Hrun. cbn [constructor_names].
        split; [constructor; [reflexivity | exact Hforms] |].
        split; [exact Hlast |]. split; [|exact Hdistinct].
        intros x Hin. destruct (Hrange x Hin) as [[Hx Hr] | Hx]; [left | now right].
        split; [exact Hx |]. intro Heq. subst r. apply Hr. reflexivity.
      + destruct r as [[| r] |].
        * pose proof (IH None rn fresh Hfresh) as Htail.
          destruct (pattern_terms ns None rn fresh) as [ts last] eqn:Hrun.
          destruct Htail as [Hforms [Hlast [Hrange Hdistinct]]].
          cbn [pattern_terms next_root]. rewrite Hrun. cbn [constructor_names].
          split; [constructor; [exists rn; reflexivity | exact Hforms] |].
          split; [exact Hlast |]. split.
          -- intros x [<- | Hin].
             ++ left. split; [reflexivity | discriminate].
             ++ destruct (Hrange x Hin) as [[Hx Hnone] | Hx]; [contradiction | now right].
          -- constructor; [|exact Hdistinct]. intro Hin.
             destruct (Hrange rn Hin) as [[Hx Hnone] | Hx]; [contradiction | lia].
        * pose proof (IH (Some r) rn (Pos.succ fresh) ltac:(lia)) as Htail.
          destruct (pattern_terms ns (Some r) rn (Pos.succ fresh)) as [ts last] eqn:Hrun.
          destruct Htail as [Hforms [Hlast [Hrange Hdistinct]]].
          cbn [pattern_terms next_root]. rewrite Hrun. cbn [constructor_names].
          split; [constructor; [exists fresh; reflexivity | exact Hforms] |].
          split; [lia |]. split.
          -- intros x [<- | Hin]; [right; lia |].
             destruct (Hrange x Hin) as [[Hx Hr] | Hx].
             ++ left. split; [exact Hx | discriminate].
             ++ right. lia.
          -- constructor; [|exact Hdistinct]. intro Hin.
             destruct (Hrange fresh Hin) as [[Hx Hr] | Hx]; lia.
        * pose proof (IH None rn (Pos.succ fresh) ltac:(lia)) as Htail.
          destruct (pattern_terms ns None rn (Pos.succ fresh)) as [ts last] eqn:Hrun.
          destruct Htail as [Hforms [Hlast [Hrange Hdistinct]]].
          cbn [pattern_terms next_root]. rewrite Hrun. cbn [constructor_names].
          split; [constructor; [exists fresh; reflexivity | exact Hforms] |].
          split; [lia |]. split.
          -- intros x [<- | Hin]; [right; lia |].
             destruct (Hrange x Hin) as [[Hx Hr] | Hx]; [contradiction | right; lia].
          -- constructor; [|exact Hdistinct]. intro Hin.
             destruct (Hrange fresh Hin) as [[Hx Hr] | Hx]; [contradiction | lia].
      + pose proof (IH (next_root r) rn fresh Hfresh) as Htail.
        destruct (pattern_terms ns (next_root r) rn fresh) as [ts last] eqn:Hrun.
        destruct Htail as [Hforms [Hlast [Hrange Hdistinct]]].
        cbn [pattern_terms]. rewrite Hrun. cbn [constructor_names].
        split; [constructor; [reflexivity | exact Hforms] |].
        split; [exact Hlast |]. split; [|exact Hdistinct].
        intros x Hin. destruct (Hrange x Hin) as [[Hx Hr] | Hx]; [left | now right].
        split; [exact Hx |]. intro Heq. subst r. apply Hr. reflexivity.
  Qed.

  (** The countdown assigns the selected constructor exactly the requested root name. *)
  Lemma pattern_terms_root : forall (ns : list (pnode V.t)) i f children rn fresh,
    nth_error ns i = Some (PApp f children) ->
    nth_error (fst (pattern_terms ns (Some i) rn fresh)) i = Some (Var rn).
  Proof.
    induction ns as [|n ns IH]; intros [|i] f children rn fresh Hnth;
      cbn [nth_error] in Hnth; try discriminate.
    - injection Hnth as Hn. subst n. cbn [pattern_terms next_root].
      destruct (pattern_terms ns None rn fresh). reflexivity.
    - destruct n as [h|fn ch|v]; cbn [pattern_terms next_root].
      + pose proof (IH i f children rn fresh Hnth) as Hroot.
        destruct (pattern_terms ns (Some i) rn fresh). exact Hroot.
      + pose proof (IH i f children rn (Pos.succ fresh) Hnth) as Hroot.
        destruct (pattern_terms ns (Some i) rn (Pos.succ fresh)). exact Hroot.
      + pose proof (IH i f children rn fresh Hnth) as Hroot.
        destruct (pattern_terms ns (Some i) rn fresh). exact Hroot.
  Qed.

  (** A constructor name at any aligned position occurs in the constructor-name list. *)
  Lemma constructor_name_at : forall ns ts j f children x,
    nth_error ns j = Some (PApp f children) -> nth_error ts j = Some (Var x) ->
    In x (constructor_names ns ts).
  Proof.
    induction ns as [|n ns IH]; intros [|t ts] [|j] f children x Hnode Hterm;
      cbn [nth_error] in Hnode, Hterm; try discriminate.
    - injection Hnode as Hn. subst n. injection Hterm as Ht. subst t. now left.
    - specialize (IH ts j f children x Hnode Hterm).
      destruct n, t; cbn [constructor_names]; try exact IH. now right.
  Qed.

  (** Distinct constructor names distinguish their original positions. *)
  Lemma constructor_names_injective : forall ns ts, NoDup (constructor_names ns ts) ->
    forall i j f children h args x,
      nth_error ns i = Some (PApp f children) -> nth_error ts i = Some (Var x) ->
      nth_error ns j = Some (PApp h args) -> nth_error ts j = Some (Var x) -> i = j.
  Proof.
    induction ns as [|n ns IH]; intros [|t ts] Hdistinct [|i] [|j] f children h args x
      Hni Hti Hnj Htj; cbn [nth_error] in Hni, Hti, Hnj, Htj; try discriminate.
    - reflexivity.
    - injection Hni as Hn. subst n. injection Hti as Ht. subst t.
      inversion Hdistinct as [|x' rest Hfresh Htail]; subst.
      exfalso. apply Hfresh. exact (constructor_name_at ns ts j h args x Hnj Htj).
    - injection Hnj as Hn. subst n. injection Htj as Ht. subst t.
      inversion Hdistinct as [|x' rest Hfresh Htail]; subst.
      exfalso. apply Hfresh. exact (constructor_name_at ns ts i f children x Hni Hti).
    - f_equal. apply (IH ts) with (f := f) (children := children) (h := h)
        (args := args) (x := x); try assumption.
      destruct n, t; cbn [constructor_names] in Hdistinct; try exact Hdistinct.
      inversion Hdistinct. assumption.
  Qed.

  (** Aligned form preservation applies at every common list position. *)
  Lemma node_term_at : forall ns ts, Forall2 node_term ns ts -> forall i n t,
    nth_error ns i = Some n -> nth_error ts i = Some t -> node_term n t.
  Proof.
    intros ns ts Hforms. induction Hforms as [|n t ns ts Hhead Htail IH];
      intros [|i] n' t' Hn Ht; cbn [nth_error] in Hn, Ht; try discriminate.
    - injection Hn as <-. injection Ht as <-. exact Hhead.
    - exact (IH i n' t' Hn Ht).
  Qed.

  (** The maximum helper bounds each of its inputs. *)
  Lemma name_max_bounds : forall x y,
    (x <= name_max x y /\ y <= name_max x y)%positive.
  Proof.
    intros x y. unfold name_max. destruct (Pos.compare x y) eqn:Hcompare.
    - apply Pos.compare_eq_iff in Hcompare. subst y. split; apply Pos.le_refl.
    - apply Pos.compare_lt_iff in Hcompare. split.
      + apply Pos.lt_le_incl. exact Hcompare.
      + apply Pos.le_refl.
    - apply Pos.compare_gt_iff in Hcompare. split.
      + apply Pos.le_refl.
      + apply Pos.lt_le_incl. exact Hcompare.
  Qed.

  (** Every hole is bounded by the pattern's computed maximum name. *)
  Lemma pattern_max_hole : forall (ns : list (pnode V.t)) h,
    In (PHole h) ns -> (h <= pattern_max ns)%positive.
  Proof.
    induction ns as [|n ns IH]; intros h Hin; [contradiction |].
    destruct Hin as [Heq | Hin].
    - subst n. cbn [pattern_max]. apply name_max_bounds.
    - specialize (IH h Hin). destruct n as [hole_name|f children|v];
        cbn [pattern_max]; try exact IH.
      pose proof (proj2 (name_max_bounds hole_name (pattern_max ns))). lia.
  Qed.

  (** A fold of name maxima bounds every variable term that it reads. *)
  Lemma terms_name_max : forall (ts : list (term V.t)) seed x, In (Var x) ts ->
    (x <= fold_right (fun t m => name_max (term_name t) m) seed ts)%positive.
  Proof.
    induction ts as [|t ts IH]; intros seed x Hin; [contradiction |].
    cbn [fold_right]. destruct Hin as [Heq | Hin].
    - subst t. apply name_max_bounds.
    - specialize (IH seed x Hin).
      pose proof (proj2 (name_max_bounds (term_name t)
        (fold_right (fun t m => name_max (term_name t) m) seed ts))). lia.
  Qed.

  (** A fold of name maxima also bounds its starting value. *)
  Lemma terms_name_seed : forall (ts : list (term V.t)) seed,
    (seed <= fold_right (fun t m => name_max (term_name t) m) seed ts)%positive.
  Proof.
    induction ts as [|t ts IH]; intro seed; cbn [fold_right]; [lia |].
    specialize (IH seed).
    pose proof (proj2 (name_max_bounds (term_name t)
      (fold_right (fun t m => name_max (term_name t) m) seed ts))). lia.
  Qed.

  (** Query atoms mention the terms in their arguments and optional result. *)
  Definition atom_terms (a : atom V.t) : list (term V.t) :=
    match a with
    | Fun _ _ args res => args ++ option_list res
    | Prim _ _ args res => args ++ [res]
    end.

  (** An atom's maximum name bounds every variable that the atom mentions. *)
  Lemma atom_name_bound : forall a x, In (Var x) (atom_terms a) ->
    (x <= atom_name_max a)%positive.
  Proof.
    intros [f args res | p args res] x Hin; cbn [atom_terms atom_name_max] in *.
    - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + now apply terms_name_max.
      + destruct res as [t |]; cbn [option_list] in Hin; [| contradiction].
        destruct Hin as [Heq | Hfalse]; [subst t | contradiction].
        apply terms_name_seed.
    - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      + now apply terms_name_max.
      + destruct Hin as [Heq | Hfalse]; [subst res | contradiction].
        apply terms_name_seed.
  Qed.

  (** The condition maximum bounds each atom in the condition. *)
  Lemma condition_name_bound : forall (q : list (atom V.t)) a, In a q ->
    (atom_name_max a <=
      fold_right (fun a m => name_max (atom_name_max a) m) 1%positive q)%positive.
  Proof.
    induction q as [|head q IH]; intros a Hin; [contradiction |].
    cbn [fold_right]. destruct Hin as [Heq | Hin].
    - subst head. apply name_max_bounds.
    - eapply Pos.le_trans; [exact (IH a Hin) |]. apply name_max_bounds.
  Qed.

  (** The chosen root name is above both pattern maxima and every condition variable. *)
  Lemma root_var_bounds : forall rw,
    (pattern_max (nodes V.t (lhs V.t rw)) < root_var rw)%positive /\
    (pattern_max (nodes V.t (rhs V.t rw)) < root_var rw)%positive /\
    forall a x, In a (cond V.t rw) -> In (Var x) (atom_terms a) ->
      (x < root_var rw)%positive.
  Proof.
    intros [[ln lr] [rn rr] conditions]. cbn [root_var nodes lhs rhs cond].
    pose proof (name_max_bounds (pattern_max ln)
      (name_max (pattern_max rn)
        (fold_right (fun a m => name_max (atom_name_max a) m) 1%positive conditions)))
      as [Hleft Hrest].
    pose proof (name_max_bounds (pattern_max rn)
      (fold_right (fun a m => name_max (atom_name_max a) m) 1%positive conditions))
      as [Hright Hconditions].
    split; [lia |]. split; [lia |]. intros a x Hin Hterm.
    pose proof (condition_name_bound conditions a Hin) as Hatom.
    pose proof (atom_name_bound a x Hterm) as Hname. lia.
  Qed.

  (** Original left-side holes are strictly below every fresh constructor name. *)
  Lemma root_var_hole : forall rw h, In (PHole h) (nodes V.t (lhs V.t rw)) ->
    (h < root_var rw)%positive.
  Proof.
    intros rw h Hin. pose proof (pattern_max_hole _ h Hin) as Hhole.
    pose proof (proj1 (root_var_bounds rw)) as Hroot. lia.
  Qed.

  (** * Compiler table environments *)

  (** A table environment uses the first variable occurrence and retains other bindings. *)
  Fixpoint table_bind {A} (ts : list (term V.t)) (values : list A)
      (base : positive -> option A) : positive -> option A :=
    match ts, values with
    | Var h :: rest, value :: tail => fun x =>
        if Pos.eqb h x then Some value else table_bind rest tail base x
    | Lit _ :: rest, _ :: tail => table_bind rest tail base
    | _, _ => base
    end.

  (** Repeated variable terms have the same payload at every aligned table position. *)
  Definition table_compatible {A} (ts : list (term V.t)) (values : list A) : Prop :=
    forall i j x v w, nth_error ts i = Some (Var x) -> nth_error values i = Some v ->
      nth_error ts j = Some (Var x) -> nth_error values j = Some w -> v = w.

  (** Compatibility of an aligned table is inherited by its tail. *)
  Lemma table_compatible_tail : forall A t (value : A) ts values,
    table_compatible (t :: ts) (value :: values) -> table_compatible ts values.
  Proof.
    intros A t value ts values Hcompatible i j x v w Hti Hvi Htj Hvj.
    exact (Hcompatible (S i) (S j) x v w Hti Hvi Htj Hvj).
  Qed.

  (** Every compatible variable entry has its assigned payload in the table environment. *)
  Lemma table_bind_at : forall A ts (values : list A) base,
    table_compatible ts values -> forall i x value,
      nth_error ts i = Some (Var x) -> nth_error values i = Some value ->
      table_bind ts values base x = Some value.
  Proof.
    intros A ts. induction ts as [|t ts IH]; intros [|v values] base Hcompatible
      [|i] x value Hterm Hvalue; cbn [nth_error] in Hterm, Hvalue; try discriminate.
    - injection Hterm as Ht. subst t. injection Hvalue as Hv. subst v.
      cbn [table_bind]. now rewrite Pos.eqb_refl.
    - pose proof (table_compatible_tail A t v ts values Hcompatible) as Htail.
      destruct t as [h|literal]; cbn [table_bind].
      + destruct (Pos.eqb h x) eqn:Heq.
        * apply Pos.eqb_eq in Heq. subst h. f_equal.
          exact (Hcompatible 0 (S i) x v value eq_refl eq_refl Hterm Hvalue).
        * exact (IH values base Htail i x value Hterm Hvalue).
      + exact (IH values base Htail i x value Hterm Hvalue).
  Qed.

  (** A table preserves any base binding with which all of its matching entries agree. *)
  Lemma table_bind_agrees : forall A ts (values : list A) base x,
    (forall i value, nth_error ts i = Some (Var x) -> nth_error values i = Some value ->
      base x = Some value) -> table_bind ts values base x = base x.
  Proof.
    intros A ts. induction ts as [|t ts IH]; intros [|v values] base x Hagree;
      try reflexivity; [destruct t; reflexivity |].
    assert (Htail : forall i value, nth_error ts i = Some (Var x) ->
      nth_error values i = Some value -> base x = Some value).
    { intros i value Ht Hv. exact (Hagree (S i) value Ht Hv). }
    destruct t as [h|literal]; cbn [table_bind].
    - destruct (Pos.eqb h x) eqn:Heq.
      + apply Pos.eqb_eq in Heq. subst h. symmetry. exact (Hagree 0 v eq_refl eq_refl).
      + exact (IH values base x Htail).
    - exact (IH values base x Htail).
  Qed.

  (** A table lookup either preserves the base or comes from an aligned variable entry. *)
  Lemma table_bind_case : forall A ts (values : list A) base x,
    table_bind ts values base x = base x \/ exists i value,
      nth_error ts i = Some (Var x) /\ nth_error values i = Some value /\
        table_bind ts values base x = Some value.
  Proof.
    intros A ts. induction ts as [|t ts IH]; intros [|v values] base x;
      try (left; reflexivity); [destruct t; left; reflexivity |].
    destruct t as [h|literal]; cbn [table_bind].
    - destruct (Pos.eqb h x) eqn:Heq.
      + apply Pos.eqb_eq in Heq. subst h. right. exists 0, v. repeat split; reflexivity.
      + destruct (IH values base x) as [Hbase | [i [value [Ht [Hv Hlookup]]]]].
        * now left.
        * right. exists (S i), value. split; [exact Ht |]. split; assumption.
    - destruct (IH values base x) as [Hbase | [i [value [Ht [Hv Hlookup]]]]].
      + now left.
      + right. exists (S i), value. split; [exact Ht |]. split; assumption.
  Qed.

  (** Equal-length lists are related when their entries are related at each common index. *)
  Lemma forall2_at_indices : forall A B (R : A -> B -> Prop) xs ys,
    length xs = length ys ->
    (forall i x y, nth_error xs i = Some x -> nth_error ys i = Some y -> R x y) ->
    Forall2 R xs ys.
  Proof.
    intros A B R xs. induction xs as [|x xs IH]; intros [|y ys] Hlength Hall;
      cbn [length] in Hlength; try discriminate.
    - constructor.
    - constructor; [exact (Hall 0 x y eq_refl eq_refl) |].
      apply IH; [lia |]. intros i a b Ha Hb. exact (Hall (S i) a b Ha Hb).
  Qed.

  (** The table environment realizes its whole term list when literals also agree. *)
  Lemma table_bind_values : forall ts cells base,
    length ts = length cells -> table_compatible ts cells ->
    (forall i v c, nth_error ts i = Some (Lit v) -> nth_error cells i = Some c -> c = Val v) ->
    terms_value (table_bind ts cells base) ts cells.
  Proof.
    intros ts cells base Hlength Hcompatible Hliterals.
    apply forall2_at_indices; [exact Hlength |]. intros i [x|v] c Hterm Hcell.
    - exact (table_bind_at _ ts cells base Hcompatible i x c Hterm Hcell).
    - exact (Hliterals i v c Hterm Hcell).
  Qed.


  (** The table wrapper preserves forms, distinct constructor names and the fresh lower bound. *)
  Lemma pattern_table_facts : forall (p : fpat V.t) rn,
    Forall2 node_term (nodes V.t p) (fst (pattern_table p rn)) /\
    NoDup (constructor_names (nodes V.t p) (fst (pattern_table p rn))) /\
    forall i f children x, nth_error (nodes V.t p) i = Some (PApp f children) ->
      nth_error (fst (pattern_table p rn)) i = Some (Var x) -> (rn <= x)%positive.
  Proof.
    intros [ns r] rn. cbn [pattern_table nodes].
    pose proof (pattern_terms_info ns (Some r) rn (Pos.succ rn) ltac:(lia)) as Hinfo.
    destruct (pattern_terms ns (Some r) rn (Pos.succ rn)) as [ts last] eqn:Hrun.
    cbn [fst]. destruct Hinfo as [Hforms [Hlast [Hrange Hdistinct]]].
    split; [exact Hforms |]. split; [exact Hdistinct |].
    intros i f children x Hnode Hterm.
    pose proof (Hrange x (constructor_name_at ns ts i f children x Hnode Hterm)) as Hname.
    destruct Hname as [[-> Hr] | Hbounds]; lia.
  Qed.

  (** A preserved term position identifies its corresponding pattern node. *)
  Lemma node_term_lookup : forall ns ts, Forall2 node_term ns ts -> forall i t,
    nth_error ts i = Some t -> exists n, nth_error ns i = Some n /\ node_term n t.
  Proof.
    intros ns ts Hforms. induction Hforms as [|n t ns ts Hhead Htail IH];
      intros [|i] t' Hterm; cbn [nth_error] in Hterm; try discriminate.
    - injection Hterm as <-. exists n. split; [reflexivity | exact Hhead].
    - exact (IH i t' Hterm).
  Qed.

  (** Variables below the fresh range can only come from original hole nodes. *)
  Lemma pattern_table_small_var : forall (p : fpat V.t) rn i x,
    (x < rn)%positive -> nth_error (fst (pattern_table p rn)) i = Some (Var x) ->
    nth_error (nodes V.t p) i = Some (PHole x).
  Proof.
    intros p rn i x Hsmall Hterm.
    destruct (pattern_table_facts p rn) as [Hforms [Hdistinct Hrange]].
    destruct (node_term_lookup _ _ Hforms i (Var x) Hterm) as [n [Hnode Hform]].
    destruct n as [h|f children|v]; cbn [node_term] in Hform.
    - injection Hform as Heq. subst h. exact Hnode.
    - pose proof (Hrange i f children x Hnode Hterm). lia.
    - discriminate.
  Qed.

  (** Literal terms in a represented table carry exactly their literal cells. *)
  Lemma pattern_table_literals : forall (p : fpat V.t) rn w tau cs,
    (forall i c, nth_error cs i = Some c -> represents_node w tau (nodes V.t p) i c) ->
    forall i v c, nth_error (fst (pattern_table p rn)) i = Some (Lit v) ->
      nth_error cs i = Some c -> c = Val v.
  Proof.
    intros p rn w tau cs Hcells i v c Hterm Hcell.
    destruct (node_term_lookup _ _ (proj1 (pattern_table_facts p rn)) i (Lit v) Hterm)
      as [n [Hnode Hform]].
    destruct n as [h|f children|literal]; cbn [node_term] in Hform; try discriminate.
    - destruct Hform as [x Hbad]. discriminate.
    - injection Hform as Heq. subst literal.
      exact (represents_node_literal w tau _ i c v Hnode (Hcells i c Hcell)).
  Qed.

  (** Repeated terms in a fresh pattern table have the same canonical representing cells. *)
  Lemma pattern_table_compatible : forall (p : fpat V.t) rn w tau cs,
    canonical_view w ->
    (forall h, In (PHole h) (nodes V.t p) -> (h < rn)%positive) ->
    (forall i c, nth_error cs i = Some c -> represents_node w tau (nodes V.t p) i c) ->
    table_compatible (fst (pattern_table p rn)) cs.
  Proof.
    intros p rn w tau cs Hcanonical Hholes Hcells.
    destruct (pattern_table_facts p rn) as [Hforms [Hdistinct Hrange]].
    intros i j x c d Hti Hci Htj Hdj.
    destruct (node_term_lookup _ _ Hforms i (Var x) Hti) as [ni [Hni Hfi]].
    destruct (node_term_lookup _ _ Hforms j (Var x) Htj) as [nj [Hnj Hfj]].
    destruct ni as [hi|fi chi|vi]; destruct nj as [hj|fj chj|vj];
      cbn [node_term] in Hfi, Hfj; try discriminate.
    - injection Hfi as Heqi. subst hi. injection Hfj as Heqj. subst hj.
      pose proof (Hcells i c Hci) as Hc. pose proof (Hcells j d Hdj) as Hd.
      destruct (represents_node_hole w tau _ i c x Hni Hc) as [e [Htau Hr]].
      destruct (represents_node_hole w tau _ j d x Hnj Hd) as [e' [Htau' Hr']].
      assert (e = e') by congruence. subst e'.
      apply (canonical_cell_unique w c d Hcanonical (proj1 Hc) (proj1 Hd)).
      exact (represents_unique w c e Hcanonical Hr d Hr').
    - injection Hfi as Heqi. subst hi.
      pose proof (Hholes x (nth_error_In _ i Hni)) as Hsmall.
      pose proof (Hrange j fj chj x Hnj Htj). lia.
    - injection Hfj as Heqj. subst hj.
      pose proof (Hholes x (nth_error_In _ j Hnj)) as Hsmall.
      pose proof (Hrange i fi chi x Hni Hti). lia.
    - assert (i = j).
      { eapply constructor_names_injective; eassumption. }
      subst j. congruence.
  Qed.

  (** A represented node has an actual position in the pattern list. *)
  Lemma represents_node_index : forall w tau ns j c,
    represents_node w tau ns j c -> j < length ns.
  Proof.
    intros w tau ns j c [_ [e [Hu Hr]]].
    destruct Hu as [i h t Hnth Htau|i v Hnth|i f children args Hnth Hbefore Hargs];
      apply nth_error_Some; rewrite Hnth; discriminate.
  Qed.

  (** Reading an aligned term table gives the value at the corresponding cell position. *)
  Lemma pattern_get_value : forall s ts cs, @terms_value V.t s ts cs ->
    forall default j c, nth_error cs j = Some c ->
      term_value s (pattern_get default j ts) c.
  Proof.
    intros s ts cs Hvalues.
    induction Hvalues as [|t d ts cs Hhead Htail IH]; intros default [|j] c Hcell;
      cbn [nth_error] in Hcell; try discriminate.
    - injection Hcell as <-. exact Hhead.
    - exact (IH default j c Hcell).
  Qed.

  (** A constructor's represented children agree with the cells selected by its term indices. *)
  Lemma pattern_children_values : forall w tau ns cs ts s children cells,
    canonical_view w -> length cs = length ns -> terms_value s ts cs ->
    (forall j c, nth_error cs j = Some c -> represents_node w tau ns j c) ->
    Forall2 (represents_node w tau ns) children cells ->
    terms_value s (map (fun j => pattern_get (Var 1%positive) j ts) children) cells.
  Proof.
    intros w tau ns cs ts s children cells Hcanonical Hlength Hvalues Hall Hchildren.
    induction Hchildren as [|j d js ds Hnode Htail IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH].
      assert (Hindex : j < length cs).
      { rewrite Hlength. exact (represents_node_index w tau ns j d Hnode). }
      destruct (nth_error cs j) as [c|] eqn:Hcell.
      + assert (c = d).
        { exact (represents_node_unique w tau ns j c d Hcanonical (Hall j c Hcell) Hnode). }
        subst c. exact (pattern_get_value s ts cs Hvalues (Var 1%positive) j d Hcell).
      + apply nth_error_None in Hcell. lia.
  Qed.

  (** Every constructor atom in the flat table is witnessed by its represented row. *)
  Lemma pattern_atom_holds : forall (p : fpat V.t) rn w tau cs s,
    canonical_view w -> length cs = length (nodes V.t p) ->
    terms_value s (fst (pattern_table p rn)) cs ->
    (forall j c, nth_error cs j = Some c -> represents_node w tau (nodes V.t p) j c) ->
    forall i f children t, nth_error (nodes V.t p) i = Some (PApp f children) ->
      nth_error (fst (pattern_table p rn)) i = Some t ->
      atom_holds V.prim w s (Fun V.t f
        (map (fun j => pattern_get (Var 1%positive) j (fst (pattern_table p rn))) children)
        (Some t)).
  Proof.
    intros p rn w tau cs s Hcanonical Hlength Hvalues Hall i f children t Hnode Hterm.
    assert (Hindex : i < length cs).
    { rewrite Hlength. apply nth_error_Some. rewrite Hnode. discriminate. }
    destruct (nth_error cs i) as [c|] eqn:Hcell; [|apply nth_error_None in Hcell; lia].
    destruct (represents_node_constructor w tau _ i c f children Hcanonical Hnode
      (Hall i c Hcell)) as [cells [Hrow Hchildren]].
    exists cells, (Some c). split.
    - exact (pattern_children_values w tau _ cs _ s children cells Hcanonical Hlength
        Hvalues Hall Hchildren).
    - split; [|exact Hrow].
      pose proof (pattern_get_value s _ cs Hvalues (Var 1%positive) i c Hcell) as Hvalue.
      unfold pattern_get in Hvalue. now rewrite Hterm in Hvalue.
  Qed.

  (** Pointwise constructor witnesses assemble into a match of the complete atom list. *)
  Lemma pattern_atoms_match : forall ns ts all w s,
    (forall i f children t, nth_error ns i = Some (PApp f children) ->
      nth_error ts i = Some t -> atom_holds V.prim w s
        (Fun V.t f (map (fun j => pattern_get (Var 1%positive) j all) children) (Some t))) ->
    matches V.prim w (pattern_atoms ns ts all) s.
  Proof.
    induction ns as [|n ns IH]; intros [|t ts] all w s Hnodes; try constructor.
    assert (Htail : forall i f children u, nth_error ns i = Some (PApp f children) ->
      nth_error ts i = Some u -> atom_holds V.prim w s
        (Fun V.t f (map (fun j => pattern_get (Var 1%positive) j all) children) (Some u))).
    { intros i f children u Hn Ht. exact (Hnodes (S i) f children u Hn Ht). }
    destruct n as [h|f children|v]; cbn [pattern_atoms].
    - exact (IH ts all w s Htail).
    - constructor; [exact (Hnodes 0 f children t eq_refl eq_refl) |].
      exact (IH ts all w s Htail).
    - exact (IH ts all w s Htail).
  Qed.

  (** A queried variable has a value among the corresponding argument cells. *)
  Lemma terms_value_occurs : forall s ts cs, @terms_value V.t s ts cs ->
    forall x, In (Var x) ts -> exists c, In c cs /\ s x = Some c.
  Proof.
    intros s ts cs Hvalues. induction Hvalues as [|t c ts cs Hhead Htail IH];
      intros x Hin; cbn in Hin; [contradiction |].
    destruct Hin as [Ht | Hin].
    - subst t. exists c. split; [now left | exact Hhead].
    - destruct (IH x Hin) as [d [Hd Hvalue]]. exists d. split; [now right | exact Hvalue].
  Qed.

  (** A primitive argument cell is a literal value. *)
  Lemma values_cells : forall cs vs, @values V.t cs vs ->
    forall c, In c cs -> exists v, c = Val v.
  Proof.
    intros cs vs Hvalues. induction Hvalues as [|d v cs vs Hhead Htail IH];
      intros c Hin; cbn in Hin; [contradiction |].
    destruct Hin as [<- | Hin]; [now exists v | exact (IH c Hin)].
  Qed.

  (** A variable used by a matching atom denotes a row cell or a literal. *)
  Lemma atom_bound_canonical : forall w s a x c,
    atom_holds V.prim w s a -> In (Var x) (atom_terms a) -> s x = Some c ->
    row_cell w c \/ exists v, c = Val v.
  Proof.
    intros w s [f args res | p args res] x c Hatom Hin Hvalue;
      cbn [atom_terms] in Hin.
    - destruct Hatom as [k [o [Hargs [Hres Hrow]]]]. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + destruct (terms_value_occurs s args k Hargs x Hin) as [d [Hd Hlookup]].
        rewrite Hvalue in Hlookup. injection Hlookup as <-. left.
        exists f, k, o. split; [exact Hrow | apply in_or_app; now left].
      + destruct res as [t|]; cbn in Hin; [|contradiction].
        destruct Hin as [Ht | Hin]; [subst t |contradiction].
        destruct o as [d|]; [|contradiction]. cbn [term_value] in Hres.
        rewrite Hvalue in Hres. injection Hres as <-. left.
        exists f, k, (Some c). split; [exact Hrow |]. apply in_or_app. right. now left.
    - destruct Hatom as [k [vs [v [Hargs [Hvals [Hprim Hres]]]]]].
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + destruct (terms_value_occurs s args k Hargs x Hin) as [d [Hd Hlookup]].
        rewrite Hvalue in Hlookup. injection Hlookup as <-. right.
        exact (values_cells k vs Hvals c Hd).
      + cbn in Hin. destruct Hin as [Ht | Hin]; [subst res |contradiction].
        cbn [term_value] in Hres. rewrite Hvalue in Hres. injection Hres as Hc.
        right. exists v. exact Hc.
  Qed.

  (** A canonical row representative agrees exactly with any represented atom value. *)
  Lemma represented_occurrence_unique : forall w c d e,
    canonical_view w -> row_cell w c -> (row_cell w d \/ exists v, d = Val v) ->
    represents w c e -> represents w d e -> c = d.
  Proof.
    intros w c d e Hcanonical Hc Hd Hrep Hrep'.
    pose proof (represents_unique w c e Hcanonical Hrep d Hrep') as Hrel.
    destruct Hd as [Hd | [v ->]].
    - exact (canonical_cell_unique w c d Hcanonical Hc Hd Hrel).
    - inversion Hrel. reflexivity.
  Qed.

  (** Argument values are preserved by environments agreeing on their mentioned variables. *)
  Lemma terms_value_agrees : forall s s' ts cs,
    (forall x, In (Var x) ts -> s' x = s x) ->
    @terms_value V.t s ts cs -> terms_value s' ts cs.
  Proof.
    intros s s' ts cs Hagree Hvalues. revert Hagree.
    induction Hvalues as [|t c ts cs Hhead Htail IH]; intros Hagree; [constructor |].
    constructor.
    - destruct t as [x|v]; cbn [term_value] in *; [|exact Hhead].
      rewrite Hagree; [exact Hhead | now left].
    - apply IH. intros x Hin. apply Hagree. now right.
  Qed.

  (** An atom match depends only on the variable names occurring in that atom. *)
  Lemma atom_holds_agrees : forall w s s' a,
    (forall x, In (Var x) (atom_terms a) -> s' x = s x) ->
    atom_holds V.prim w s a -> atom_holds V.prim w s' a.
  Proof.
    intros w s s' [f args res|p args res] Hagree Hatom;
      cbn [atom_terms] in Hagree.
    - destruct Hatom as [k [o [Hargs [Hres Hrow]]]]. exists k, o. split.
      + apply (terms_value_agrees s s' args k); [|exact Hargs].
        intros x Hin. apply Hagree. apply in_or_app. now left.
      + split; [|exact Hrow]. destruct res as [t|], o as [c|]; try contradiction;
          [|exact I]. destruct t as [x|v]; cbn [term_value] in *; [|exact Hres].
        rewrite Hagree; [exact Hres |]. apply in_or_app. right. now left.
    - destruct Hatom as [k [vs [v [Hargs [Hvals [Hprim Hres]]]]]].
      exists k, vs, v. split.
      + apply (terms_value_agrees s s' args k); [|exact Hargs].
        intros x Hin. apply Hagree. apply in_or_app. now left.
      + split; [exact Hvals |]. split; [exact Hprim |].
        destruct res as [x|u]; cbn [term_value] in *; [|exact Hres].
        rewrite Hagree; [exact Hres |]. apply in_or_app. right. now left.
  Qed.

  (** Binding represented pattern nodes preserves an already matching source atom. *)
  Lemma pattern_atom_agrees : forall (p : fpat V.t) rn w tau cs s a,
    canonical_view w -> represents_subst w tau s -> atom_holds V.prim w s a ->
    (forall i c, nth_error cs i = Some c -> represents_node w tau (nodes V.t p) i c) ->
    (forall x, In (Var x) (atom_terms a) -> (x < rn)%positive) ->
    forall x, In (Var x) (atom_terms a) ->
      table_bind (fst (pattern_table p rn)) cs s x = s x.
  Proof.
    intros p rn w tau cs s a Hcanonical Hsubst Hatom Hall Hsmall x Hvar.
    apply table_bind_agrees. intros i c Hterm Hcell.
    pose proof (pattern_table_small_var p rn i x (Hsmall x Hvar) Hterm) as Hhole.
    destruct (represents_node_hole w tau _ i c x Hhole (Hall i c Hcell))
      as [e [Htau Hrep]].
    destruct (Hsubst x e Htau) as [d [Hlookup Hrep']].
    assert (c = d).
    { exact (represented_occurrence_unique w c d e Hcanonical
        (proj1 (Hall i c Hcell))
        (atom_bound_canonical w s a x d Hatom Hvar Hlookup) Hrep Hrep'). }
    now subst d.
  Qed.

  (** The represented table preserves each well-scoped substitution binding. *)
  Lemma pattern_bind_represents : forall (p : fpat V.t) rn w tau cs s g,
    represents_subst w tau s ->
    (forall i c, nth_error cs i = Some c -> represents_node w tau (nodes V.t p) i c) ->
    (forall h t, g h = Some t -> (h < rn)%positive) ->
    represents_on g w tau (table_bind (fst (pattern_table p rn)) cs s).
  Proof.
    intros p rn w tau cs s g Hsubst Hall Hsmall h t e Hsort Htau.
    destruct (table_bind_case _ (fst (pattern_table p rn)) cs s h)
      as [Hbase | [i [c [Hterm [Hcell Hlookup]]]]].
    - destruct (Hsubst h e Htau) as [c [Hlookup Hrep]]. exists c.
      split; [now rewrite Hbase | exact Hrep].
    - exists c. split; [exact Hlookup |].
      pose proof (pattern_table_small_var p rn i h (Hsmall h t Hsort) Hterm) as Hhole.
      destruct (represents_node_hole w tau _ i c h Hhole (Hall i c Hcell))
        as [e' [Htau' Hrep]]. assert (e = e') by congruence. now subst e'.
  Qed.

  (** A constructor node can only be represented by an identifier cell. *)
  Lemma represents_node_app_id : forall w tau ns i c f children,
    nth_error ns i = Some (PApp f children) -> represents_node w tau ns i c ->
    exists j, c = Id j.
  Proof.
    intros w tau ns i c f children Hnode [_ [e [Hunfold Hrep]]].
    inversion Hunfold as [j h t Hnth Htau|j v Hnth|j g ch args Hnth Hbefore Hargs];
      subst; try congruence.
    inversion Hrep. now eexists.
  Qed.

  (** The represented cell table supplies a canonical row at the constructor root. *)
  Lemma pattern_root_row : forall (p : fpat V.t) w tau cs c e,
    canonical_view w -> app_rooted p ->
    unfolds_pat tau (nodes V.t p) (root V.t p) e -> represents w (Id c) e ->
    length cs = length (nodes V.t p) ->
    (forall i d, nth_error cs i = Some d -> represents_node w tau (nodes V.t p) i d) ->
    exists j, nth_error cs (root V.t p) = Some (Id j) /\ same w c j /\
      exists f k, row w f k (Some (Id j)).
  Proof.
    intros p w tau cs c e Hcanonical [f [children Hroot]] Hunfold Hrep Hlength Hall.
    assert (Hindex : root V.t p < length cs).
    { rewrite Hlength. apply nth_error_Some. rewrite Hroot. discriminate. }
    destruct (nth_error cs (root V.t p)) as [d|] eqn:Hcell;
      [|apply nth_error_None in Hcell; lia].
    destruct (represents_node_app_id w tau _ _ d f children Hroot
      (Hall _ d Hcell)) as [j ->]. exists j. split; [reflexivity |].
    split.
    - destruct (Hall _ (Id j) Hcell) as [Hrow [e' [Hunfold' Hrep']]].
      assert (e = e') by (eapply unfolds_pat_unique; eassumption). subst e'.
      pose proof (represents_unique w (Id c) e Hcanonical Hrep (Id j) Hrep') as Hrel.
      now inversion Hrel.
    - destruct (represents_node_constructor w tau _ _ (Id j) f children Hcanonical Hroot
        (Hall _ (Id j) Hcell)) as [cells [Hrow Hchildren]]. now exists f, cells.
  Qed.

  (** The root constructor uses the reserved table name. *)
  Lemma pattern_table_root : forall (p : fpat V.t) rn,
    app_rooted p -> nth_error (fst (pattern_table p rn)) (root V.t p) = Some (Var rn).
  Proof.
    intros [ns r] rn [f [children Hroot]]. cbn [nodes root] in Hroot.
    cbn [pattern_table root]. apply (pattern_terms_root ns r f children rn (Pos.succ rn)).
    exact Hroot.
  Qed.

  (** A term has a unique value in a fixed environment. *)
  Lemma term_value_unique : forall s (t : term V.t) c d,
    term_value s t c -> term_value s t d -> c = d.
  Proof.
    intros s [x|v] c d Hc Hd; cbn [term_value] in *; congruence.
  Qed.

  (** Updating a different variable preserves a term's value. *)
  Lemma term_value_update_other : forall s x d (t : term V.t) c,
    t <> Var x -> term_value s t c -> term_value (update s x d) t c.
  Proof.
    intros s x d [y|v] c Hdifferent Hvalue; cbn [term_value] in *; [|exact Hvalue].
    unfold update. destruct (Pos.eqb x y) eqn:Hxy; [|exact Hvalue].
    apply Pos.eqb_eq in Hxy. subst y. contradiction.
  Qed.

  (** The assigned variable takes the newly inserted cell. *)
  Lemma term_value_update_same : forall s x c,
    @term_value V.t (update s x c) (Var x) c.
  Proof.
    intros s x c. unfold term_value, update. now rewrite Pos.eqb_refl.
  Qed.

  (** Every generated constructor variable belongs to exactly one table position. *)
  Lemma pattern_constructor_name_unique : forall (p : fpat V.t) rn i f children x j,
    (forall h, In (PHole h) (nodes V.t p) -> (h < rn)%positive) ->
    nth_error (nodes V.t p) i = Some (PApp f children) ->
    nth_error (fst (pattern_table p rn)) i = Some (Var x) ->
    nth_error (fst (pattern_table p rn)) j = Some (Var x) -> i = j.
  Proof.
    intros p rn i f children x j Hholes Hnode Hterm Hother.
    destruct (pattern_table_facts p rn) as [Hforms [Hdistinct Hrange]].
    pose proof (Hrange i f children x Hnode Hterm) as Hfresh.
    destruct (node_term_lookup _ _ Hforms j (Var x) Hother) as [n [Hnth Hform]].
    destruct n as [h|g ch|v]; cbn [node_term] in Hform.
    - injection Hform as Heq. subst h.
      pose proof (Hholes x (nth_error_In _ _ Hnth)). lia.
    - exact (constructor_names_injective _ _ Hdistinct i j f children g ch x
        Hnode Hterm Hnth Hother).
    - discriminate.
  Qed.

  (** Related child unfoldings and their current table values give represented row keys. *)
  Lemma pattern_arguments_represent : forall w tau ns ts s children args cells,
    Forall2 (@unfolds_pat V.t tau ns) children args ->
    terms_value s (map (fun j => pattern_get (Var 1%positive) j ts) children) cells ->
    (forall j e, In j children -> unfolds_pat tau ns j e ->
      exists c, term_value s (pattern_get (Var 1%positive) j ts) c /\ represents w c e) ->
    Forall2 (represents w) cells args.
  Proof.
    intros w tau ns ts s children args cells Hunfold. revert cells.
    induction Hunfold as [|j e children args Hhead Htail IH];
      intros cells Hvalues Hready; inversion Hvalues as [|t c terms rest Hvalue Hrest];
      subst; [constructor|].
    constructor.
    - destruct (Hready j e (or_introl eq_refl) Hhead) as [d [Hd Hrep]].
      assert (c = d) by (eapply term_value_unique; eassumption). now subst c.
    - apply IH; [exact Hrest |]. intros k r Hin Hr. apply Hready; [now right |exact Hr].
  Qed.


  (** * Sorting compiled patterns *)

  (** A context includes another when it preserves every existing sort assignment. *)
  Definition ctx_includes (g h : ctx) : Prop :=
    forall x s, g x = Some s -> h x = Some s.

  (** Every context includes itself. *)
  Lemma ctx_includes_refl : forall g, ctx_includes g g.
  Proof.
    intros g x s H. exact H.
  Qed.

  (** Inclusion composes pointwise. *)
  Lemma ctx_includes_trans : forall g h k,
    ctx_includes g h -> ctx_includes h k -> ctx_includes g k.
  Proof.
    intros g h k Hgh Hhk x s H. apply Hhk, Hgh. exact H.
  Qed.

  (** A term keeps its sort when the context includes its assignments. *)
  Lemma has_includes : forall g h (t : term V.t) s,
    ctx_includes g h -> has g t s -> has h t s.
  Proof.
    intros g h [x|v] s Hinc Hhas; cbn [has] in *; [apply Hinc|]; exact Hhas.
  Qed.

  (** Term binding preserves every previously assigned variable. *)
  Lemma binds_includes : forall g (t : term V.t) s g',
    binds g t s g' -> ctx_includes g g'.
  Proof.
    intros g t s g' Hbind. destruct Hbind as [x s Hsort|x s Hnone|v];
      try apply ctx_includes_refl.
    intros y u Hsort. unfold ctx_set. destruct (Pos.eqb x y) eqn:Hxy.
    - apply Pos.eqb_eq in Hxy. subst y. congruence.
    - exact Hsort.
  Qed.

  (** A bound term has the sort required by that binding. *)
  Lemma binds_has : forall g (t : term V.t) s g',
    binds g t s g' -> has g' t s.
  Proof.
    intros g t s g' Hbind. destruct Hbind as [x s Hsort|x s Hnone|v];
      cbn [has]; try assumption; try reflexivity.
    unfold ctx_set. now rewrite Pos.eqb_refl.
  Qed.

  (** A binding can add only the variable term that it visits. *)
  Lemma binds_scope : forall g (t : term V.t) s g',
    binds g t s g' -> forall x u, g' x = Some u -> g x = Some u \/ t = Var x.
  Proof.
    intros g t s g' Hbind. destruct Hbind as [y s Hsort|y s Hnone|v];
      intros x u H; try (left; exact H).
    unfold ctx_set in H. destruct (Pos.eqb y x) eqn:Hyx.
    - apply Pos.eqb_eq in Hyx. subst x. right. reflexivity.
    - left. exact H.
  Qed.

  (** A partially assigned context can bind a term compatible with a complete target. *)
  Lemma binds_complete_target : forall g target (t : term V.t) s,
    ctx_includes g target -> has target t s ->
    exists g', binds g t s g' /\ ctx_includes g' target.
  Proof.
    intros g target [x|v] s Hinc Hhas; cbn [has] in Hhas.
    - destruct (g x) as [u|] eqn:Hlookup.
      + pose proof (Hinc x u Hlookup) as Hu. assert (u = s) by congruence. subst u.
        exists g. split; [apply binds_old; exact Hlookup|exact Hinc].
      + exists (ctx_set g x s). split; [apply binds_new; exact Hlookup|].
        intros y u H. unfold ctx_set in H. destruct (Pos.eqb x y) eqn:Hxy.
        * apply Pos.eqb_eq in Hxy. subst y. injection H as <-. exact Hhas.
        * apply Hinc. exact H.
    - subst s. exists g. split; [constructor|exact Hinc].
  Qed.

  (** Argument binding preserves previously assigned variables. *)
  Lemma binds_list_includes : forall g ts ss g',
    @binds_list V.t g ts ss g' -> ctx_includes g g'.
  Proof.
    intros g ts ss g' Hbind. induction Hbind as [g|g g1 g2 t ts s ss Hhead Htail IH].
    - apply ctx_includes_refl.
    - eapply ctx_includes_trans; [eapply binds_includes; exact Hhead|exact IH].
  Qed.

  (** Argument binding can add only variables appearing in its argument list. *)
  Lemma binds_list_scope : forall g ts ss g',
    @binds_list V.t g ts ss g' -> forall x u,
    g' x = Some u -> g x = Some u \/ In (Var x) ts.
  Proof.
    intros g ts ss g' Hbind. induction Hbind as [g|g g1 g2 t ts s ss Hhead Htail IH];
      intros x u Hsort.
    - left. exact Hsort.
    - destruct (IH x u Hsort) as [Hbound|Hin].
      + destruct (binds_scope g t s g1 Hhead x u Hbound) as [Hold|Heq].
        * left. exact Hold.
        * right. left. exact Heq.
      + right. right. exact Hin.
  Qed.

  (** Every bound argument retains its requested sort at the end of the binding list. *)
  Lemma binds_list_has : forall g ts ss g',
    @binds_list V.t g ts ss g' -> Forall2 (has g') ts ss.
  Proof.
    intros g ts ss g' Hbind. induction Hbind as [g|g g1 g2 t ts s ss Hhead Htail IH].
    - constructor.
    - constructor; [|exact IH]. eapply has_includes.
      + eapply binds_list_includes. exact Htail.
      + apply binds_has in Hhead. exact Hhead.
  Qed.

  (** A list of target-sorted arguments can be bound from any compatible partial context. *)
  Lemma binds_list_complete_target : forall target ts ss,
    Forall2 (@has V.t target) ts ss -> forall g, ctx_includes g target ->
    exists g', binds_list g ts ss g' /\ ctx_includes g' target.
  Proof.
    intros target ts ss Htyped.
    induction Htyped as [|t s ts ss Hhead Htail IH]; intros g Hinc.
    - exists g. split; [constructor|exact Hinc].
    - destruct (binds_complete_target g target t s Hinc Hhead) as [g1 [Hb Hinc1]].
      destruct (IH g1 Hinc1) as [g2 [Hbs Hinc2]].
      exists g2. split; [econstructor; eassumption|exact Hinc2].
  Qed.

  (** Result binding preserves previously assigned variables. *)
  Lemma binds_result_includes : forall g out res g',
    @binds_result V.t g out res g' -> ctx_includes g g'.
  Proof.
    intros g out [t|] g' Hbind; destruct out;
      cbn [binds_result out_sort] in Hbind; try contradiction.
    - apply binds_includes in Hbind. exact Hbind.
    - apply binds_includes in Hbind. exact Hbind.
    - subst g'. apply ctx_includes_refl.
  Qed.

  (** A result binding can add only its result variable. *)
  Lemma binds_result_scope : forall g out res g',
    @binds_result V.t g out res g' -> forall x u,
    g' x = Some u -> g x = Some u \/ In (Var x) (option_list res).
  Proof.
    intros g out [t|] g' Hbind; destruct out;
      cbn [binds_result out_sort] in Hbind; try contradiction;
      intros x u Hsort.
    - destruct (binds_scope g t SId g' Hbind x u Hsort) as [Hold|Heq];
        [left; exact Hold|right; left; exact Heq].
    - destruct (binds_scope g t SVal g' Hbind x u Hsort) as [Hold|Heq];
        [left; exact Hold|right; left; exact Heq].
    - subst g'. left. exact Hsort.
  Qed.

  (** The output context of a well-sorted query includes its starting context. *)
  Lemma query_ok_includes : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' -> ctx_includes g g'.
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as
      [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hargs Hres Hrest IH|
       g g1 op args res rest Hargs Hres Hrest IH].
    - apply ctx_includes_refl.
    - eapply ctx_includes_trans; [eapply binds_list_includes; exact Hargs|].
      eapply ctx_includes_trans; [eapply binds_result_includes; exact Hres|exact IH].
    - exact IH.
  Qed.
  (** A query can add only variables appearing in one of its atoms. *)
  Lemma query_ok_scope : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' -> forall x s,
    g' x = Some s -> g x = Some s \/
      exists a, In a q /\ In (Var x) (atom_terms a).
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as
      [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hargs Hres Hrest IH|
       g g1 op args res rest Hargs Hres Hrest IH]; intros x s Hbound.
    - left. exact Hbound.
    - destruct (IH x s Hbound) as [Hnew|[a [Hin Hvar]]].
      + destruct (binds_result_scope g1 out res g2 Hres x s Hnew) as [Harg|Hvar].
        * destruct (binds_list_scope g args ss g1 Hargs x s Harg) as [Hold|Hvar].
          -- left. exact Hold.
          -- right. exists (Fun V.t f args res). split; [left; reflexivity|].
             cbn [atom_terms]. apply in_or_app. left. exact Hvar.
        * right. exists (Fun V.t f args res). split; [left; reflexivity|].
          cbn [atom_terms]. apply in_or_app. right. exact Hvar.
      + right. exists a. split; [right; exact Hin|exact Hvar].
    - destruct (IH x s Hbound) as [Hold|[a [Hin Hvar]]].
      + left. exact Hold.
      + right. exists a. split; [right; exact Hin|exact Hvar].
  Qed.

  (** Every source variable in a sorted rewrite is below its generated root name. *)
  Lemma rewrite_context_bound : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    forall x s, g x = Some s -> (x < root_var rw)%positive.
  Proof.
    intros ds rw g [g0 [Hroot [Hleft [Hscope [Hquery Hright]]]]] x s Hbound.
    destruct (query_ok_scope _ _ g0 (cond V.t rw) g Hquery x s Hbound)
      as [Hold|[a [Hin Hvar]]].
    - apply root_var_hole. apply Hscope with s. exact Hold.
    - exact (proj2 (proj2 (root_var_bounds rw)) a x Hin Hvar).
  Qed.

  (** Binding can be replayed from a larger context compatible with the final target. *)
  Lemma binds_extend : forall g (t : term V.t) s g', binds g t s g' ->
    forall h target, ctx_includes g h -> ctx_includes h target ->
    ctx_includes g' target ->
    exists h', binds h t s h' /\ ctx_includes g' h' /\ ctx_includes h' target.
  Proof.
    intros g t s g' Hbind. destruct Hbind as [x s Hsort|x s Hnone|v];
      intros h target Hstart Hpart Htarget.
    - exists h. split; [apply binds_old; apply Hstart; exact Hsort|].
      split; assumption.
    - assert (Hsort : @has V.t target (Var x) s).
      { apply Htarget. unfold ctx_set. now rewrite Pos.eqb_refl. }
      destruct (binds_complete_target h target (Var x) s Hpart Hsort)
        as [h' [Hbind Hpart']]. exists h'. split; [exact Hbind|].
      split; [|exact Hpart']. intros y u Hnew. unfold ctx_set in Hnew.
      destruct (Pos.eqb x y) eqn:Hxy.
      + apply Pos.eqb_eq in Hxy. subst y. injection Hnew as <-.
        exact (binds_has h (Var x) s h' Hbind).
      + apply (binds_includes h (Var x) s h' Hbind), Hstart. exact Hnew.
    - exists h. split; [constructor|]. split; assumption.
  Qed.

  (** Argument binding can be replayed while preserving a compatible context extension. *)
  Lemma binds_list_extend : forall g ts ss g', @binds_list V.t g ts ss g' ->
    forall h target, ctx_includes g h -> ctx_includes h target ->
    ctx_includes g' target ->
    exists h', binds_list h ts ss h' /\ ctx_includes g' h' /\ ctx_includes h' target.
  Proof.
    intros g ts ss g' Hbind.
    induction Hbind as [g|g g1 g2 t ts s ss Hhead Htail IH];
      intros h target Hstart Hpart Htarget.
    - exists h. split; [constructor|]. split; assumption.
    - assert (Htarget1 : ctx_includes g1 target).
      { eapply ctx_includes_trans; [eapply binds_list_includes; exact Htail|exact Htarget]. }
      destruct (binds_extend g t s g1 Hhead h target Hstart Hpart Htarget1)
        as [h1 [Hb [Hstart1 Hpart1]]].
      destruct (IH h1 target Hstart1 Hpart1 Htarget) as [h2 [Hbs [Hstart2 Hpart2]]].
      exists h2. split; [econstructor; eassumption|]. split; assumption.
  Qed.

  (** Result binding can be replayed from a compatible context extension. *)
  Lemma binds_result_extend : forall g out res g', @binds_result V.t g out res g' ->
    forall h target, ctx_includes g h -> ctx_includes h target ->
    ctx_includes g' target ->
    exists h', binds_result h out res h' /\ ctx_includes g' h' /\ ctx_includes h' target.
  Proof.
    intros g out [t|] g' Hbind; destruct out;
      cbn [binds_result out_sort] in Hbind |- *; try contradiction.
    - apply binds_extend. exact Hbind.
    - apply binds_extend. exact Hbind.
    - subst g'. intros h target Hstart Hpart Htarget.
      exists h. split; [reflexivity|]. split; assumption.
  Qed.

  (** Query typing survives compatible extra assignments of fresh compiler variables. *)
  Lemma query_ok_extend : forall sorts kinds g q g',
    @query_ok V.t sorts kinds g q g' ->
    forall h target, ctx_includes g h -> ctx_includes h target ->
    ctx_includes g' target ->
    exists h', query_ok sorts kinds h q h' /\
      ctx_includes g' h' /\ ctx_includes h' target.
  Proof.
    intros sorts kinds g q g' Hquery.
    induction Hquery as
      [g|g g1 g2 g3 f args res ss out rest Hsort Hkind Hargs Hres Hrest IH|
       g g1 op args res rest Hargs Hres Hrest IH];
      intros h target Hstart Hpart Htarget.
    - exists h. split; [constructor|]. split; assumption.
    - assert (Htarget2 : ctx_includes g2 target).
      { eapply ctx_includes_trans; [eapply query_ok_includes; exact Hrest|exact Htarget]. }
      assert (Htarget1 : ctx_includes g1 target).
      { eapply ctx_includes_trans; [eapply binds_result_includes; exact Hres|exact Htarget2]. }
      destruct (binds_list_extend g args ss g1 Hargs h target Hstart Hpart Htarget1)
        as [h1 [Hargs' [Hstart1 Hpart1]]].
      destruct (binds_result_extend g1 out res g2 Hres h1 target Hstart1 Hpart1 Htarget2)
        as [h2 [Hres' [Hstart2 Hpart2]]].
      destruct (IH h2 target Hstart2 Hpart2 Htarget) as [h3 [Hrest' [Hstart3 Hpart3]]].
      exists h3. split; [econstructor; eassumption|]. split; assumption.
    - destruct (IH h target Hstart Hpart Htarget) as [h' [Hrest' [Hstart' Hpart']]].
      exists h'. split.
      + eapply query_prim; [| |exact Hrest'].
        * eapply Forall_impl; [|exact Hargs]. intros t Hhas.
          eapply has_includes; eassumption.
        * eapply has_includes; eassumption.
      + split; assumption.
  Qed.


  (** * Fresh constructor sort contexts *)

  (** Fresh compiler variables denote classes, while earlier source names keep their sorts. *)
  Definition fresh_context (g : ctx) (fresh : positive) : ctx :=
    fun x => if Pos.leb fresh x then Some SId else g x.

  (** Names below the fresh threshold retain their source assignment. *)
  Lemma fresh_context_low : forall g fresh x, (x < fresh)%positive ->
    fresh_context g fresh x = g x.
  Proof.
    intros g fresh x Hlt. unfold fresh_context. destruct (Pos.leb fresh x) eqn:Htest.
    - apply Pos.leb_le in Htest. lia.
    - reflexivity.
  Qed.

  (** Names at or above the fresh threshold have the class sort. *)
  Lemma fresh_context_high : forall g fresh x, (fresh <= x)%positive ->
    fresh_context g fresh x = Some SId.
  Proof.
    intros g fresh x Hle. unfold fresh_context. destruct (Pos.leb fresh x) eqn:Htest.
    - reflexivity.
    - apply Pos.leb_gt in Htest. lia.
  Qed.

  (** A bounded source context is included by its fresh-variable extension. *)
  Lemma fresh_context_includes : forall g fresh,
    (forall x s, g x = Some s -> (x < fresh)%positive) ->
    ctx_includes g (fresh_context g fresh).
  Proof.
    intros g fresh Hbound x s Hsort. rewrite fresh_context_low; [exact Hsort|].
    apply Hbound with s. exact Hsort.
  Qed.

  (** Extending the source context also extends its fresh-variable context. *)
  Lemma fresh_context_mono : forall g h fresh, ctx_includes g h ->
    ctx_includes (fresh_context g fresh) (fresh_context h fresh).
  Proof.
    intros g h fresh Hinc x s Hsort. unfold fresh_context in *.
    destruct (Pos.leb fresh x); [exact Hsort|apply Hinc; exact Hsort].
  Qed.

  (** Assigning a target-compatible sort preserves all older assignments. *)
  Lemma ctx_set_includes : forall g target x s,
    ctx_includes g target -> target x = Some s -> ctx_includes g (ctx_set g x s).
  Proof.
    intros g target x s Hpart Htarget y u Hsort.
    unfold ctx_set. destruct (Pos.eqb x y) eqn:Hxy; [|exact Hsort].
    apply Pos.eqb_eq in Hxy. subst y. pose proof (Hpart x u Hsort). congruence.
  Qed.

  (** Assigning a target-compatible sort keeps the resulting context compatible. *)
  Lemma ctx_set_target : forall g target x s,
    ctx_includes g target -> target x = Some s -> ctx_includes (ctx_set g x s) target.
  Proof.
    intros g target x s Hpart Htarget y u Hsort. unfold ctx_set in Hsort.
    destruct (Pos.eqb x y) eqn:Hxy.
    - apply Pos.eqb_eq in Hxy. subst y. injection Hsort as <-. exact Htarget.
    - apply Hpart. exact Hsort.
  Qed.

  (** A node-form table supplies a term at every existing node position. *)
  Lemma term_for_node : forall ns ts, Forall2 node_term ns ts ->
    forall j n, nth_error ns j = Some n ->
    exists t, nth_error ts j = Some t /\ node_term n t.
  Proof.
    intros ns ts Hforms. induction Hforms as [|n t ns ts Hhead Htail IH];
      intros [|j] n' Hnth; cbn [nth_error] in Hnth; try discriminate.
    - injection Hnth as <-. exists t. split; [reflexivity|exact Hhead].
    - exact (IH j n' Hnth).
  Qed.

  (** Table interpretation transfers the declared sort of each node to its compiled term. *)
  Definition sorted_pattern_table (g target : ctx) (ns : list (pnode V.t))
      (ts : list (term V.t)) : Prop :=
    forall j n t s, nth_error ns j = Some n -> nth_error ts j = Some t ->
      pnode_sort g n = Some s -> has target t s.

  (** Fresh constructor names and unchanged holes make the generated table well sorted. *)
  Lemma fresh_table_sorted : forall g ns ts fresh,
    Forall2 node_term ns ts ->
    (forall h, In (PHole h) ns -> (h < fresh)%positive) ->
    (forall x, In x (constructor_names ns ts) -> (fresh <= x)%positive) ->
    sorted_pattern_table g (fresh_context g fresh) ns ts.
  Proof.
    intros g ns ts fresh Hforms Hholes Hnames j n t s Hnode Hterm Hsort.
    pose proof (node_term_at ns ts Hforms j n t Hnode Hterm) as Hform.
    destruct n as [h|f ch|v]; cbn [node_term pnode_sort] in Hform, Hsort.
    - subst t. cbn [has]. rewrite fresh_context_low; [exact Hsort|].
      apply Hholes. apply nth_error_In with j. exact Hnode.
    - destruct Hform as [x ->]. injection Hsort as <-. cbn [has].
      apply fresh_context_high, Hnames. eapply constructor_name_at; eassumption.
    - subst t. injection Hsort as <-. reflexivity.
  Qed.

  (** Pattern tables preserve forms, assign usable sorts, and advance beyond their root name. *)
  Lemma pattern_table_sorted : forall (p : fpat V.t) root_name g,
    (pattern_max (nodes V.t p) < root_name)%positive ->
    let ts := fst (pattern_table p root_name) in
    Forall2 node_term (nodes V.t p) ts /\
    sorted_pattern_table g (fresh_context g root_name) (nodes V.t p) ts /\
    (root_name < snd (pattern_table p root_name))%positive.
  Proof.
    intros [ns r] rn g Hfresh. cbn [pattern_table nodes].
    pose proof (pattern_terms_info ns (Some r) rn (Pos.succ rn) ltac:(lia)) as Hinfo.
    destruct (pattern_terms ns (Some r) rn (Pos.succ rn)) as [ts last].
    destruct Hinfo as [Hforms [Hlast [Hrange Hdistinct]]]. cbn [fst snd].
    split; [exact Hforms|]. split; [|lia]. apply fresh_table_sorted; [exact Hforms| |].
    - intros h Hin. pose proof (pattern_max_hole ns h Hin). cbn [nodes] in Hfresh. lia.
    - intros x Hin. destruct (Hrange x Hin) as [[-> _]|Hrange']; lia.
  Qed.

  (** A well-sorted node lookup returns a term of the same sort. *)
  Lemma pattern_get_typed : forall g target ns ts j s default,
    Forall2 node_term ns ts -> sorted_pattern_table g target ns ts ->
    (exists n, nth_error ns j = Some n /\ pnode_sort g n = Some s) ->
    has target (pattern_get default j ts) s.
  Proof.
    intros g target ns ts j s default Hforms Htable [n [Hnode Hsort]].
    destruct (term_for_node ns ts Hforms j n Hnode) as [t [Hterm Hform]].
    unfold pattern_get. rewrite Hterm. exact (Htable j n t s Hnode Hterm Hsort).
  Qed.

  (** A constructor contributes its own atom to the generated query. *)
  Lemma pattern_atom_at : forall ns ts all j f ch t,
    nth_error ns j = Some (PApp f ch) -> nth_error ts j = Some t ->
    In (Fun V.t f (map (fun k => pattern_get (Var 1%positive) k all) ch) (Some t))
      (pattern_atoms ns ts all).
  Proof.
    induction ns as [|n ns IH]; intros [|u ts] all [|j] f ch t Hnode Hterm;
      cbn [nth_error] in Hnode, Hterm; try discriminate.
    - injection Hnode as Hn. subst n. injection Hterm as Ht. subst u.
      left. reflexivity.
    - specialize (IH ts all j f ch t Hnode Hterm).
      destruct n; cbn [pattern_atoms]; try exact IH. right. exact IH.
  Qed.
  (** A term has at most one sort in any fixed context. *)
  Lemma has_unique : forall g (t : term V.t) s u, has g t s -> has g t u -> s = u.
  Proof.
    intros g [x|v] s u Hs Hu; cbn [has] in *; congruence.
  Qed.

  (** A compatible partial context agrees with the target sort of every typed term. *)
  Lemma has_target_sort : forall g target (t : term V.t) s u,
    ctx_includes g target -> has g t u -> has target t s -> has g t s.
  Proof.
    intros g target t s u Hinc Hu Hs.
    assert (u = s) by (eapply has_unique; [eapply has_includes; eassumption|exact Hs]).
    subst u. exact Hu.
  Qed.

  (** An argument in a typed list has some sort in that context. *)
  Lemma has_list_member : forall g ts ss, Forall2 (@has V.t g) ts ss ->
    forall t, In t ts -> exists s, has g t s.
  Proof.
    intros g ts ss Htyped. induction Htyped as [|t s ts ss Hhead Htail IH];
      intros u Hin; [contradiction|].
    destruct Hin as [<-|Hin]; [exists s; exact Hhead|apply IH; exact Hin].
  Qed.

  (** A constructor atom is well sorted in a complete target context. *)
  Definition constructor_atom_typed sorts kinds target (a : atom V.t) : Prop :=
    match a with
    | Fun _ f args (Some t) => exists ss,
        sorts f = Some ss /\ kinds f = Some OId /\
        Forall2 (has target) args ss /\ has target t SId
    | _ => False
    end.

  (** A sorted constructor-only query can bind all of its terms from a partial context. *)
  Lemma constructor_query_complete : forall sorts kinds target q,
    Forall (constructor_atom_typed sorts kinds target) q ->
    forall g, ctx_includes g target -> exists g',
      query_ok sorts kinds g q g' /\ ctx_includes g' target /\
      (forall a t s, In a q -> In t (atom_terms a) -> has target t s -> has g' t s).
  Proof.
    intros sorts kinds target q Htyped.
    induction Htyped as [|a q Hhead Htail IH]; intros g Hpart.
    - exists g. split; [constructor|]. split; [exact Hpart|].
      intros a t s Hin. contradiction.
    - destruct a as [f args [result|]|op args result];
        cbn [constructor_atom_typed] in Hhead; try contradiction.
      destruct Hhead as [ss [Hsort [Hkind [Hargs Hresult]]]].
      destruct (binds_list_complete_target target args ss Hargs g Hpart)
        as [g1 [Hbargs Hpart1]].
      destruct (binds_complete_target g1 target result SId Hpart1 Hresult)
        as [g2 [Hbresult Hpart2]].
      destruct (IH g2 Hpart2) as [g3 [Hquery [Hpart3 Hcovered]]].
      assert (Hkeep2 : ctx_includes g2 g3) by (eapply query_ok_includes; exact Hquery).
      assert (Hkeep1 : ctx_includes g1 g3).
      { eapply ctx_includes_trans; [eapply binds_includes; exact Hbresult|exact Hkeep2]. }
      exists g3. split.
      + eapply query_fun; [exact Hsort|exact Hkind|exact Hbargs|exact Hbresult|exact Hquery].
      + split; [exact Hpart3|]. intros a t s [Heq|Hin] Hterm Htyped.
        * subst a. cbn [atom_terms option_list] in Hterm. apply in_app_or in Hterm.
          destruct Hterm as [Harg|[Heq|Hbad]]; [|subst t|contradiction].
          -- destruct (has_list_member g1 args ss (binds_list_has _ _ _ _ Hbargs) t Harg)
               as [u Hu].
             eapply has_target_sort; [exact Hpart3| |exact Htyped].
             eapply has_includes; [exact Hkeep1|exact Hu].
          -- eapply has_target_sort; [exact Hpart3| |exact Htyped].
             eapply has_includes; [exact Hkeep2|]. eapply binds_has; exact Hbresult.
        * exact (Hcovered a t s Hin Hterm Htyped).
  Qed.

  (** Concatenating two sorted queries composes their intermediate contexts. *)
  Lemma query_ok_app : forall sorts kinds g q g1 rest g2,
    @query_ok V.t sorts kinds g q g1 -> query_ok sorts kinds g1 rest g2 ->
    query_ok sorts kinds g (q ++ rest) g2.
  Proof.
    intros sorts kinds g q g1 rest g2 Hfirst. induction Hfirst;
      intro Hrest; cbn [app]; [exact Hrest| |]; econstructor; eauto.
  Qed.

  (** Node-wise constructor typing induces typing of the emitted atom list. *)
  Lemma pattern_atoms_from_typed_nodes : forall sorts kinds target ns ts all,
    Forall2 (fun n t => match n with
      | PApp f ch => constructor_atom_typed sorts kinds target
          (Fun V.t f (map (fun j => pattern_get (Var 1%positive) j all) ch) (Some t))
      | _ => True
      end) ns ts ->
    Forall (constructor_atom_typed sorts kinds target) (pattern_atoms ns ts all).
  Proof.
    intros sorts kinds target ns ts all Htyped.
    induction Htyped as [|n t ns ts Hhead Htail IH]; [constructor|].
    destruct n; cbn [pattern_atoms]; try exact IH. constructor; assumption.
  Qed.

  (** A compatible term table turns each well-sorted pattern constructor into a sorted atom. *)
  Lemma pattern_atoms_typed : forall sorts kinds g target (p : fpat V.t) ts,
    pat_ok sorts kinds g p -> Forall2 node_term (nodes V.t p) ts ->
    sorted_pattern_table g target (nodes V.t p) ts ->
    Forall (constructor_atom_typed sorts kinds target)
      (pattern_atoms (nodes V.t p) ts ts).
  Proof.
    intros sorts kinds g target [ns r] ts [_ [_ [_ Hnodes]]] Hforms Htable.
    apply pattern_atoms_from_typed_nodes.
    apply (forall2_at_indices (pnode V.t) (term V.t)); [eapply Forall2_length; exact Hforms|].
    intros i n t Hnode Hterm. destruct n as [h|f ch|v]; [exact I| |exact I].
    destruct (Hnodes i f ch Hnode) as [Hkind [ss [Hsort Hchildren]]].
    exists ss. split; [exact Hsort|]. split; [exact Hkind|]. split.
    - clear Hnode Hterm Hsort Hkind. induction Hchildren as [|j s ch ss Hhead Htail IH];
        cbn [map]; [constructor|].
      constructor; [|exact IH].
      eapply pattern_get_typed; [exact Hforms|exact Htable|exact (proj2 Hhead)].
    - exact (Htable i (PApp f ch) t SId Hnode Hterm eq_refl).
  Qed.

  (** Every left-side hole occurs in the argument list of a generated constructor atom. *)
  Lemma pattern_hole_occurs : forall sorts kinds g ns r ts h,
    pat_ok sorts kinds g (FPat V.t ns r) -> app_rooted (FPat V.t ns r) ->
    Forall2 node_term ns ts -> In (PHole h) ns ->
    exists a, In a (pattern_atoms ns ts ts) /\ In (Var h) (atom_terms a).
  Proof.
    intros sorts kinds g ns r ts h [Hlast [_ [Hcoverage _]]] [rf [rc Hroot]] Hforms Hin.
    cbn [nodes root] in Hlast, Hcoverage, Hroot.
    apply In_nth_error in Hin. destruct Hin as [j Hhole].
    assert (Hindex : j < length ns).
    { apply nth_error_Some. rewrite Hhole. discriminate. }
    assert (Hbefore : j < r).
    { destruct (Nat.eq_dec j r) as [->|Hneq]; [congruence|lia]. }
    destruct (Hcoverage j Hbefore) as [i [f [ch [_ [Hparent Hchild]]]]].
    destruct (term_for_node ns ts Hforms j (PHole h) Hhole) as [ht [Hht Hform]].
    cbn [node_term] in Hform. subst ht.
    destruct (term_for_node ns ts Hforms i (PApp f ch) Hparent) as [t [Ht Hform]].
    exists (Fun V.t f (map (fun k => pattern_get (Var 1%positive) k ts) ch) (Some t)).
    split; [eapply pattern_atom_at; eassumption|].
    cbn [atom_terms]. apply in_or_app. left. apply in_map_iff.
    exists j. split; [unfold pattern_get; rewrite Hht; reflexivity|exact Hchild].
  Qed.
  (** Every constructor's result term occurs in its emitted atom. *)
  Lemma pattern_constructor_occurs : forall ns ts i f ch t,
    nth_error ns i = Some (PApp f ch) -> nth_error ts i = Some t ->
    exists a, In a (pattern_atoms ns ts ts) /\ In t (atom_terms a).
  Proof.
    intros ns ts i f ch t Hnode Hterm.
    exists (Fun V.t f (map (fun j => pattern_get (Var 1%positive) j ts) ch) (Some t)).
    split; [eapply pattern_atom_at; eassumption|].
    cbn [atom_terms option_list]. apply in_or_app. right. left. reflexivity.
  Qed.

  (** Covering every generated atom also covers the scoped source hole context. *)
  Lemma pattern_query_covers_context : forall sorts kinds g target h ns r ts,
    pat_ok sorts kinds g (FPat V.t ns r) -> app_rooted (FPat V.t ns r) ->
    Forall2 node_term ns ts -> ctx_includes g target ->
    (forall x s, g x = Some s -> In (PHole x) ns) ->
    (forall a t s, In a (pattern_atoms ns ts ts) -> In t (atom_terms a) ->
      has target t s -> has h t s) -> ctx_includes g h.
  Proof.
    intros sorts kinds g target h ns r ts Hpat Hroot Hforms Htarget Hscope Hcovers x s Hsort.
    destruct (pattern_hole_occurs sorts kinds g ns r ts x Hpat Hroot Hforms
      (Hscope x s Hsort)) as [a [Hin Hterm]].
    apply (Hcovers a (Var x) s Hin Hterm). apply Htarget. exact Hsort.
  Qed.

  (** A flattened constructor-rooted pattern binds its source holes and its fresh root. *)
  Lemma flatten_pat_sorted : forall sorts kinds g (p : fpat V.t) rn,
    pat_ok sorts kinds g p -> app_rooted p ->
    (forall x s, g x = Some s -> In (PHole x) (nodes V.t p)) ->
    (pattern_max (nodes V.t p) < rn)%positive ->
    exists h, query_ok sorts kinds ctx_empty (flatten_pat p rn) h /\
      ctx_includes g h /\ ctx_includes h (fresh_context g rn) /\ h rn = Some SId.
  Proof.
    intros sorts kinds g [ns r] rn Hpat Hroot Hscope Hfresh.
    set (ts := fst (pattern_table (FPat V.t ns r) rn)).
    destruct (pattern_table_sorted (FPat V.t ns r) rn g Hfresh)
      as [Hforms [Htable Hlast]].
    assert (Hsource : ctx_includes g (fresh_context g rn)).
    { apply fresh_context_includes. intros x s Hsort.
      pose proof (pattern_max_hole ns x (Hscope x s Hsort)). cbn [nodes] in Hfresh. lia. }
    pose proof (pattern_atoms_typed sorts kinds g (fresh_context g rn)
      (FPat V.t ns r) ts Hpat Hforms Htable) as Htyped.
    destruct (constructor_query_complete sorts kinds (fresh_context g rn)
      (pattern_atoms ns ts ts) Htyped ctx_empty ltac:(intros x s H; discriminate H))
      as [h [Hquery [Hpart Hcovers]]].
    exists h. split; [exact Hquery|]. split.
    - eapply pattern_query_covers_context; eassumption.
    - split; [exact Hpart|]. destruct Hroot as [f [ch Hroot]].
      assert (Hterm : nth_error ts r = Some (Var rn)).
      { unfold ts, pattern_table. eapply pattern_terms_root. exact Hroot. }
      destruct (pattern_constructor_occurs ns ts r f ch (Var rn) Hroot Hterm)
        as [a [Hin Hterm_in]].
      apply (Hcovers a (Var rn) SId Hin Hterm_in).
      cbn [has]. apply fresh_context_high. lia.
  Qed.

  (** The complete flattened left side types the condition while retaining its class root. *)
  Lemma flatten_lhs_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    exists h, query_ok (lookup_sorts ds) (lookup_kind ds) ctx_empty (flatten_lhs rw) h /\
      ctx_includes g h /\ ctx_includes h (fresh_context g (root_var rw)) /\
      h (root_var rw) = Some SId.
  Proof.
    intros ds rw g Hrw. destruct Hrw as [g0 [Hroot [Hleft [Hscope [Hquery Hright]]]]].
    destruct (flatten_pat_sorted (lookup_sorts ds) (lookup_kind ds) g0
      (lhs V.t rw) (root_var rw) Hleft Hroot Hscope (proj1 (root_var_bounds rw)))
      as [h0 [Hflat [Hincludes [Hpart Hroot_sort]]]].
    assert (Hgrow : ctx_includes g0 g) by (eapply query_ok_includes; exact Hquery).
    assert (Hpart' : ctx_includes h0 (fresh_context g (root_var rw))).
    { eapply ctx_includes_trans; [exact Hpart|apply fresh_context_mono; exact Hgrow]. }
    assert (Htarget : ctx_includes g (fresh_context g (root_var rw))).
    { apply fresh_context_includes. intros x s Hsort.
      eapply rewrite_context_bound; [|exact Hsort].
      exists g0. split; [exact Hroot|]. split; [exact Hleft|].
      split; [exact Hscope|]. split; assumption. }
    destruct (query_ok_extend _ _ g0 (cond V.t rw) g Hquery h0
      (fresh_context g (root_var rw)) Hincludes Hpart' Htarget)
      as [h [Hconditions [Hsource Hpart_final]]].
    exists h. split.
    - assert (Hflatten : flatten_lhs rw =
        flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw).
      { destruct rw. reflexivity. }
      rewrite Hflatten. eapply query_ok_app; eassumption.
    - split; [exact Hsource|]. split; [exact Hpart_final|].
      apply (query_ok_includes _ _ _ _ _ Hconditions). exact Hroot_sort.
  Qed.


  (** Every hole occurring in a well-sorted pattern is assigned a sort. *)
  Lemma pat_hole_sorted : forall sorts kinds g (p : fpat V.t) h,
    pat_ok sorts kinds g p -> In (PHole h) (nodes V.t p) -> exists s, g h = Some s.
  Proof.
    intros sorts kinds g p h [Hlast [Hroot [Hcoverage Hnodes]]] Hin.
    apply In_nth_error in Hin. destruct Hin as [j Hhole].
    assert (Hindex : j < length (nodes V.t p)).
    { apply nth_error_Some. rewrite Hhole. discriminate. }
    destruct (Nat.eq_dec j (root V.t p)) as [->|Hneq].
    - destruct Hroot as [n [Hnode Hsort]]. rewrite Hhole in Hnode.
      injection Hnode as <-. exists SId. exact Hsort.
    - assert (Hbefore : j < root V.t p) by lia.
      destruct (Hcoverage j Hbefore) as [i [f [ch [_ [Hparent Hchild]]]]].
      destruct (Hnodes i f ch Hparent) as [_ [ss [_ Hchildren]]].
      assert (Hsome : exists s, pat_sort g p j s).
      { clear Hcoverage Hnodes Hroot Hlast Hbefore Hindex Hneq Hparent.
        induction Hchildren as [|k s ch ss [_ Hsort] Htail IH].
        - contradiction.
        - destruct Hchild as [<-|Hchild].
          + exists s. exact Hsort.
          + apply IH. exact Hchild. }
      destruct Hsome as [s [n [Hnode Hsort]]]. rewrite Hhole in Hnode.
      injection Hnode as <-. exists s. exact Hsort.
  Qed.

  (** * Typing the ordered constructor actions *)

  (** Earlier positions in the pattern table are already available at their node sorts. *)
  Definition prefix_terms_sorted (g h : ctx) (ns : list (pnode V.t))
      (ts : list (term V.t)) (bound : nat) : Prop :=
    forall j n t s, j < bound -> nth_error ns j = Some n -> nth_error ts j = Some t ->
      pnode_sort g n = Some s -> has h t s.

  (** Prefix typing supplies the compiled term for an earlier well-sorted child. *)
  Lemma prefix_get_typed : forall g h ns ts bound j s default,
    Forall2 node_term ns ts -> prefix_terms_sorted g h ns ts bound -> j < bound ->
    (exists n, nth_error ns j = Some n /\ pnode_sort g n = Some s) ->
    has h (pattern_get default j ts) s.
  Proof.
    intros g h ns ts bound j s default Hforms Hprefix Hbefore [n [Hnode Hsort]].
    destruct (term_for_node ns ts Hforms j n Hnode) as [t [Hterm Hform]].
    unfold pattern_get. rewrite Hterm. eapply Hprefix; eassumption.
  Qed.

  (** Extending a context and typing its next node advances the typed prefix by one. *)
  Lemma prefix_terms_step : forall g h h' ns ts i n t,
    prefix_terms_sorted g h ns ts i -> ctx_includes h h' ->
    nth_error ns i = Some n -> nth_error ts i = Some t ->
    (forall s, pnode_sort g n = Some s -> has h' t s) ->
    prefix_terms_sorted g h' ns ts (S i).
  Proof.
    intros g h h' ns ts i n t Hprefix Hkeep Hnode Hterm Hhead j n' t' s
      Hbefore Hnode' Hterm' Hsort.
    destruct (Nat.eq_dec j i) as [->|Hneq].
    - assert (n' = n) by congruence. assert (t' = t) by congruence.
      subst n' t'. apply Hhead. exact Hsort.
    - eapply has_includes; [exact Hkeep|]. eapply (Hprefix j n' t' s); [lia| | |]; eassumption.
  Qed.

  (** Constructor declarations require earlier children at their declared node sorts. *)
  Definition pattern_node_sorts sorts kinds g (ns : list (pnode V.t)) : Prop :=
    forall i f ch, nth_error ns i = Some (PApp f ch) ->
      kinds f = Some OId /\ exists ss, sorts f = Some ss /\
      Forall2 (fun j s => j < i /\ exists n,
        nth_error ns j = Some n /\ pnode_sort g n = Some s) ch ss.

  (** All children of the current constructor read their sorts from the typed prefix. *)
  Lemma pattern_children_prefix_typed : forall g h ns ts i ch ss,
    Forall2 node_term ns ts -> prefix_terms_sorted g h ns ts i ->
    Forall2 (fun j s => j < i /\ exists n,
      nth_error ns j = Some n /\ pnode_sort g n = Some s) ch ss ->
    Forall2 (has h) (map (fun j => pattern_get (Var 1%positive) j ts) ch) ss.
  Proof.
    intros g h ns ts i ch ss Hforms Hprefix Hchildren.
    induction Hchildren as [|j s ch ss [Hbefore Hsort] Htail IH]; cbn [map].
    - constructor.
    - constructor; [|exact IH]. eapply prefix_get_typed; eassumption.
  Qed.

  (** One pattern node may prepend its constructor action to a typed continuation. *)
  Definition pattern_step_typed sorts kinds (h h' : ctx) (n : pnode V.t)
      (t : term V.t) (all : list (term V.t)) : Prop :=
    forall acts, actions_ok sorts kinds h' acts -> actions_ok sorts kinds h
      (match n, t with
       | PApp f ch, Var x =>
           Make x f (map (fun j => pattern_get (Var 1%positive) j all) ch) :: acts
       | _, _ => acts
       end).

  (** A node step preserves compatible assignments and makes its own term available. *)
  Lemma pattern_step_sorted : forall sorts kinds g target ns ts i n t h,
    Forall2 node_term ns ts -> sorted_pattern_table g target ns ts ->
    pattern_node_sorts sorts kinds g ns ->
    nth_error ns i = Some n -> nth_error ts i = Some t ->
    ctx_includes g h -> ctx_includes h target -> prefix_terms_sorted g h ns ts i ->
    exists h', ctx_includes h h' /\ ctx_includes h' target /\
      (forall s, pnode_sort g n = Some s -> has h' t s) /\
      pattern_step_typed sorts kinds h h' n t ts.
  Proof.
    intros sorts kinds g target ns ts i n t h Hforms Htable Hnodes Hnode Hterm
      Hsource Hpart Hprefix.
    pose proof (node_term_at ns ts Hforms i n t Hnode Hterm) as Hform.
    destruct n as [x|f ch|v]; cbn [node_term] in Hform.
    - subst t. exists h. split; [apply ctx_includes_refl|]. split; [exact Hpart|].
      split.
      + intros s Hsort. apply Hsource. exact Hsort.
      + intros acts Hacts. exact Hacts.
    - destruct Hform as [x ->].
      assert (Hclass : target x = Some SId) by
        (exact (Htable i (PApp f ch) (Var x) SId Hnode Hterm eq_refl)).
      destruct (Hnodes i f ch Hnode) as [Hkind [ss [Hsort Hchildren]]].
      pose proof (pattern_children_prefix_typed g h ns ts i ch ss Hforms Hprefix Hchildren)
        as Hargs.
      exists (ctx_set h x SId). split; [eapply ctx_set_includes; eassumption|].
      split; [eapply ctx_set_target; eassumption|]. split.
      + intros s Hs. cbn [pnode_sort] in Hs. injection Hs as <-.
        cbn [has]. unfold ctx_set. now rewrite Pos.eqb_refl.
      + intros acts Hacts. cbn [actions_ok]. exists ss. split; [exact Hsort|].
        split; [exact Hkind|]. split; assumption.
    - subst t. exists h. split; [apply ctx_includes_refl|]. split; [exact Hpart|].
      split.
      + intros s Hs. cbn [pnode_sort] in Hs. injection Hs as <-. reflexivity.
      + intros acts Hacts. exact Hacts.
  Qed.

  (** Appending a continuation exposes exactly the current node's optional Make action. *)
  Lemma pattern_actions_cons : forall (n : pnode V.t) ns t ts all acts,
    pattern_actions (n :: ns) (t :: ts) all ++ acts =
      match n, t with
      | PApp f ch, Var x =>
          Make x f (map (fun j => pattern_get (Var 1%positive) j all) ch) ::
            (pattern_actions ns ts all ++ acts)
      | _, _ => pattern_actions ns ts all ++ acts
      end.
  Proof.
    intros n ns t ts all acts. destruct n, t; reflexivity.
  Qed.

  (** The action fold advances its sorted table prefix and types every continuation. *)
  Lemma pattern_actions_sorted_fold : forall sorts kinds g target all_ns all_ts,
    Forall2 node_term all_ns all_ts -> sorted_pattern_table g target all_ns all_ts ->
    pattern_node_sorts sorts kinds g all_ns ->
    forall ns ts, Forall2 node_term ns ts -> forall i h,
    (forall j, nth_error ns j = nth_error all_ns (i + j)) ->
    (forall j, nth_error ts j = nth_error all_ts (i + j)) ->
    ctx_includes g h -> ctx_includes h target ->
    prefix_terms_sorted g h all_ns all_ts i ->
    exists h', ctx_includes h h' /\ ctx_includes h' target /\
      prefix_terms_sorted g h' all_ns all_ts (i + length ns) /\
      (forall acts, actions_ok sorts kinds h' acts ->
        actions_ok sorts kinds h (pattern_actions ns ts all_ts ++ acts)).
  Proof.
    intros sorts kinds g target all_ns all_ts Hwhole Htable Hnodes ns ts Hforms.
    induction Hforms as [|n t ns ts Hform Hforms IH];
      intros i h Hnode_pos Hterm_pos Hsource Hpart Hprefix.
    - exists h. split; [apply ctx_includes_refl|]. split; [exact Hpart|]. split.
      + cbn [length]. rewrite Nat.add_0_r. exact Hprefix.
      + intros acts Hacts. exact Hacts.
    - assert (Hnode : nth_error all_ns i = Some n).
      { specialize (Hnode_pos 0). rewrite Nat.add_0_r in Hnode_pos. symmetry. exact Hnode_pos. }
      assert (Hterm : nth_error all_ts i = Some t).
      { specialize (Hterm_pos 0). rewrite Nat.add_0_r in Hterm_pos. symmetry. exact Hterm_pos. }
      destruct (pattern_step_sorted sorts kinds g target all_ns all_ts i n t h
        Hwhole Htable Hnodes Hnode Hterm Hsource Hpart Hprefix)
        as [h1 [Hkeep1 [Hpart1 [Hhead Hstep]]]].
      assert (Hsource1 : ctx_includes g h1) by (eapply ctx_includes_trans; eassumption).
      assert (Hprefix1 : prefix_terms_sorted g h1 all_ns all_ts (S i)).
      { eapply prefix_terms_step; eassumption. }
      assert (Hnode_pos1 : forall j, nth_error ns j = nth_error all_ns (S i + j)).
      { intro j. replace (S i + j) with (i + S j) by lia. exact (Hnode_pos (S j)). }
      assert (Hterm_pos1 : forall j, nth_error ts j = nth_error all_ts (S i + j)).
      { intro j. replace (S i + j) with (i + S j) by lia. exact (Hterm_pos (S j)). }
      destruct (IH (S i) h1 Hnode_pos1 Hterm_pos1 Hsource1 Hpart1 Hprefix1)
        as [h2 [Hkeep2 [Hpart2 [Hprefix2 Hcontinue]]]].
      exists h2. split; [eapply ctx_includes_trans; eassumption|].
      split; [exact Hpart2|]. split.
      + replace (i + length (n :: ns)) with (S i + length ns) by (cbn [length]; lia).
        exact Hprefix2.
      + intros acts Hacts. rewrite pattern_actions_cons. apply Hstep, Hcontinue. exact Hacts.
  Qed.


  (** Reserving names from an earlier threshold preserves a later fresh-name context. *)
  Lemma fresh_context_lower : forall g low high,
    (low <= high)%positive -> (forall x s, g x = Some s -> (x < low)%positive) ->
    ctx_includes (fresh_context g high) (fresh_context g low).
  Proof.
    intros g low high Horder Hbound x s Hsort. unfold fresh_context in Hsort.
    destruct (Pos.leb high x) eqn:Hhigh.
    - apply Pos.leb_le in Hhigh. rewrite fresh_context_high; [exact Hsort|lia].
    - rewrite fresh_context_low; [exact Hsort|eapply Hbound; exact Hsort].
  Qed.

  (** Every typed pattern table remains typed when its target context grows. *)
  Lemma sorted_pattern_table_includes : forall g target target' ns ts,
    sorted_pattern_table g target ns ts -> ctx_includes target target' ->
    sorted_pattern_table g target' ns ts.
  Proof.
    intros g target target' ns ts Htable Hgrow i n t s Hnode Hterm Hsort.
    eapply has_includes; [exact Hgrow|]. eapply Htable; eassumption.
  Qed.

  (** Ordered constructor actions finish with a well-sorted union of the two roots. *)
  Lemma pattern_actions_sorted : forall sorts kinds g target (p : fpat V.t) ts h old_root default,
    pat_ok sorts kinds g p -> Forall2 node_term (nodes V.t p) ts ->
    sorted_pattern_table g target (nodes V.t p) ts ->
    ctx_includes g h -> ctx_includes h target -> h old_root = Some SId ->
    actions_ok sorts kinds h
      (pattern_actions (nodes V.t p) ts ts ++
        [Union (Var old_root) (pattern_get default (root V.t p) ts)]).
  Proof.
    intros sorts kinds g target p ts h old_root default
      [Hlast [Hroot [_ Hnodes]]] Hforms Htable Hsource Hpart Hold.
    assert (Hprefix0 : prefix_terms_sorted g h (nodes V.t p) ts 0).
    { intros j n t s Hlt. lia. }
    destruct (pattern_actions_sorted_fold sorts kinds g target (nodes V.t p) ts
      Hforms Htable Hnodes (nodes V.t p) ts Hforms 0 h
      (fun j => eq_refl) (fun j => eq_refl) Hsource Hpart Hprefix0)
      as [h' [Hkeep [Hpart' [Hprefix Hcontinue]]]].
    apply Hcontinue. cbn [actions_ok]. split; [apply Hkeep; exact Hold|].
    split; [|exact I].
    eapply (prefix_get_typed g h' (nodes V.t p) ts (length (nodes V.t p))
      (root V.t p) SId default); [exact Hforms|exact Hprefix|lia|exact Hroot].
  Qed.

  (** A compiled rewrite has a typed query followed by typed constructor and union actions. *)
  Lemma compile_rule_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    rule_ok (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof.
    intros ds rw g Hrw.
    destruct (flatten_lhs_sorted ds rw g Hrw)
      as [h [Hquery [Hsource [Hpart Hroot]]]].
    destruct (root_var_bounds rw) as [Hleft [Hright Hconditions]].
    destruct (pattern_table_sorted (lhs V.t rw) (root_var rw) g Hleft)
      as [_ [_ Hnext]].
    set (next := snd (pattern_table (lhs V.t rw) (root_var rw))).
    assert (Hfresh : (pattern_max (nodes V.t (rhs V.t rw)) < next)%positive) by
      (unfold next; lia).
    destruct (pattern_table_sorted (rhs V.t rw) next g Hfresh)
      as [Hforms [Htable Hlast]].
    assert (Htarget : ctx_includes (fresh_context g next) (fresh_context g (root_var rw))).
    { apply fresh_context_lower; [unfold next; lia|].
      intros x s Hsort. eapply rewrite_context_bound; eassumption. }
    assert (Htyped : sorted_pattern_table g (fresh_context g (root_var rw))
      (nodes V.t (rhs V.t rw)) (fst (pattern_table (rhs V.t rw) next))).
    { eapply sorted_pattern_table_includes; eassumption. }
    exists h. split.
    { assert (Heq : query V.t (compile_rule rw) = flatten_lhs rw).
      { destruct rw as [lp [ns r] conditions]. reflexivity. }
      rewrite Heq. exact Hquery. }
    assert (Hactions : actions V.t (compile_rule rw) =
      pattern_actions (nodes V.t (rhs V.t rw))
        (fst (pattern_table (rhs V.t rw) next))
        (fst (pattern_table (rhs V.t rw) next)) ++
      [Union (Var (root_var rw))
        (pattern_get (Var next) (root V.t (rhs V.t rw))
          (fst (pattern_table (rhs V.t rw) next)))]).
    { unfold next. destruct rw as [lp [ns r] conditions]. reflexivity. }
    destruct Hrw as [g0 [Hrooted [Hleftpat [Hscope [Hcond Hrightpat]]]]].
    rewrite Hactions. eapply pattern_actions_sorted; eassumption.
  Qed.


  Lemma compile_program : forall ds rws ans,
    decls V.t (compile ds rws ans) = ds /\
    rules V.t (compile ds rws ans) = map compile_rule rws ++ ans.
  Proof.
    intros ds rws ans. split; reflexivity.
  Qed.

  Lemma compile_query : forall rw, query V.t (compile_rule rw) = flatten_lhs rw.
  Proof.
    intros [lp [ns r] conditions]. reflexivity.
  Qed.

  Lemma compile_sorted : forall ds rws ans, rules_ok ds rws ans ->
    program_ok (compile ds rws ans).
  Proof.
    intros ds rws ans [Hrewrites Hanalyses]. unfold program_ok.
    change (Forall (rule_ok (lookup_sorts ds) (lookup_kind ds))
      (map compile_rule rws ++ ans)).
    apply Forall_app. split.
    - apply Forall_map. eapply Forall_impl; [|exact Hrewrites].
      intros rw [g Hrw]. eapply compile_rule_sorted; exact Hrw.
    - eapply Forall_impl; [|exact Hanalyses]. intros r [Hrule Hactions]. exact Hrule.
  Qed.

  Lemma compile_valid : forall (M : model (V := V.t)) ds rws ans, rules_ok ds rws ans ->
    Forall (valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds)) rws ->
    Forall (rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds)) ans ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    valid_sorted V.prim V.merge M (compile ds rws ans).
  Proof. Admitted. (* STUB *)

  Lemma flatten_complete : forall ds w rw g tau c e,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g -> canonical_view w ->
    instantiates tau (lhs V.t rw) e -> represents w (Id c) e ->
    cond_in_view w tau (cond V.t rw) ->
    exists s j, matches V.prim w (flatten_lhs rw) s /\ represents_on g w tau s /\
      s (root_var rw) = Some (Id j) /\ same w c j /\
      exists f k, row w f k (Some (Id j)).
  Proof.
    intros ds w rw g tau c e Hrw Hcanonical Hunfold Hrep [base [Hsubst Hcond]].
    pose proof Hrw as Hrw_all.
    destruct Hrw as [g0 [Hroot [Hleft [Hscope [Hquery Hright]]]]].
    destruct (pattern_cell_table _ _ g0 (lhs V.t rw) tau w c e
      Hcanonical Hleft Hunfold Hrep) as [cs [Hlength Hall]].
    set (ts := fst (pattern_table (lhs V.t rw) (root_var rw))).
    assert (Hcompatible : table_compatible ts cs).
    { apply (pattern_table_compatible (lhs V.t rw) (root_var rw) w tau cs
        Hcanonical); [|exact Hall]. intros h Hin. exact (root_var_hole rw h Hin). }
    assert (Hvalues : terms_value (table_bind ts cs base) ts cs).
    { apply table_bind_values; [|exact Hcompatible |].
      - destruct (pattern_table_facts (lhs V.t rw) (root_var rw)) as [Hforms Hrest].
        pose proof (Forall2_length Hforms). unfold ts. lia.
      - exact (pattern_table_literals (lhs V.t rw) (root_var rw) w tau cs Hall). }
    destruct (pattern_root_row (lhs V.t rw) w tau cs c e Hcanonical Hroot
      Hunfold Hrep Hlength Hall) as [j [Hrootcell [Hsame Hrow]]].
    exists (table_bind ts cs base), j. split.
    - assert (Hflat : flatten_lhs rw =
        pattern_atoms (nodes V.t (lhs V.t rw)) ts ts ++ cond V.t rw).
      { unfold ts. destruct rw as [[ns r] rp conditions]. reflexivity. }
      rewrite Hflat. apply Forall_app. split.
      + apply pattern_atoms_match. intros i f children t Hnode Hterm.
        exact (pattern_atom_holds (lhs V.t rw) (root_var rw) w tau cs _
          Hcanonical Hlength Hvalues Hall i f children t Hnode Hterm).
      + apply Forall_forall. intros a Hin.
        assert (Hatom : atom_holds V.prim w base a).
        { apply (proj1 (Forall_forall _ _) Hcond a Hin). }
        apply (atom_holds_agrees w base _ a); [|exact Hatom].
        apply (pattern_atom_agrees (lhs V.t rw) (root_var rw) w tau cs base a
          Hcanonical Hsubst Hatom Hall).
        intros x Hvar. exact (proj2 (proj2 (root_var_bounds rw)) a x Hin Hvar).
    - split.
      + apply (pattern_bind_represents (lhs V.t rw) (root_var rw) w tau cs base g
          Hsubst Hall).
        intros h t Hsort. exact (rewrite_context_bound ds rw g Hrw_all h t Hsort).
      + split.
        * exact (table_bind_at _ ts cs base Hcompatible (root V.t (lhs V.t rw))
            (root_var rw) (Id j) (pattern_table_root _ _ Hroot) Hrootcell).
        * split; assumption.
  Qed.

  Lemma present_represents : forall ds w rw g s tau c r,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    view_sorted (lookup_sorts ds) w -> (forall f, kind w f = lookup_kind ds f) ->
    canonical_view w -> matches V.prim w (flatten_lhs rw) s ->
    s (root_var rw) = Some (Id c) -> represents_on g w tau s ->
    instantiates tau (rhs V.t rw) r ->
    present V.prim V.merge w s (actions V.t (compile_rule rw)) ->
    represents w (Id c) r.
  Proof. Admitted. (* STUB *)

End Compile.

Module CompileT (V : VALUE_T) <: COMPILE_ALL V.
  Include Compile V.
  TimeFun root_var.
  TimeFun flatten_pat.
  TimeFun flatten_lhs.
  TimeFun compile_rule.
  TimeFun compile.
  Definition c_compile : N := 1. (* STUB *)
  Definition k_compile : N := 1. (* STUB *)
  Lemma T_compile_le : forall ds rws ans,
    (T_compile ds rws ans <= c_compile *
      N.of_nat (fold_right (fun rw n => (rewrite_size rw + n)%nat) 0 rws +
        length ans + 1)%nat)%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_compile_rule_valid : forall (M : model (V := V.t)) ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    valid_rw V.prim M (lookup_sorts ds) (lookup_kind ds) rw ->
    rule_valid_sorted V.prim M (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof. Admitted. (* STUB *)

  Lemma F2_compile_rule_sorted : forall ds rw g,
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    rule_ok (lookup_sorts ds) (lookup_kind ds) (compile_rule rw).
  Proof.
    exact compile_rule_sorted.
  Qed.

  Lemma F3_flatten_spec : forall rw,
    flatten_lhs rw = flatten_pat (lhs V.t rw) (root_var rw) ++ cond V.t rw.
  Proof.
    intros [lp rp conditions]. reflexivity.
  Qed.

  Lemma T1_compile_split : forall ds rws ans,
    (T_compile ds rws ans <= fold_right (fun rw n => T_compile_rule rw + n) 0 rws +
      k_compile * N.of_nat (length rws + length ans + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_compile_rule_le : forall rw,
    (T_compile_rule rw <= k_compile * N.of_nat (rewrite_size rw + 1))%N.
  Proof. Admitted. (* STUB *)

  (** The compiled rule's bit size is bounded by the square of its rewrite size. *)
  Lemma compile_rule_bits : forall rw,
    (N.of_nat (rule_bits (compile_rule rw)) <=
      c_compile * N.of_nat (rewrite_size rw + 1) * N.of_nat (rewrite_size rw + 1))%N.
  Proof. Admitted. (* STUB *)
End CompileT.
