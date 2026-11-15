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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
  Proof. Admitted. (* STUB *)

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
