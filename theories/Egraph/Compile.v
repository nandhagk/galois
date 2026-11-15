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
