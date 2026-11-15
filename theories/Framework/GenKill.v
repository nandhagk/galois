(** * Gen/kill analyses

    This file constructs may and must lattices and dense transfers.
    For example, a generated fact survives a simultaneous kill.
    Builds on: Framework.GenKillSig and Framework.Dense. *)

From Stdlib Require Import List Bool NArith Arith Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import KeySig SetSig.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import DenseSig Dense GenKillSig.

Module GenKillMayDomainCode (F : KEY_OPS) (S : SET_OPS F)
    <: GENKILL_MAY_DOMAIN_OPS F S.
  Definition t := S.t.
  Definition leb := S.subset.
  Definition bot := S.empty.
  Definition is_bot x := S.subset x S.empty.
  Definition join := S.union.
End GenKillMayDomainCode.

Module GenKillMustDomainCode (F : KEY_OPS) (S : SET_OPS F)
    <: GENKILL_MUST_DOMAIN_OPS F S.
  Definition t := option S.t.
  Definition leb := genkill_must_leb S.subset.
  Definition bot : t := None.
  Definition is_bot (x : t) := match x with None => true | Some _ => false end.
  Definition join := genkill_must_join S.inter.
End GenKillMustDomainCode.

Module GenKillMayFlowCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN_OPS F S) <: GENKILL_MAY_FLOW_OPS P N E F S G L.
  Definition dir := G.dir.
  Definition boundary p (_ : N.t) := G.init p.
  Definition transfer p e a := S.union (G.gen p e) (S.diff a (G.kill p e)).
End GenKillMayFlowCode.

Module GenKillMustFlowCode (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN_OPS F S) <: GENKILL_MUST_FLOW_OPS P N E F S G L.
  Definition dir := G.dir.
  Definition boundary p (_ : N.t) := Some (G.init p).
  Definition transfer p e (a : option S.t) :=
    match a with
    | None => None
    | Some facts => Some (S.union (G.gen p e) (S.diff facts (G.kill p e)))
    end.
End GenKillMustFlowCode.

Module GenKillMayDomain (F : KEY) (S : SET F) <: GENKILL_MAY_DOMAIN F S.
  Include GenKillMayDomainCode F S.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intro a; apply S.subset_spec; intros p Hp; exact Hp.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros a b c Hab Hbc; apply S.subset_spec.
    unfold leb in Hab, Hbc.
    rewrite S.subset_spec in Hab; rewrite S.subset_spec in Hbc.
    intros p Hp; apply Hbc, Hab; exact Hp.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a; apply S.subset_spec; intros p Hp.
    rewrite S.has_empty in Hp; discriminate.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    apply leb_refl.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros a b Ha; eapply leb_trans; [exact Ha|apply bot_least].
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros a b; apply S.subset_spec; intros p Hp.
    rewrite S.has_union, Hp; reflexivity.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros a b; apply S.subset_spec; intros p Hp.
    rewrite S.has_union, Hp; apply orb_true_r.
  Qed.
End GenKillMayDomain.

Module GenKillMustDomain (F : KEY) (S : SET F) <: GENKILL_MUST_DOMAIN F S.
  Include GenKillMustDomainCode F S.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [a|]; [|reflexivity].
    apply S.subset_spec; intros p Hp; exact Hp.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [leb genkill_must_leb];
      try discriminate; try reflexivity.
    intros Hab Hbc; apply S.subset_spec.
    rewrite S.subset_spec in Hab; rewrite S.subset_spec in Hbc.
    intros p Hp; apply Hab, Hbc; exact Hp.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intro a; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [a|] b Ha; [discriminate|reflexivity].
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [leb join genkill_must_leb genkill_must_join];
      try reflexivity.
    - apply S.subset_spec; intros p Hp.
      rewrite S.has_inter in Hp; apply andb_true_iff in Hp; exact (proj1 Hp).
    - apply S.subset_spec; intros p Hp; exact Hp.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [leb join genkill_must_leb genkill_must_join];
      try reflexivity.
    - apply S.subset_spec; intros p Hp.
      rewrite S.has_inter in Hp; apply andb_true_iff in Hp; exact (proj2 Hp).
    - apply S.subset_spec; intros p Hp; exact Hp.
  Qed.
End GenKillMustDomain.

Module GenKillMayCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN_OPS F S) (T : GENKILL_MAY_FLOW_OPS P N E F S G L)
    <: SYSTEM_OPS L.
  Include DenseCode P N E C L T.
End GenKillMayCode.

Module GenKillMustCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY_OPS) (S : SET_OPS F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN_OPS F S) (T : GENKILL_MUST_FLOW_OPS P N E F S G L)
    <: SYSTEM_OPS L.
  Include DenseCode P N E C L T.
End GenKillMustCode.

Module GenKillMay (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MAY_DOMAIN F S) (T : GENKILL_MAY_FLOW_OPS P N E F S G L)
    <: GENKILL_MAY P N E C F S G L T.
  Include Dense P N E C L T.
End GenKillMay.

Module GenKillMust (P : TYPE) (N : KEY) (E : TYPE) (C : CFG_OPS P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (L : GENKILL_MUST_DOMAIN F S) (T : GENKILL_MUST_FLOW_OPS P N E F S G L)
    <: GENKILL_MUST P N E C F S G L T.
  Include Dense P N E C L T.
End GenKillMust.

Module GenKillSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (F : KEY) (S : SET F) (G : GENKILL_OPS P E F S)
    (ML : GENKILL_MAY_DOMAIN_OPS F S) (UL : GENKILL_MUST_DOMAIN_OPS F S)
    (MT : GENKILL_MAY_FLOW_OPS P N E F S G ML)
    (UT : GENKILL_MUST_FLOW_OPS P N E F S G UL)
    (May : DENSE_SYSTEM P N E C ML MT) (Must : DENSE_SYSTEM P N E C UL UT)
    <: GENKILL_SOUND P N E C F S G ML UL MT UT May Must.
  Definition route p entry path n := genkill_route (C.edges p)
    (fun e => match G.dir with Forward => C.src p e | Backward => C.dst p e end)
    (fun e => match G.dir with Forward => C.dst p e | Backward => C.src p e end)
    entry path n.
  Definition path_facts p path :=
    genkill_path S.union S.diff (G.gen p) (G.kill p) (G.init p) path.
  Definition produces p n d := exists root initial path,
    genkill_may_start (C.nodes p) (C.entries p) S.empty (G.init p) root initial /\
    route p root path n /\
    S.mem d (genkill_path S.union S.diff (G.gen p) (G.kill p) initial path) = true.

  (** Set inclusion transports membership without a representation invariant. *)
  Lemma subset_mem : forall a b d, S.subset a b = true ->
    S.mem d a = true -> S.mem d b = true.
  Proof.
    intros a b d Hab Hd; rewrite !S.mem_has in *.
    rewrite S.subset_spec in Hab; apply Hab; exact Hd.
  Qed.

  (** Set inclusion composes through the same intermediate set. *)
  Lemma subset_trans : forall a b c, S.subset a b = true ->
    S.subset b c = true -> S.subset a c = true.
  Proof.
    intros a b c Hab Hbc; apply S.subset_spec.
    rewrite S.subset_spec in Hab; rewrite S.subset_spec in Hbc.
    intros q Hq; apply Hbc, Hab; exact Hq.
  Qed.

  (** A gen/kill transfer preserves inclusion of its incoming facts. *)
  Lemma transfer_subset : forall p e a b, S.subset a b = true ->
    S.subset (S.union (G.gen p e) (S.diff a (G.kill p e)))
      (S.union (G.gen p e) (S.diff b (G.kill p e))) = true.
  Proof.
    intros p e a b Hab; apply S.subset_spec.
    rewrite S.subset_spec in Hab; intros q Hq.
    rewrite !S.has_union, !S.has_diff in *.
    apply orb_true_iff in Hq; apply orb_true_iff.
    destruct Hq as [Hgen|Hkeep]; [left; exact Hgen|right].
    apply andb_true_iff in Hkeep; apply andb_true_iff.
    split; [apply Hab; exact (proj1 Hkeep)|exact (proj2 Hkeep)].
  Qed.

  (** A may post-solution includes each actual boundary. *)
  Lemma may_seed_closed : forall p look n, May.post_solution p look ->
    In n (C.entries p) -> S.subset (G.init p) (look n) = true.
  Proof.
    intros p look n Hpost Hentry.
    assert (Hrow : In (Seed n) (May.rows p)).
    { rewrite May.rows_spec; apply in_or_app; left; apply in_map; exact Hentry. }
    specialize (Hpost _ Hrow).
    rewrite May.eval_seed, May.target_seed in Hpost.
    cbn [row_ok forallb] in Hpost; rewrite andb_true_r in Hpost; exact Hpost.
  Qed.

  (** A may post-solution includes every listed directional transfer. *)
  Lemma may_flow_closed : forall p look e, May.post_solution p look ->
    In e (C.edges p) ->
    S.subset (S.union (G.gen p e)
      (S.diff (look (match G.dir with Forward => C.src p e | Backward => C.dst p e end))
        (G.kill p e)))
      (look (match G.dir with Forward => C.dst p e | Backward => C.src p e end)) = true.
  Proof.
    intros p look e Hpost Hedge.
    assert (Hrow : In (Flow e) (May.rows p)).
    { rewrite May.rows_spec; apply in_or_app; right; apply in_map; exact Hedge. }
    specialize (Hpost _ Hrow).
    rewrite May.eval_flow, May.target_flow in Hpost.
    cbn [row_ok forallb] in Hpost; rewrite andb_true_r in Hpost; exact Hpost.
  Qed.

  (** Initial inclusion propagates along every route of a may post-solution. *)
  Lemma may_route_bound : forall p look root path n, May.post_solution p look ->
    route p root path n -> forall initial, S.subset initial (look root) = true ->
    S.subset (genkill_path S.union S.diff (G.gen p) (G.kill p) initial path)
      (look n) = true.
  Proof.
    intros p look root path n Hpost Hroute.
    induction Hroute as [n|e es n Hedge Hroute IH]; intros initial Hinitial.
    - exact Hinitial.
    - cbn [genkill_path fold_left]; apply IH.
      eapply subset_trans; [apply transfer_subset; exact Hinitial|].
      apply may_flow_closed; assumption.
  Qed.

  (** Must inclusion composes in the reversed set order. *)
  Lemma must_order_trans : forall a b c,
    genkill_must_leb S.subset a b = true ->
    genkill_must_leb S.subset b c = true ->
    genkill_must_leb S.subset a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [genkill_must_leb];
      try discriminate; try reflexivity.
    intros Hab Hbc; eapply subset_trans; [exact Hbc|exact Hab].
  Qed.

  (** The strict must transfer preserves the reversed set order. *)
  Lemma must_transfer_mono : forall p e a b,
    genkill_must_leb S.subset a b = true ->
    genkill_must_leb S.subset (UT.transfer p e a) (UT.transfer p e b) = true.
  Proof.
    intros p e [a|] [b|]; cbn [UT.transfer genkill_must_leb];
      try discriminate; try reflexivity.
    apply transfer_subset.
  Qed.

  (** Every actual boundary forces a reached must value. *)
  Lemma must_seed_closed : forall p look n, Must.post_solution p look ->
    In n (C.entries p) ->
    genkill_must_leb S.subset (Some (G.init p)) (look n) = true.
  Proof.
    intros p look n Hpost Hentry.
    assert (Hrow : In (Seed n) (Must.rows p)).
    { rewrite Must.rows_spec; apply in_or_app; left; apply in_map; exact Hentry. }
    specialize (Hpost _ Hrow).
    rewrite Must.eval_seed, Must.target_seed in Hpost.
    cbn [row_ok forallb] in Hpost; rewrite andb_true_r in Hpost; exact Hpost.
  Qed.

  (** A must post-solution accepts every listed directional transfer. *)
  Lemma must_flow_closed : forall p look e, Must.post_solution p look ->
    In e (C.edges p) ->
    genkill_must_leb S.subset
      (UT.transfer p e
        (look (match G.dir with Forward => C.src p e | Backward => C.dst p e end)))
      (look (match G.dir with Forward => C.dst p e | Backward => C.src p e end)) = true.
  Proof.
    intros p look e Hpost Hedge.
    assert (Hrow : In (Flow e) (Must.rows p)).
    { rewrite Must.rows_spec; apply in_or_app; right; apply in_map; exact Hedge. }
    specialize (Hpost _ Hrow).
    rewrite Must.eval_flow, Must.target_flow in Hpost.
    cbn [row_ok forallb] in Hpost; rewrite andb_true_r in Hpost; exact Hpost.
  Qed.

  (** A reached path value bounds the must result at the route endpoint. *)
  Lemma must_route_bound : forall p look root path n, Must.post_solution p look ->
    route p root path n -> forall initial,
    genkill_must_leb S.subset (Some initial) (look root) = true ->
    genkill_must_leb S.subset
      (Some (genkill_path S.union S.diff (G.gen p) (G.kill p) initial path))
      (look n) = true.
  Proof.
    intros p look root path n Hpost Hroute.
    induction Hroute as [n|e es n Hedge Hroute IH]; intros initial Hinitial.
    - exact Hinitial.
    - cbn [genkill_path fold_left]; apply IH.
      eapply must_order_trans; [|apply must_flow_closed; eassumption].
      apply (must_transfer_mono p e (Some initial)); exact Hinitial.
  Qed.

  (** Every produced path fact belongs to a may post-solution. *)
  Lemma may_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall n d, produces p n d -> S.mem d (look n) = true.
  Proof.
    intros p look Hmay Hpost n d [root [initial [path [Hstart [Hroute Hd]]]]].
    eapply subset_mem; [eapply may_route_bound; [exact Hpost|exact Hroute|]|exact Hd].
    destruct Hstart as [root Hroot|root Hentry].
    - apply S.subset_spec; intros q Hq; rewrite S.has_empty in Hq; discriminate.
    - apply may_seed_closed; assumption.
  Qed.
  (** Every fact generated on an actual boundary path belongs to a may post-solution. *)
  Lemma may_boundary_covers : forall p look, G.may = true -> May.post_solution p look ->
    forall entry path n d, In entry (C.entries p) -> route p entry path n ->
      S.mem d (path_facts p path) = true -> S.mem d (look n) = true.
  Proof.
    intros p look Hmay Hpost entry path n d Hentry Hroute Hd.
    eapply may_covers; [exact Hmay|exact Hpost|].
    exists entry, (G.init p), path; split.
    - apply Genkill_boundary; exact Hentry.
    - split; assumption.
  Qed.
  (** A reached must post-solution contains facts present on every boundary path. *)
  Lemma must_covers : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n facts d, In entry (C.entries p) -> route p entry path n ->
      look n = Some facts -> S.mem d facts = true -> S.mem d (path_facts p path) = true.
  Proof.
    intros p look Hmust Hpost entry path n facts d Hentry Hroute Hlook Hd.
    pose proof (must_route_bound p look entry path n Hpost Hroute (G.init p)
      (must_seed_closed p look entry Hpost Hentry)) as Hbound.
    rewrite Hlook in Hbound; eapply subset_mem; [exact Hbound|exact Hd].
  Qed.
  (** A boundary path has a reached must value in every post-solution. *)
  Lemma must_reached : forall p look, G.may = false -> Must.post_solution p look ->
    forall entry path n, In entry (C.entries p) -> route p entry path n ->
      exists facts, look n = Some facts.
  Proof.
    intros p look Hmust Hpost entry path n Hentry Hroute.
    pose proof (must_route_bound p look entry path n Hpost Hroute (G.init p)
      (must_seed_closed p look entry Hpost Hentry)) as Hbound.
    destruct (look n) as [facts|]; [exists facts; reflexivity|discriminate].
  Qed.

  (** Pointwise Boolean growth cannot reduce the number of listed true values. *)
  Local Lemma count_mono {A} (xs : list A) (b c : A -> bool) :
    (forall x, In x xs -> b x = true -> c x = true) ->
    length (filter b xs) <= length (filter c xs).
  Proof.
    induction xs as [|x xs IH]; intro Hbc; cbn; [lia|].
    assert (Htail : length (filter b xs) <= length (filter c xs)).
    { apply IH; intros y Hy; apply Hbc; right; exact Hy. }
    specialize (Hbc x (or_introl eq_refl)).
    destruct (b x), (c x); cbn in *; try discriminate; lia.
  Qed.

  (** Boolean growth with unchanged finite count leaves every listed value unchanged. *)
  Local Lemma count_equal {A} (xs : list A) (b c : A -> bool) :
    (forall x, In x xs -> b x = true -> c x = true) ->
    length (filter b xs) = length (filter c xs) ->
    forall x, In x xs -> b x = c x.
  Proof.
    induction xs as [|a xs IH]; intros Hbc Hcount x Hx; [contradiction|].
    assert (Htail : forall y, In y xs -> b y = true -> c y = true).
    { intros y Hy; apply Hbc; right; exact Hy. }
    pose proof (count_mono xs b c Htail) as Hle.
    specialize (Hbc a (or_introl eq_refl)); cbn in Hcount.
    destruct (b a) eqn:Hb, (c a) eqn:Hc; cbn in Hcount;
      try discriminate; try (exfalso; lia).
    - destruct Hx as [<-|Hx]; [rewrite Hb, Hc; reflexivity|].
      apply IH; [exact Htail|lia|exact Hx].
    - destruct Hx as [<-|Hx]; [rewrite Hb, Hc; reflexivity|].
      apply IH; [exact Htail|lia|exact Hx].
  Qed.

  (** An inflationary Boolean operator reaches a closed finite observation with its invariant. *)
  Local Lemma finite_closure {A} (xs : list A)
      (step : (A -> bool) -> A -> bool) (inv : (A -> bool) -> Prop) :
    (forall b x, b x = true -> step b x = true) ->
    (forall b, inv b -> inv (step b)) -> inv (fun _ => false) ->
    exists b, inv b /\ forall x, In x xs -> step b x = b x.
  Proof.
    intros Hgrow Hstep Hempty.
    assert (Hbound : forall b : A -> bool, length (filter b xs) <= length xs).
    { intro b; induction xs as [|x xs IH]; cbn; [lia|].
      destruct (b x); cbn; lia. }
    assert (Hsearch : forall k b, length xs - length (filter b xs) <= k -> inv b ->
      exists c, inv c /\ forall x, In x xs -> step c x = c x).
    { induction k as [|k IH]; intros b Hcapacity Hb.
      - pose proof (Hbound (step b)) as Hstep_bound.
        pose proof (count_mono xs b (step b) (fun x _ => Hgrow b x)) as Hgrowth.
        exists b; split; [exact Hb|]; intros x Hx; symmetry.
        apply (count_equal xs b (step b)); [intros y _; apply Hgrow|lia|exact Hx].
      - pose proof (Hbound (step b)) as Hstep_bound.
        pose proof (count_mono xs b (step b) (fun x _ => Hgrow b x)) as Hgrowth.
        destruct (Nat.eq_dec (length (filter b xs)) (length (filter (step b) xs)))
          as [Heq|Hne].
        + exists b; split; [exact Hb|]; intros x Hx; symmetry.
          apply (count_equal xs b (step b)); [intros y _; apply Hgrow|exact Heq|exact Hx].
        + apply (IH (step b)); [lia|apply Hstep; exact Hb]. }
    apply (Hsearch (length xs) (fun _ => false)); [lia|exact Hempty].
  Qed.

  Local Definition source p e :=
    match G.dir with Forward => C.src p e | Backward => C.dst p e end.
  Local Definition destination p e :=
    match G.dir with Forward => C.dst p e | Backward => C.src p e end.

  (** A well-formed listed edge has both directional endpoints in the node inventory. *)
  Local Lemma edge_nodes : forall p e, C.wf p -> In e (C.edges p) ->
    In (source p e) (C.nodes p) /\ In (destination p e) (C.nodes p).
  Proof.
    intros p e Hwf He; pose proof (C.edges_nodes p e Hwf He) as Hnodes.
    unfold source, destination; destruct G.dir; tauto.
  Qed.

  (** Appending one listed edge extends a route at its actual endpoint. *)
  Local Lemma route_snoc : forall p root path n e, route p root path n ->
    In e (C.edges p) -> source p e = n ->
    route p root (path ++ e :: nil) (destination p e).
  Proof.
    intros p root path n e Hroute He Hend.
    induction Hroute as [n|edge path n Hedge Hroute IH].
    - cbn [app]; rewrite <- Hend; constructor; [exact He|constructor].
    - cbn [app]; eapply Genkill_next with (e := edge); [exact Hedge|].
      apply IH; exact Hend.
  Qed.

  (** Path transfer applies an appended edge after the complete prefix. *)
  Local Lemma path_snoc : forall p initial path e,
    genkill_path S.union S.diff (G.gen p) (G.kill p) initial (path ++ e :: nil) =
    S.union (G.gen p e)
      (S.diff (genkill_path S.union S.diff (G.gen p) (G.kill p) initial path)
        (G.kill p e)).
  Proof.
    intros p initial path e; unfold genkill_path; rewrite fold_left_app; reflexivity.
  Qed.

  (** Every boundary member has a zero-edge production witness. *)
  Local Lemma produces_seed : forall p n d, In n (C.entries p) ->
    S.mem d (G.init p) = true -> produces p n d.
  Proof.
    intros p n d Hentry Hd; exists n, (G.init p), nil; split.
    - apply Genkill_boundary; exact Hentry.
    - split; [constructor|exact Hd].
  Qed.

  (** A generated fact or an un-killed produced fact has an extended production witness. *)
  Local Lemma produces_step : forall p e d, C.wf p -> In e (C.edges p) ->
    (S.mem d (G.gen p e) = true \/
      (produces p (source p e) d /\ S.mem d (G.kill p e) = false)) ->
    produces p (destination p e) d.
  Proof.
    intros p e d Hwf He [Hgen|[Hproduce Hkill]].
    - exists (source p e), S.empty, (e :: nil); split.
      + apply Genkill_empty; exact (proj1 (edge_nodes p e Hwf He)).
      + split; [constructor; [exact He|constructor]|].
        cbn [genkill_path fold_left]; rewrite S.mem_union, Hgen; reflexivity.
    - destruct Hproduce as [root [initial [path [Hstart [Hroute Hd]]]]].
      exists root, initial, (path ++ e :: nil); split; [exact Hstart|]; split.
      + apply route_snoc with (n := source p e); [exact Hroute|exact He|reflexivity].
      + rewrite path_snoc, S.mem_union, S.mem_diff, Hd, Hkill.
        apply orb_true_r.
  Qed.

  (** The client's equality test recognizes exactly equal graph nodes. *)
  Local Lemma node_eqb_true : forall a b, N.eqb a b = true <-> a = b.
  Proof.
    intros a b; destruct (N.eqb_spec a b) as [Heq|Hne]; intuition discriminate.
  Qed.

  (** Boolean entry membership agrees with the listed boundary nodes. *)
  Local Lemma entryb_spec : forall p n,
    existsb (N.eqb n) (C.entries p) = true <-> In n (C.entries p).
  Proof.
    intros p n; rewrite existsb_exists; split.
    - intros [root [Hroot Heq]]; apply node_eqb_true in Heq; now subst root.
    - intro Hn; exists n; split; [exact Hn|apply node_eqb_true; reflexivity].
  Qed.

  (* This finite Boolean closure is proof-only separation evidence, not an executable solver. *)
  Local Definition may_close p d (b : N.t -> bool) n :=
    b n || (existsb (N.eqb n) (C.entries p) && S.mem d (G.init p)) ||
    existsb (fun e => N.eqb n (destination p e) &&
      (S.mem d (G.gen p e) || (b (source p e) && negb (S.mem d (G.kill p e)))))
      (C.edges p).

  (** One Boolean closure round records existing, boundary, and transferred production. *)
  Local Lemma may_close_spec : forall p d b n, may_close p d b n = true <->
    b n = true \/ (In n (C.entries p) /\ S.mem d (G.init p) = true) \/
    exists e, In e (C.edges p) /\ n = destination p e /\
      (S.mem d (G.gen p e) = true \/
        (b (source p e) = true /\ S.mem d (G.kill p e) = false)).
  Proof.
    intros p d b n; unfold may_close.
    rewrite !orb_true_iff, andb_true_iff, entryb_spec, existsb_exists.
    setoid_rewrite andb_true_iff; setoid_rewrite node_eqb_true.
    setoid_rewrite orb_true_iff; setoid_rewrite andb_true_iff.
    setoid_rewrite negb_true_iff; tauto.
  Qed.

  (** Finite closure supplies a decidable subset of production closed at every listed node. *)
  Local Lemma may_closure : forall p d, C.wf p ->
    exists b, (forall n, b n = true -> produces p n d) /\
      forall n, In n (C.nodes p) -> may_close p d b n = b n.
  Proof.
    intros p d Hwf; apply (finite_closure (C.nodes p) (may_close p d)
      (fun b => forall n, b n = true -> produces p n d)).
    - intros b n Hb; apply may_close_spec; left; exact Hb.
    - intros b Hb n Hn; apply may_close_spec in Hn.
      destruct Hn as [Hn|[[Hentry Hd]|[e [He [-> Hflow]]]]].
      + apply Hb; exact Hn.
      + apply produces_seed; assumption.
      + apply produces_step; [exact Hwf|exact He|].
        destruct Hflow as [Hgen|[Hsource Hkill]]; [left; exact Hgen|right].
        split; [apply Hb; exact Hsource|exact Hkill].
    - intros n Hbad; discriminate.
  Qed.

  Local Definition may_candidate d (b : N.t -> bool) (look : N.t -> S.t) n :=
    if b n then look n else S.remove d (look n).

  (** Removing one selected fact never adds an encoded member. *)
  Local Lemma candidate_subset : forall d b look n,
    S.subset (may_candidate d b look n) (look n) = true.
  Proof.
    intros d b look n; apply S.subset_spec; intros q Hq.
    unfold may_candidate in Hq; destruct (b n); [exact Hq|].
    rewrite S.has_remove in Hq; apply andb_true_iff in Hq; exact (proj2 Hq).
  Qed.

  (** The selected fact survives precisely at nodes marked by the Boolean closure. *)
  Local Lemma candidate_selected : forall d b look n,
    S.mem d (may_candidate d b look n) = (S.mem d (look n) && b n).
  Proof.
    intros d b look n; unfold may_candidate; destruct (b n).
    - symmetry; apply andb_true_r.
    - rewrite S.mem_remove_same, andb_false_r; reflexivity.
  Qed.

  (** A closed Boolean mask can remove its selected fact from a may post-solution. *)
  Local Lemma may_candidate_post : forall p d b look, C.wf p ->
    May.post_solution p look ->
    (forall n, In n (C.nodes p) -> may_close p d b n = b n) ->
    May.post_solution p (may_candidate d b look).
  Proof.
    intros p d b look Hwf Hpost Hclosed r Hr.
    rewrite May.rows_spec in Hr; apply in_app_or in Hr.
    destruct Hr as [Hr|Hr]; apply in_map_iff in Hr; destruct Hr as [v [<- Hv]].
    - rewrite May.eval_seed, May.target_seed; cbn [row_ok forallb].
      rewrite andb_true_r; apply S.subset_spec; intros q Hq.
      pose proof (proj1 (S.subset_spec _ _) (may_seed_closed p look v Hpost Hv)
        q Hq) as Hlook.
      unfold may_candidate; destruct (b v) eqn:Hb; [exact Hlook|].
      rewrite S.has_remove, Hlook, andb_true_r; apply negb_true_iff, Pos.eqb_neq.
      intro Heq; subst q.
      assert (Hmarked : b v = true).
      { rewrite <- Hclosed by (apply C.entries_nodes; assumption).
        apply may_close_spec; right; left; split; [exact Hv|].
        rewrite S.mem_has; exact Hq. }
      congruence.
    - rewrite May.eval_flow, May.target_flow; cbn [row_ok forallb].
      rewrite andb_true_r; apply S.subset_spec; intros q Hq.
      assert (Hbound : S.subset
        (S.union (G.gen p v) (S.diff (may_candidate d b look (source p v))
          (G.kill p v))) (look (destination p v)) = true).
      { eapply subset_trans; [apply transfer_subset, candidate_subset|].
        apply may_flow_closed; assumption. }
      pose proof (proj1 (S.subset_spec _ _) Hbound q Hq) as Hlook.
      change (S.has q (may_candidate d b look (destination p v)) = true).
      unfold may_candidate; destruct (b (destination p v)) eqn:Hb; [exact Hlook|].
      rewrite S.has_remove, Hlook, andb_true_r; apply negb_true_iff, Pos.eqb_neq.
      intro Heq; subst q.
      assert (Hmarked : b (destination p v) = true).
      { rewrite <- Hclosed by exact (proj2 (edge_nodes p v Hwf Hv)).
        apply may_close_spec; right; right; exists v; split; [exact Hv|].
        split; [reflexivity|].
        rewrite <- S.mem_has in Hq.
        change (S.mem d (S.union (G.gen p v)
          (S.diff (may_candidate d b look (source p v)) (G.kill p v))) = true) in Hq.
        rewrite S.mem_union, S.mem_diff in Hq.
        apply orb_true_iff in Hq; destruct Hq as [Hgen|Hkeep]; [left; exact Hgen|right].
        apply andb_true_iff in Hkeep; destruct Hkeep as [Hsource Hkill].
        rewrite candidate_selected in Hsource; apply andb_true_iff in Hsource.
        split; [exact (proj2 Hsource)|apply negb_true_iff; exact Hkill]. }
      congruence.
  Qed.

  (** A least may post-solution equals production from empty listed starts and boundaries. *)
  Lemma may_exact : forall p look, C.wf p -> G.may = true -> May.post_solution p look ->
    (forall other, May.post_solution p other -> forall n, S.subset (look n) (other n) = true) ->
    forall n d, In n (C.nodes p) -> (S.mem d (look n) = true <-> produces p n d).
  Proof.
    intros p look Hwf Hmay Hpost Hleast n d Hn; split.
    - intro Hd; destruct (may_closure p d Hwf) as [b [Hsound Hclosed]].
      pose proof (Hleast _ (may_candidate_post p d b look Hwf Hpost Hclosed) n) as Hbound.
      pose proof (subset_mem _ _ d Hbound Hd) as Hcandidate.
      rewrite candidate_selected in Hcandidate; apply andb_true_iff in Hcandidate.
      apply Hsound; exact (proj2 Hcandidate).
    - apply may_covers; assumption.
  Qed.
  (** A least reached must post-solution contains exactly the facts on all boundary paths. *)
  Lemma must_exact : forall p look, C.wf p -> G.may = false -> Must.post_solution p look ->
    (forall other, Must.post_solution p other -> forall n,
      genkill_must_leb S.subset (look n) (other n) = true) ->
    forall n facts, In n (C.nodes p) -> look n = Some facts -> forall d,
      S.mem d facts = true <-> forall entry path,
        In entry (C.entries p) -> route p entry path n -> S.mem d (path_facts p path) = true.
  Proof. Admitted. (* CONVERT: must_greatest_paths: The variable must_post_keeps was not found *)
End GenKillSound.

Module GenKillMayDomainT (F : KEY_T) (S : SET_T F)
    <: GENKILL_MAY_DOMAIN_T F S.
  Include GenKillMayDomain F S.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size := S.nodes.
  Lemma size_nodes : forall a, size a = S.nodes a.
  Proof. reflexivity. Qed.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End GenKillMayDomainT.

Module GenKillMustDomainT (F : KEY_T) (S : SET_T F)
    <: GENKILL_MUST_DOMAIN_T F S.
  Include GenKillMustDomain F S.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (a : t) :=
    match a with
    | None => 0
    | Some facts => S.nodes facts
    end.
  Lemma size_nodes : forall a,
    size a = match a with None => 0 | Some facts => S.nodes facts end.
  Proof. reflexivity. Qed.
  Definition c_lat : N := 1%N. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof. Admitted. (* STUB *)
End GenKillMustDomainT.

Module GenKillMayFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MAY_DOMAIN_T F S) <: GENKILL_MAY_FLOW_T P N E F S G L.
  Include GenKillMayFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
  Definition flow_work p s := N.of_nat (G.gk_work p + s).
  Definition c_flow : N := 1%N. (* STUB *)
  Lemma flow_work_mono : forall p s t, s <= t ->
    (flow_work p s <= flow_work p t)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_boundary_le : forall p n,
    (T_boundary p n <= c_flow * (flow_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_transfer_le : forall p e a,
    (T_transfer p e a <= c_flow * (flow_work p (L.size a) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma boundary_size_le : forall p n,
    (N.of_nat (L.size (boundary p n)) <= flow_work p 0)%N.
  Proof. Admitted. (* STUB *)
  Lemma transfer_size_le : forall p e a,
    (N.of_nat (L.size (transfer p e a)) <= flow_work p (L.size a))%N.
  Proof. Admitted. (* STUB *)
End GenKillMayFlowT.

Module GenKillMustFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MUST_DOMAIN_T F S) <: GENKILL_MUST_FLOW_T P N E F S G L.
  Include GenKillMustFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
  Definition flow_work p s := N.of_nat (G.gk_work p + s).
  Definition c_flow : N := 1%N. (* STUB *)
  Lemma flow_work_mono : forall p s t, s <= t ->
    (flow_work p s <= flow_work p t)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_boundary_le : forall p n,
    (T_boundary p n <= c_flow * (flow_work p 0 + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_transfer_le : forall p e a,
    (T_transfer p e a <= c_flow * (flow_work p (L.size a) + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma boundary_size_le : forall p n,
    (N.of_nat (L.size (boundary p n)) <= flow_work p 0)%N.
  Proof. Admitted. (* STUB *)
  Lemma transfer_size_le : forall p e a,
    (N.of_nat (L.size (transfer p e a)) <= flow_work p (L.size a))%N.
  Proof. Admitted. (* STUB *)
End GenKillMustFlowT.

Module GenKillMayOperationalT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (F : KEY_T) (S : SET_T F)
    (G : GENKILL_T P E F S) (L : GENKILL_MAY_DOMAIN_T F S).
  Module Flow := GenKillMayFlowT P N E F S G L.
  Include GenKillMay P N E C F S G L Flow.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
End GenKillMayOperationalT.

Module GenKillMustOperationalT (P : TYPE) (N : KEY_T) (E : TYPE)
    (C : CFG_T P N E) (F : KEY_T) (S : SET_T F)
    (G : GENKILL_T P E F S) (L : GENKILL_MUST_DOMAIN_T F S).
  Module Flow := GenKillMustFlowT P N E F S G L.
  Include GenKillMust P N E C F S G L Flow.
  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun start.
  TimeFun resume.
  TimeFun deps.
  TimeFun sides.
End GenKillMustOperationalT.
