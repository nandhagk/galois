(** * Gen/kill analyses

    This file constructs may and must lattices and dense transfers.
    For example, a generated fact survives a simultaneous kill.
    Builds on: Framework.GenKillSig and Framework.Dense. *)

From Stdlib Require Import List Bool NArith Arith Lia.
From Argent Require Import Time Tactics Std BigO.
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

  Local Definition presence_states p :=
    flat_map (fun n => (n, false) :: (n, true) :: nil) (C.nodes p).

  (** Each listed node has both possible observations of the selected fact. *)
  Local Lemma presence_listed : forall p n bit, In n (C.nodes p) ->
    In (n, bit) (presence_states p).
  Proof.
    intros p n bit Hn; unfold presence_states; apply in_flat_map.
    exists n; split; [exact Hn|]; destruct bit; cbn; auto.
  Qed.

  Local Definition presence_next p d e bit :=
    S.mem d (G.gen p e) || (bit && negb (S.mem d (G.kill p e))).

  (* Both observations are retained, so unreachable nodes stay distinct from present facts. *)
  Local Definition presence_close p d (b : N.t * bool -> bool) state :=
    b state ||
    (existsb (N.eqb (fst state)) (C.entries p) &&
      Bool.eqb (S.mem d (G.init p)) (snd state)) ||
    existsb (fun e => N.eqb (fst state) (destination p e) &&
      existsb (fun bit => b (source p e, bit) &&
        Bool.eqb (presence_next p d e bit) (snd state)) (false :: true :: nil))
      (C.edges p).

  (** Presence closure records exactly old observations, boundaries, and one-edge extensions. *)
  Local Lemma presence_close_spec : forall p d b n bit,
    presence_close p d b (n, bit) = true <->
    b (n, bit) = true \/
    (In n (C.entries p) /\ S.mem d (G.init p) = bit) \/
    exists e before, In e (C.edges p) /\ n = destination p e /\
      b (source p e, before) = true /\ presence_next p d e before = bit.
  Proof.
    intros p d b n bit; unfold presence_close; cbn [fst snd].
    rewrite !orb_true_iff, andb_true_iff, entryb_spec, Bool.eqb_true_iff.
    rewrite existsb_exists; split.
    - intros [[Hold|Hseed]|[e [He Hstep]]].
      + left; exact Hold.
      + right; left; exact Hseed.
      + apply andb_true_iff in Hstep; destruct Hstep as [Hnode Hstep].
        apply node_eqb_true in Hnode; apply existsb_exists in Hstep.
        destruct Hstep as [before [_ Hbefore]]; apply andb_true_iff in Hbefore.
        destruct Hbefore as [Hmarked Hnext]; rewrite Bool.eqb_true_iff in Hnext.
        right; right; exists e, before; split; [exact He|].
        split; [exact Hnode|]; split; [exact Hmarked|exact Hnext].
    - intros [Hold|[Hseed|[e [before [He [Hnode [Hmarked Hnext]]]]]]].
      + left; left; exact Hold.
      + left; right; exact Hseed.
      + right; exists e; split; [exact He|]; apply andb_true_iff; split.
        * apply node_eqb_true; exact Hnode.
        * apply existsb_exists; exists before; split.
          -- destruct before; cbn; auto.
          -- apply andb_true_iff; split; [exact Hmarked|].
             rewrite Bool.eqb_true_iff; exact Hnext.
  Qed.

  (** Every marked presence observation has an actual finite boundary-path witness. *)
  Local Lemma presence_closure : forall p d, C.wf p -> exists b,
    (forall n bit, b (n, bit) = true -> exists entry path,
      In entry (C.entries p) /\ route p entry path n /\
      S.mem d (path_facts p path) = bit) /\
    forall state, In state (presence_states p) -> presence_close p d b state = b state.
  Proof.
    intros p d Hwf; apply (finite_closure (presence_states p) (presence_close p d)
      (fun b => forall n bit, b (n, bit) = true -> exists entry path,
        In entry (C.entries p) /\ route p entry path n /\
        S.mem d (path_facts p path) = bit)).
    - intros b [n bit] Hmarked; apply presence_close_spec; left; exact Hmarked.
    - intros b Hsound n bit Hmarked; apply presence_close_spec in Hmarked.
      destruct Hmarked as [Hold|[[Hentry Hinitial]|
        [e [before [He [-> [Hbefore Hnext]]]]]]].
      + apply Hsound; exact Hold.
      + exists n, nil; split; [exact Hentry|]; split; [constructor|exact Hinitial].
      + destruct (Hsound _ _ Hbefore) as [entry [path [Hentry [Hroute Hbit]]]].
        exists entry, (path ++ e :: nil); split; [exact Hentry|]; split.
        * apply route_snoc with (n := source p e); [exact Hroute|exact He|reflexivity].
        * unfold path_facts in *; rewrite path_snoc, S.mem_union, S.mem_diff, Hbit.
          exact Hnext.
    - intros n bit Hbad; discriminate.
  Qed.

  (** A closed observation mask marks the initial fact value at every boundary. *)
  Local Lemma presence_seed : forall p d b, C.wf p ->
    (forall state, In state (presence_states p) -> presence_close p d b state = b state) ->
    forall n, In n (C.entries p) -> b (n, S.mem d (G.init p)) = true.
  Proof.
    intros p d b Hwf Hclosed n Hentry.
    rewrite <- Hclosed by (apply presence_listed; apply C.entries_nodes; assumption).
    apply presence_close_spec; right; left; split; [exact Hentry|reflexivity].
  Qed.

  (** A closed observation mask transports each marked input through a listed edge. *)
  Local Lemma presence_edge : forall p d b, C.wf p ->
    (forall state, In state (presence_states p) -> presence_close p d b state = b state) ->
    forall e bit, In e (C.edges p) -> b (source p e, bit) = true ->
      b (destination p e, presence_next p d e bit) = true.
  Proof.
    intros p d b Hwf Hclosed e bit He Hmarked.
    rewrite <- Hclosed by (apply presence_listed; exact (proj2 (edge_nodes p e Hwf He))).
    apply presence_close_spec; right; right; exists e, bit.
    split; [exact He|]; split; [reflexivity|]; split; [exact Hmarked|reflexivity].
  Qed.

  Local Definition must_candidate d (b : N.t * bool -> bool)
      (look : N.t -> option S.t) n :=
    if b (n, false) then look n
    else if b (n, true) then option_map (S.add d) (look n) else None.

  (** Adding the selected fact preserves every old encoded member. *)
  Local Lemma subset_add : forall d facts, S.subset facts (S.add d facts) = true.
  Proof.
    intros d facts; apply S.subset_spec; intros q Hq.
    rewrite S.has_add, Hq; apply orb_true_r.
  Qed.

  (** An observed path value bounds a candidate that adds only its guaranteed selected fact. *)
  Local Lemma must_candidate_bound : forall d b look n facts bound bit,
    look n = Some facts -> S.subset facts bound = true -> b (n, bit) = true ->
    (bit = true -> S.mem d bound = true) ->
    genkill_must_leb S.subset (Some bound) (must_candidate d b look n) = true.
  Proof.
    intros d b look n facts bound bit Hlook Hbound Hmarked Hbit.
    unfold must_candidate; rewrite Hlook.
    destruct (b (n, false)) eqn:Hfalse; [exact Hbound|].
    destruct bit; [|congruence]; rewrite Hmarked; cbn [option_map genkill_must_leb].
    apply S.subset_spec; intros q Hq; rewrite S.has_add in Hq.
    apply orb_true_iff in Hq; destruct Hq as [Heq|Hq].
    - apply Pos.eqb_eq in Heq; subst q; rewrite <- S.mem_has; apply Hbit; reflexivity.
    - exact (proj1 (S.subset_spec _ _) Hbound q Hq).
  Qed.

  (** The candidate accepts every initial must constraint. *)
  Local Lemma must_candidate_seed : forall p d b look, C.wf p ->
    Must.post_solution p look ->
    (forall state, In state (presence_states p) -> presence_close p d b state = b state) ->
    forall n, In n (C.entries p) ->
      genkill_must_leb S.subset (Some (G.init p)) (must_candidate d b look n) = true.
  Proof.
    intros p d b look Hwf Hpost Hclosed n Hentry.
    pose proof (must_seed_closed p look n Hpost Hentry) as Hseed.
    destruct (look n) as [facts|] eqn:Hlook; [|discriminate].
    eapply must_candidate_bound with (facts := facts) (bit := S.mem d (G.init p)).
    - exact Hlook.
    - exact Hseed.
    - apply presence_seed; assumption.
    - intro Hbit; exact Hbit.
  Qed.

  (** A marked source observation ensures the candidate accepts its transfer constraint. *)
  Local Lemma must_candidate_flow : forall p d b look, C.wf p ->
    Must.post_solution p look ->
    (forall state, In state (presence_states p) -> presence_close p d b state = b state) ->
    forall e, In e (C.edges p) ->
      genkill_must_leb S.subset
        (UT.transfer p e (must_candidate d b look (source p e)))
        (must_candidate d b look (destination p e)) = true.
  Proof.
    intros p d b look Hwf Hpost Hclosed e He.
    pose proof (must_flow_closed p look e Hpost He) as Hflow.
    change (genkill_must_leb S.subset (UT.transfer p e (look (source p e)))
      (look (destination p e)) = true) in Hflow.
    destruct (look (source p e)) as [facts|] eqn:Hsource.
    - destruct (look (destination p e)) as [target_facts|] eqn:Htarget;
        [|discriminate].
      change (S.subset target_facts
        (S.union (G.gen p e) (S.diff facts (G.kill p e))) = true) in Hflow.
      destruct (b (source p e, false)) eqn:Hfalse.
      + unfold must_candidate at 1; rewrite Hfalse, Hsource.
        eapply must_candidate_bound with (facts := target_facts)
          (bit := presence_next p d e false).
        * exact Htarget.
        * exact Hflow.
        * apply presence_edge; assumption.
        * intro Hbit; unfold presence_next in Hbit; cbn [andb] in Hbit.
          rewrite orb_false_r in Hbit; rewrite S.mem_union, Hbit; reflexivity.
      + destruct (b (source p e, true)) eqn:Htrue.
        * unfold must_candidate at 1; rewrite Hfalse, Htrue, Hsource.
          eapply must_candidate_bound with (facts := target_facts)
            (bit := presence_next p d e true).
          -- exact Htarget.
          -- eapply subset_trans; [exact Hflow|apply transfer_subset, subset_add].
          -- apply presence_edge; assumption.
          -- intro Hbit; rewrite S.mem_union, S.mem_diff, S.mem_add_same; exact Hbit.
        * unfold must_candidate at 1; rewrite Hfalse, Htrue; reflexivity.
    - unfold must_candidate at 1; rewrite Hsource.
      destruct (b (source p e, false)), (b (source p e, true)); reflexivity.
  Qed.

  (** The presence mask yields a must post-solution that adds every unrefuted selected fact. *)
  Local Lemma must_candidate_post : forall p d b look, C.wf p ->
    Must.post_solution p look ->
    (forall state, In state (presence_states p) -> presence_close p d b state = b state) ->
    Must.post_solution p (must_candidate d b look).
  Proof.
    intros p d b look Hwf Hpost Hclosed r Hr.
    rewrite Must.rows_spec in Hr; apply in_app_or in Hr.
    destruct Hr as [Hr|Hr]; apply in_map_iff in Hr; destruct Hr as [v [<- Hv]].
    - rewrite Must.eval_seed, Must.target_seed; cbn [row_ok forallb].
      rewrite andb_true_r; apply must_candidate_seed; assumption.
    - rewrite Must.eval_flow, Must.target_flow; cbn [row_ok forallb].
      rewrite andb_true_r; apply must_candidate_flow; assumption.
  Qed.

  (** A least reached must post-solution contains exactly the facts on all boundary paths. *)
  Lemma must_exact : forall p look, C.wf p -> G.may = false -> Must.post_solution p look ->
    (forall other, Must.post_solution p other -> forall n,
      genkill_must_leb S.subset (look n) (other n) = true) ->
    forall n facts, In n (C.nodes p) -> look n = Some facts -> forall d,
      S.mem d facts = true <-> forall entry path,
        In entry (C.entries p) -> route p entry path n -> S.mem d (path_facts p path) = true.
  Proof.
    intros p look Hwf Hmust Hpost Hleast n facts Hn Hlook d; split.
    - intros Hd entry path Hentry Hroute.
      eapply must_covers; eassumption.
    - intro Hall; destruct (presence_closure p d Hwf) as [b [Hsound Hclosed]].
      pose proof (Hleast _ (must_candidate_post p d b look Hwf Hpost Hclosed) n) as Hbound.
      unfold must_candidate in Hbound; rewrite Hlook in Hbound.
      destruct (b (n, false)) eqn:Hfalse.
      + destruct (Hsound n false Hfalse) as [entry [path [Hentry [Hroute Hmissing]]]].
        specialize (Hall entry path Hentry Hroute); congruence.
      + destruct (b (n, true)); [|discriminate].
        eapply subset_mem; [exact Hbound|apply S.mem_add_same].
  Qed.
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
  Definition c_lat : N := (S.c_set + 8)%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat; lia.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; pose proof (S.T_subset_le a b) as Htime.
    unfold size, c_lat; time_unfold @T_leb; nia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b; pose proof (S.T_union_le a b) as Htime.
    unfold size, c_lat; time_unfold @T_join; nia.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intro a; pose proof (S.T_subset_le a S.empty) as Htime.
    rewrite S.nodes_empty, Nat.add_0_r in Htime.
    unfold size, c_lat; time_unfold @T_is_bot; nia.
  Qed.
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
  Definition c_lat : N := (S.c_set + 8)%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat; lia.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a|] [b|]; unfold size, c_lat.
    all: time_unfold @T_leb; time_unfold @T_genkill_must_leb.
    all: time_cbn; time_pose; time_cbn_all;
      repeat rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [a|] [b|]; unfold size, c_lat.
    all: time_unfold @T_join; time_unfold @T_genkill_must_join.
    all: time_cbn; time_pose; time_cbn_all;
      repeat rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros [a|]; unfold size, c_lat; time_step.
  Qed.
End GenKillMustDomainT.

Module GenKillMayFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MAY_DOMAIN_T F S) <: GENKILL_MAY_FLOW_T P N E F S G L.
  Include GenKillMayFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
  Definition flow_work p s := N.of_nat (G.gk_work p + s).
  Definition c_flow : N := (8 * (G.c_gk + S.c_set + 1))%N.
  Lemma flow_work_mono : forall p s t, s <= t ->
    (flow_work p s <= flow_work p t)%N.
  Proof.
    intros p s t Hst; unfold flow_work; apply time_of_nat_le; lia.
  Qed.
  Lemma T_boundary_le : forall p n,
    (T_boundary p n <= c_flow * (flow_work p 0 + 1))%N.
  Proof.
    intros p n; unfold c_flow, flow_work; time_step.
  Qed.
  Lemma T_transfer_le : forall p e a,
    (T_transfer p e a <= c_flow * (flow_work p (L.size a) + 1))%N.
  Proof.
    intros p e a.
    pose proof (G.gen_nodes p e) as Hgen_size.
    pose proof (G.kill_nodes p e) as Hkill_size.
    pose proof (S.nodes_diff a (G.kill p e)) as Hdiff_size.
    apply time_of_nat_le in Hgen_size, Hkill_size, Hdiff_size.
    pose proof (G.T_gen_le p e) as Hgen.
    pose proof (G.T_kill_le p e) as Hkill.
    pose proof (S.T_diff_le a (G.kill p e)) as Hdiff.
    pose proof (S.T_union_le (G.gen p e) (S.diff a (G.kill p e))) as Hunion.
    unfold c_flow, flow_work; rewrite L.size_nodes; time_unfold @T_transfer.
    repeat rewrite Nat2N.inj_add in *; nia.
  Qed.
  Lemma boundary_size_le : forall p n,
    (N.of_nat (L.size (boundary p n)) <= flow_work p 0)%N.
  Proof.
    intros p n; unfold boundary, flow_work; rewrite L.size_nodes.
    apply time_of_nat_le; pose proof (G.init_nodes p) as Hinit; lia.
  Qed.
  Lemma transfer_size_le : forall p e a,
    (N.of_nat (L.size (transfer p e a)) <= flow_work p (L.size a))%N.
  Proof.
    intros p e a; unfold transfer, flow_work; rewrite !L.size_nodes.
    apply time_of_nat_le.
    pose proof (S.nodes_union (G.gen p e) (S.diff a (G.kill p e))) as Hunion.
    pose proof (S.nodes_diff a (G.kill p e)) as Hdiff.
    pose proof (G.gen_nodes p e) as Hgen; lia.
  Qed.

  (** Reading the initial facts is linear in the gen-kill problem size. *)
  Lemma boundary_complexity : bigO (X := P.t * N.t) (fun _ => True)
    (fun '(p, _) => N.of_nat (G.gk_work p)) (fun '(p, n) => T_boundary p n).
  Proof.
    apply bigO_intro with (c := c_flow); intros [p n] _.
    pose proof (T_boundary_le p n) as Htime.
    unfold flow_work in Htime; rewrite Nat.add_0_r in Htime.
    change (T_boundary p n <= c_flow * N.of_nat (G.gk_work p) + c_flow)%N; nia.
  Qed.

  (** A transfer is linear in the gen-kill problem and input fact sizes. *)
  Lemma transfer_complexity : bigO (X := P.t * E.t * L.t) (fun _ => True)
    (fun '(p, _, a) => N.of_nat (G.gk_work p + L.size a))
    (fun '(p, e, a) => T_transfer p e a).
  Proof.
    apply bigO_intro with (c := c_flow); intros [[p e] a] _.
    pose proof (T_transfer_le p e a) as Htime; unfold flow_work in Htime.
    change (T_transfer p e a <=
      c_flow * N.of_nat (G.gk_work p + L.size a) + c_flow)%N; nia.
  Qed.
End GenKillMayFlowT.

Module GenKillMustFlowT (P : TYPE) (N : KEY_T) (E : TYPE)
    (F : KEY_T) (S : SET_T F) (G : GENKILL_T P E F S)
    (L : GENKILL_MUST_DOMAIN_T F S) <: GENKILL_MUST_FLOW_T P N E F S G L.
  Include GenKillMustFlowCode P N E F S G L.
  TimeFun dir.
  TimeFun boundary.
  TimeFun transfer.
  Definition flow_work p s := N.of_nat (G.gk_work p + s).
  Definition c_flow : N := (8 * (G.c_gk + S.c_set + 1))%N.
  Lemma flow_work_mono : forall p s t, s <= t ->
    (flow_work p s <= flow_work p t)%N.
  Proof.
    intros p s t Hst; unfold flow_work; apply time_of_nat_le; lia.
  Qed.
  Lemma T_boundary_le : forall p n,
    (T_boundary p n <= c_flow * (flow_work p 0 + 1))%N.
  Proof.
    intros p n; unfold c_flow, flow_work; time_step.
  Qed.
  Lemma T_transfer_le : forall p e a,
    (T_transfer p e a <= c_flow * (flow_work p (L.size a) + 1))%N.
  Proof.
    intros p e [a|].
    - pose proof (G.gen_nodes p e) as Hgen_size.
      pose proof (G.kill_nodes p e) as Hkill_size.
      pose proof (S.nodes_diff a (G.kill p e)) as Hdiff_size.
      apply time_of_nat_le in Hgen_size, Hkill_size, Hdiff_size.
      pose proof (G.T_gen_le p e) as Hgen.
      pose proof (G.T_kill_le p e) as Hkill.
      pose proof (S.T_diff_le a (G.kill p e)) as Hdiff.
      pose proof (S.T_union_le (G.gen p e) (S.diff a (G.kill p e))) as Hunion.
      unfold c_flow, flow_work; rewrite L.size_nodes; time_unfold @T_transfer.
      time_cbn; repeat rewrite Nat2N.inj_add in *; nia.
    - unfold c_flow, flow_work; rewrite L.size_nodes; time_step.
  Qed.
  Lemma boundary_size_le : forall p n,
    (N.of_nat (L.size (boundary p n)) <= flow_work p 0)%N.
  Proof.
    intros p n; unfold boundary, flow_work; rewrite L.size_nodes.
    apply time_of_nat_le; pose proof (G.init_nodes p) as Hinit; lia.
  Qed.
  Lemma transfer_size_le : forall p e a,
    (N.of_nat (L.size (transfer p e a)) <= flow_work p (L.size a))%N.
  Proof.
    intros p e [a|]; unfold transfer, flow_work; rewrite !L.size_nodes;
      apply time_of_nat_le; [|lia].
    pose proof (S.nodes_union (G.gen p e) (S.diff a (G.kill p e))) as Hunion.
    pose proof (S.nodes_diff a (G.kill p e)) as Hdiff.
    pose proof (G.gen_nodes p e) as Hgen; lia.
  Qed.

  (** Reading the initial facts is linear in the gen-kill problem size. *)
  Lemma boundary_complexity : bigO (X := P.t * N.t) (fun _ => True)
    (fun '(p, _) => N.of_nat (G.gk_work p)) (fun '(p, n) => T_boundary p n).
  Proof.
    apply bigO_intro with (c := c_flow); intros [p n] _.
    pose proof (T_boundary_le p n) as Htime.
    unfold flow_work in Htime; rewrite Nat.add_0_r in Htime.
    change (T_boundary p n <= c_flow * N.of_nat (G.gk_work p) + c_flow)%N; nia.
  Qed.

  (** A transfer is linear in the gen-kill problem and input fact sizes. *)
  Lemma transfer_complexity : bigO (X := P.t * E.t * L.t) (fun _ => True)
    (fun '(p, _, a) => N.of_nat (G.gk_work p + L.size a))
    (fun '(p, e, a) => T_transfer p e a).
  Proof.
    apply bigO_intro with (c := c_flow); intros [[p e] a] _.
    pose proof (T_transfer_le p e a) as Htime; unfold flow_work in Htime.
    change (T_transfer p e a <=
      c_flow * N.of_nat (G.gk_work p + L.size a) + c_flow)%N; nia.
  Qed.
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
