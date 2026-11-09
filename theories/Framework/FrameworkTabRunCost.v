(** * Numerical costs of the actual jump run

    Primitive budgets compose through preparation, owned record replay and the binary driver.
    For example, an exhausted raw run pays for every supplied inventory occurrence.
    Builds on: FrameworkTabPrepareCost, FrameworkTabRecordCost and FrameworkTabJumpProgress. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop CostBound.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseTrieCost.
From Galois.Lattice Require Import LatticeCore LatticeHeight.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabPaths FrameworkTabRecords FrameworkTabCost FrameworkTabEncodingCost
  FrameworkTabPrepareCost FrameworkTabRecordCost FrameworkTabJumpProgress.
Import List.ListNotations Cost.Notations.

Module TabRunCost.

(** The key domain contains supplied roots and actual raw endpoints, including unlisted outputs. *)
Definition coordinate {N E P D A F} (I : Ide.t N E P D A F) start v :=
  In v (TabPaths.roots I start) \/
    exists a, In a (Jump.arcs I) /\ (v = Jump.source a \/ v = Jump.target a).

(** Budgets price original callbacks on the finite coordinate domain and all symbolic operands. *)
Record primitives {N E P D A F} (I : Ide.t N E P D A F) start e w m : Prop := {
  node : forall v, coordinate I start v ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (fst v) e w;
  fact : forall v, coordinate I start v ->
    match snd v with
    | Some d => TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w
    | None => True
    end;
  edge : forall a, In a (Jump.arcs I) ->
    TabEncodingCost.bounded (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Jump.edge a) e w;
  site : forall a p, In a (Jump.arcs I) ->
    (Jump.kind a = Icfg.Call p \/ Jump.kind a = Icfg.Return p) ->
    TabEncodingCost.bounded (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) p e w;
  compose : forall f g, (Cost.ticks (Micro.compose_c (Ide.micro I) f g) <= m)%N;
  compare : forall f g, (Cost.ticks (leb_c (Micro.lat (Ide.micro I)) f g) <= m)%N;
  joining : forall f g, (Cost.ticks (join_c (Micro.lat (Ide.micro I)) f g) <= m)%N
}.
Arguments node {N E P D A F I start e w m}.
Arguments fact {N E P D A F I start e w m}.
Arguments edge {N E P D A F I start e w m}.
Arguments site {N E P D A F I start e w m}.
Arguments compose {N E P D A F I start e w m}.
Arguments compare {N E P D A F I start e w m}.
Arguments joining {N E P D A F I start e w m}.

Definition vw w := TabEncodingCost.pair_width w (TabEncodingCost.option_width w).
Definition ve e w :=
  TabEncodingCost.pair_charge e (TabEncodingCost.option_charge e w)
    w (TabEncodingCost.option_width w).
Definition jw w := TabEncodingCost.pair_width (vw w) (vw w).
Definition je e w := TabEncodingCost.pair_charge (ve e w) (ve e w) (vw w) (vw w).
Definition aw w :=
  TabEncodingCost.pair_width w
    (TabEncodingCost.pair_width (TabEncodingCost.option_width w)
      (TabEncodingCost.option_width w)).
Definition ae e w :=
  TabEncodingCost.pair_charge e
    (TabEncodingCost.pair_charge (TabEncodingCost.option_charge e w)
      (TabEncodingCost.option_charge e w)
      (TabEncodingCost.option_width w) (TabEncodingCost.option_width w))
    w (TabEncodingCost.pair_width (TabEncodingCost.option_width w)
      (TabEncodingCost.option_width w)).
Definition iw w := TabEncodingCost.pair_width (vw w) (aw w).
Definition ie e w := TabEncodingCost.pair_charge (ve e w) (ae e w) (vw w) (aw w).
Definition probe e w := (3 + je e w + jw w)%N.
Definition update e w m := (probe e w + 2 * m + 3 * je e w + 3 * jw w + 7)%N.
Definition replay e w m := (2 + 2 * e + w + 2 * probe e w + 3 + 3 * m + update e w m)%N.

Definition roots {N E P D A F} (I : Ide.t N E P D A F) :=
  (1 + TabPrepareCost.facts I + TabPrepareCost.arc_count I)%N.
Definition keys {N E P D A F} (I : Ide.t N E P D A F) :=
  (roots I * (1 + 2 * TabPrepareCost.arc_count I))%N.
Definition call_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (3 * (1 + ve e w + vw w) + 1 + ie e w + 2 + iw w +
    TrieCost.trie_k * (1 + TabPrepareCost.arc_count I * aw w) +
    TabPrepareCost.arc_count I * (1 + replay e w m))%N.
Definition end_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (3 * (1 + ve e w + vw w) + 1 + ae e w + 2 + aw w +
    TrieCost.trie_k * (1 + roots I * TabPrepareCost.arc_count I * iw w) +
    roots I * TabPrepareCost.arc_count I * (1 + replay e w m))%N.
Definition arc_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (probe e w + 1 + m + update e w m + call_charge I e w m + end_charge I e w m)%N.
Definition step_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (1 + je e w + jw w + 1 + ve e w + vw w +
    TabPrepareCost.arc_count I * (1 + arc_charge I e w m))%N.
Definition initial_charge {N E P D A F} (I : Ide.t N E P D A F) e w m :=
  (keys I * (1 + 2 * (1 + je e w + jw w)) + roots I * (1 + update e w m))%N.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

(** A charged fold composes a body bound while retaining the body's maintained invariant. *)
Theorem fold_cost {X S} (f : S -> X -> Cost.t S) (P : S -> Prop) xs s k :
  (forall t x, P t -> In x xs ->
    P (Cost.value (f t x)) /\ (Cost.ticks (f t x) <= k)%N) ->
  P s -> (Cost.ticks (fold_left_c f xs s) <= N.of_nat (length xs) * (1 + k))%N.
Proof.
  intros Hstep Hs.
  pose proof (ticks_fold_left_c_potential f P (fun _ => 0%N) k xs s) as Hfold.
  specialize (Hfold (fun t x Ht Hx => ltac:(
    destruct (Hstep t x Ht Hx) as [Hp Hcost]; split; [exact Hp|cbn; lia])) Hs).
  cbn in Hfold; nia.
Qed.

(** Sequential callback budgets add without a hypothesis about the returned intermediate value. *)
Theorem bind_cost {X Y} (c : Cost.t X) (f : X -> Cost.t Y) a b :
  (Cost.ticks c <= a)%N -> (forall x, (Cost.ticks (f x) <= b)%N) ->
  (Cost.ticks (Cost.bind c f) <= a + b)%N.
Proof.
  intros Hc Hf; rewrite Cost.ticks_bind; specialize (Hf (Cost.value c)); lia.
Qed.

Local Lemma code_set_cost {V} code (v : V) bucket :
  Cost.ticks (Map.set_c positive_encoding code v bucket) = (2 + N.pos (Pos.size code))%N.
Proof.
  rewrite Map.set_cost, positive_encoding_cost, positive_encoding_equation; reflexivity.
Qed.

(** Sum bounds use named leaf budgets before descending through the surrounding additions. *)
Local Ltac add_budgets :=
  first [
    eassumption
  | match goal with
    | |- (?a + ?b <= _)%N => eapply N.add_le_mono; add_budgets
    end
  | apply N.le_refl ].

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (start : N) (e w m : BinNums.N).
Context (HP : primitives I start e w m).
Context (HV : encoding_laws (IdeValue.key_enc I)).

Local Lemma source_coordinate a :
  In a (Jump.arcs I) -> coordinate I start (Jump.source a).
Proof.
  intro Ha; right; exists a; split; [exact Ha|left; reflexivity].
Qed.

Local Lemma target_coordinate a :
  In a (Jump.arcs I) -> coordinate I start (Jump.target a).
Proof.
  intro Ha; right; exists a; split; [exact Ha|right; reflexivity].
Qed.

(** Vertex budgets derive from the original callbacks on the explicit coordinate domain. *)
Theorem vertex_budget v :
  coordinate I start v -> TabEncodingCost.bounded (IdeValue.key_enc I) v (ve e w) (vw w).
Proof.
  intro Hv; destruct v as [n d]; apply TabEncodingCost.vertex_bounded.
  - exact (node HP (n, d) Hv).
  - exact (fact HP (n, d) Hv).
Qed.

(** Jump budgets retain both actual coordinate encodings and their serialization. *)
Theorem jump_budget r v :
  coordinate I start r -> coordinate I start v ->
  TabEncodingCost.bounded (Jump.enc I) (r, v) (je e w) (jw w).
Proof.
  intros Hr Hv; apply TabEncodingCost.jump_bounded; apply vertex_budget; assumption.
Qed.

Local Lemma arc_budget a :
  In a (Jump.arcs I) -> TabEncodingCost.bounded (Tab.arc_enc I) (Tab.arc_key a) (ae e w) (aw w).
Proof.
  intro Ha; apply TabEncodingCost.arc_bounded.
  - exact (edge HP a Ha).
  - exact (fact HP (Jump.source a) (source_coordinate a Ha)).
  - exact (fact HP (Jump.target a) (target_coordinate a Ha)).
Qed.

Local Lemma incoming_budget root a :
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  TabEncodingCost.bounded (Tab.incoming_enc I) (root, Tab.arc_key a) (ie e w) (iw w).
Proof.
  intros Hr Ha; apply TabEncodingCost.incoming_bounded.
  - apply vertex_budget; left; exact Hr.
  - apply arc_budget; exact Ha.
Qed.

(** A jump probe prices its composite encoder and the public positive-map traversal. *)
Theorem lookup_cost js r v :
  coordinate I start r -> coordinate I start v ->
  (Cost.ticks (Jump.lookup_c I js (r, v)) <= probe e w)%N.
Proof.
  intros Hr Hv; destruct (jump_budget r v Hr Hv) as [He Hw].
  unfold Jump.lookup_c; autorewrite with galois_cost.
  rewrite Map.find_or_cost, Map.get_cost, positive_encoding_cost, positive_encoding_equation.
  fold (encode (Jump.enc I) (r, v)).
  fold (key_bits (Jump.enc I) (r, v)).
  unfold probe; lia.
Qed.

Local Lemma update_cost s r v f :
  coordinate I start r -> coordinate I start v ->
  (Cost.ticks (Tab.update_c I (r, v) f s) <= update e w m)%N.
Proof.
  intros Hr Hv; destruct (jump_budget r v Hr Hv) as [He Hw].
  eapply N.le_trans.
  - apply TabCost.update_cost with
      (Kq := probe e w) (Kl := m) (Kj := m) (Ke := je e w)
      (Kput := (2 + jw w)%N) (w := jw w).
    + apply lookup_cost; assumption.
    + exact (compare HP _ _).
    + exact (joining HP _ _).
    + exact He.
    + intros joined js; rewrite Map.set_cost, positive_encoding_cost, positive_encoding_equation.
      fold (key_bits (Jump.enc I) (r, v)); lia.
    + exact Hw.
  - unfold update; lia.
Qed.

(** Actual matching prices original site encoders and the public encoded comparison. *)
Theorem matches_cost a b :
  In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  (Cost.ticks (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) <=
    2 + 2 * e + w)%N.
Proof.
  intros Ha Hb; unfold Jump.matches_c.
  destruct (Jump.kind a) as [|p|p] eqn:Hka,
    (Jump.kind b) as [|q|q] eqn:Hkb; try (cbn; lia).
  pose proof (eqb_cost (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) p q) as Hcost.
  destruct (site HP a p Ha (or_introl Hka)) as [Hpe Hpw].
  destruct (site HP b q Hb (or_intror Hkb)) as [Hqe Hqw].
  pose proof (N.le_min_l
    (key_bits (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) p)
    (key_bits (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) q)); lia.
Qed.

Local Lemma return_cost s root a b :
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) -> In b (Jump.arcs I) ->
  (Cost.ticks (Tab.return_c I root a b s) <= replay e w m)%N.
Proof.
  intros Hr Ha Hb; unfold Tab.return_c.
  eapply N.le_trans.
  - eapply bind_cost; [apply matches_cost; assumption|].
    intros yes; destruct yes.
    + eapply bind_cost; [apply lookup_cost; [left; exact Hr|apply source_coordinate; exact Ha]|].
      intro prior.
      eapply bind_cost; [apply lookup_cost; apply target_coordinate || apply source_coordinate;
        assumption|].
      intro inside.
      eapply bind_cost; [reflexivity|]; intros [].
      eapply bind_cost; [exact (compose HP _ _)|]; intro pushed.
      eapply bind_cost; [reflexivity|]; intros [].
      eapply bind_cost; [exact (compose HP _ _)|]; intro body.
      eapply bind_cost; [reflexivity|]; intros [].
      eapply bind_cost; [exact (compose HP _ _)|]; intro result.
      apply update_cost; [left; exact Hr|apply target_coordinate; exact Hb].
    + rewrite Cost.ticks_ret; lia.
  - autorewrite with galois_cost; unfold replay; lia.
Qed.

(** Supplied initial facts and exploded call occurrences bound the actual root list. *)
Theorem root_count :
  (N.of_nat (length (TabPaths.roots I start)) <= roots I)%N.
Proof.
  exact (TabPrepareCost.roots_length I start (Jump.arcs I)).
Qed.

Local Lemma call_replay_cost s root a t :
  TabRecords.valid I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (Cost.ticks (fold_left_c (fun t kv => Tab.return_c I root a (snd kv) t)
    (Map.elements (TabRecords.ends I s (Jump.target a))) t) <=
    TabPrepareCost.arc_count I * (1 + replay e w m))%N.
Proof.
  intros Hvalid Hr Ha.
  eapply N.le_trans.
  - apply fold_cost with (P := fun _ => True); [|exact Logic.I].
    intros u [code b] Hu Hb; split; [exact Logic.I|].
    apply return_cost; [exact Hr|exact Ha|].
    exact (proj1 (proj2 (TabRecords.end_element I start s (Jump.target a) code b Hvalid Hb))).
  - apply N.mul_le_mono_r, nat_N_le.
    exact (TabRecordCost.end_length I start s (Jump.target a) Hvalid).
Qed.

Local Lemma call_cost s root a :
  TabRecords.valid I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (Cost.ticks (Tab.call_c I root a s) <= call_charge I e w m)%N.
Proof.
  intros Hvalid Hr Ha.
  destruct (vertex_budget (Jump.target a) (target_coordinate a Ha)) as [He Hw].
  destruct (incoming_budget root a Hr Ha) as [Hi Hiw].
  pose proof (TabRecordCost.end_enumeration_cost I start s (Jump.target a) (aw w)
    Hvalid (fun b Hb => proj2 (arc_budget b Hb))) as Henum.
  fold (TabPrepareCost.arc_count I) in Henum.
  unfold Tab.call_c; rewrite !Cost.ticks_bind.
  fold (TabRecords.callers I s (Jump.target a)).
  fold (TabRecords.ends I s (Jump.target a)).
  rewrite Map.find_or_cost, Map.get_cost.
  autorewrite with galois_cost.
  rewrite code_set_cost, Map.set_cost, Map.find_or_cost, Map.get_cost.
  cbn [Tab.ends Tab.callers].
  change (Cost.value (encode_c (Tab.incoming_enc I) (root, Tab.arc_key a)))
    with (encode (Tab.incoming_enc I) (root, Tab.arc_key a)).
  change (Cost.value (Map.find_or_c (IdeValue.key_enc I) Map.empty
    (Jump.target a) (Tab.ends s))) with (TabRecords.ends I s (Jump.target a)).
  change (Cost.value (Map.elements_c (TabRecords.ends I s (Jump.target a))))
    with (Map.elements (TabRecords.ends I s (Jump.target a))).
  fold (key_bits (IdeValue.key_enc I) (Jump.target a)).
  fold (key_bits (Tab.incoming_enc I) (root, Tab.arc_key a)).
  match goal with
  | |- context [Cost.ticks (fold_left_c _ _ ?t)] =>
    pose proof (call_replay_cost s root a t Hvalid Hr Ha) as Hbodycost
  end.
  eapply N.le_trans; [add_budgets|].
  unfold call_charge; lia.
Qed.

Local Lemma end_replay_cost s root a t :
  TabRecords.valid I start s -> In a (Jump.arcs I) ->
  (Cost.ticks (fold_left_c (fun t kv =>
    Tab.return_c I (fst (snd kv)) (snd (snd kv)) a t)
    (Map.elements (TabRecords.callers I s root)) t) <=
    roots I * TabPrepareCost.arc_count I * (1 + replay e w m))%N.
Proof.
  intros Hvalid Ha.
  pose proof (TabRecordCost.caller_length I start s root Hvalid) as Hlen.
  apply nat_N_le in Hlen; rewrite Nat2N.inj_mul in Hlen.
  eapply N.le_trans.
  - apply fold_cost with (P := fun _ => True); [|exact Logic.I].
    intros u [code [outer call]] Hu Hcall; split; [exact Logic.I|].
    destruct (TabRecords.caller_element I start s root code outer call Hvalid Hcall)
      as [Hroot [Harc Hrest]].
    apply return_cost; assumption.
  - apply N.mul_le_mono_r; eapply N.le_trans; [exact Hlen|].
    apply N.mul_le_mono_r; exact root_count.
Qed.

Local Lemma end_cost s root a :
  TabRecords.valid I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (Cost.ticks (Tab.end_c I root a s) <= end_charge I e w m)%N.
Proof.
  intros Hvalid Hr Ha.
  destruct (vertex_budget root (or_introl Hr)) as [He Hw].
  destruct (arc_budget a Ha) as [Haenc Haw].
  pose proof (TabRecordCost.caller_enumeration_cost I start s root (iw w)
    Hvalid (fun r b Hroot Hb => proj2 (incoming_budget r b Hroot Hb))) as Henum.
  unfold Tab.end_c; rewrite !Cost.ticks_bind.
  fold (TabRecords.ends I s root).
  fold (TabRecords.callers I s root).
  rewrite Map.find_or_cost, Map.get_cost.
  autorewrite with galois_cost.
  rewrite code_set_cost, Map.set_cost, Map.find_or_cost, Map.get_cost.
  cbn [Tab.ends Tab.callers].
  change (Cost.value (encode_c (Tab.arc_enc I) (Tab.arc_key a)))
    with (encode (Tab.arc_enc I) (Tab.arc_key a)).
  change (Cost.value (Map.find_or_c (IdeValue.key_enc I) Map.empty root (Tab.callers s)))
    with (TabRecords.callers I s root).
  change (Cost.value (Map.elements_c (TabRecords.callers I s root)))
    with (Map.elements (TabRecords.callers I s root)).
  fold (key_bits (IdeValue.key_enc I) root).
  fold (key_bits (Tab.arc_enc I) (Tab.arc_key a)).
  match goal with
  | |- context [Cost.ticks (fold_left_c _ _ ?t)] =>
    pose proof (end_replay_cost s root a t Hvalid Ha) as Hbodycost
  end.
  assert (Htrie :
    (TrieCost.trie_k * (1 + N.of_nat (length (TabPaths.roots I start)) *
      N.of_nat (length (Jump.arcs I)) * iw w) <=
      TrieCost.trie_k * (1 + roots I * TabPrepareCost.arc_count I * iw w))%N).
  { apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r, N.mul_le_mono_r.
    exact root_count. }
  pose proof (N.le_trans _ _ _ Henum Htrie) as Henumeration.
  eapply N.le_trans; [add_budgets|].
  unfold end_charge; lia.
Qed.

Local Lemma arc_cost s root a :
  TabRecords.valid I start s -> In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (Cost.ticks (Tab.arc_c I root a s) <= arc_charge I e w m)%N.
Proof.
  intros Hvalid Hr Ha; unfold Tab.arc_c; destruct (Jump.kind a).
  - autorewrite with galois_cost.
    pose proof (lookup_cost (Tab.jumps s) root (Jump.source a)
      (or_introl Hr) (source_coordinate a Ha)) as Hlookup.
    pose proof (compose HP (Jump.weight a)
      (Jump.lookup I (Tab.jumps s) (root, Jump.source a))) as Hcompose.
    pose proof (update_cost s root (Jump.target a)
      (Micro.compose (Ide.micro I) (Jump.weight a)
        (Jump.lookup I (Tab.jumps s) (root, Jump.source a)))
      (or_introl Hr) (target_coordinate a Ha)) as Hupdate.
    change (Cost.ticks (Jump.lookup_c I (Tab.jumps s) (root, Jump.source a)) +
      (1 + (Cost.ticks (Micro.compose_c (Ide.micro I) (Jump.weight a)
        (Jump.lookup I (Tab.jumps s) (root, Jump.source a))) +
      Cost.ticks (Tab.update_c I (root, Jump.target a)
        (Micro.compose (Ide.micro I) (Jump.weight a)
          (Jump.lookup I (Tab.jumps s) (root, Jump.source a))) s))) <=
      arc_charge I e w m)%N.
    unfold arc_charge; lia.
  - pose proof (call_cost s root a Hvalid Hr Ha); unfold arc_charge; lia.
  - pose proof (end_cost s root a Hvalid Hr Ha); unfold arc_charge; lia.
Qed.

Local Lemma inventory_coordinates key :
  In key (Tab.inventory (Tab.prepare I start)) ->
  coordinate I start (fst key) /\ coordinate I start (snd key).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  intro Hin; apply in_flat_map in Hin; destruct Hin as [root [Hr Hin]].
  apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; subst key.
  split; [left; exact Hr|]; cbn [snd]; destruct Hv as [Heq|Hv].
  - subst v; left; exact Hr.
  - right; apply in_flat_map in Hv; destruct Hv as [a [Ha [Heq|[Heq|Hbad]]]].
    + exists a; split; [exact Ha|left; symmetry; exact Heq].
    + exists a; split; [exact Ha|right; symmetry; exact Heq].
    + contradiction.
Qed.

(** The actual callback price follows from owned bucket support and maintained finite work keys. *)
Theorem step_cost s :
  TabJumpProgress.invariant I start s ->
  (Cost.ticks (Tab.step_c I (Tab.prepare I start) s) <= step_charge I e w m)%N.
Proof.
  intros [Hvalid [Hshape [Hwork Hstored]]].
  unfold Tab.step_c; destruct (Tab.work s) as [|[root v] rest] eqn:Hlist.
  - cbn; lia.
  - assert (Hkey : In (root, v) (Tab.inventory (Tab.prepare I start))).
    { apply Hwork; left; reflexivity. }
    destruct (inventory_coordinates (root, v) Hkey) as [Hr Hv].
    destruct (jump_budget root v Hr Hv) as [Hje Hjw].
    destruct (vertex_budget v Hv) as [Hve Hvw].
    assert (Hroot : In root (TabPaths.roots I start)).
    { exact (TabRecords.inventory_root I start (root, v) Hkey). }
    assert (Hout : (N.of_nat (length
      (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start)))) <=
      TabPrepareCost.arc_count I)%N).
    { rewrite Tab.prepare_equation; cbn [Tab.outgoing]; rewrite Index.find_group_by.
      apply nat_N_le; apply List.filter_length_le. }
    pose proof (fold_cost (fun t a => Tab.arc_c I root a t) (TabRecords.valid I start)
      (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start)))
      (Tab.State (Tab.jumps s) (Tab.callers s) (Tab.ends s) rest
        (FinSet.remove (Jump.enc I) (root, v) (Tab.pending s)))
      (arc_charge I e w m)) as Hfold.
    assert (Hbody : forall t a, TabRecords.valid I start t ->
      In a (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start))) ->
      TabRecords.valid I start (Cost.value (Tab.arc_c I root a t)) /\
        (Cost.ticks (Tab.arc_c I root a t) <= arc_charge I e w m)%N).
    { intros t a Ht Ha.
      apply (TabRecords.outgoing_member I start v a) in Ha; split.
      - apply TabRecords.arc_valid with (start := start); assumption.
      - apply arc_cost; assumption. }
    specialize (Hfold Hbody (TabRecords.rebuild_valid I start s _ _ _ Hvalid)).
    autorewrite with galois_cost; rewrite FinSet.remove_cost, Index.find_cost, Map.get_cost.
    fold (key_bits (Jump.enc I) (root, v)).
    fold (key_bits (IdeValue.key_enc I) v).
    assert (Hscan :
      (N.of_nat (length
        (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start)))) *
        (1 + arc_charge I e w m) <=
        TabPrepareCost.arc_count I * (1 + arc_charge I e w m))%N).
    { apply N.mul_le_mono_r; exact Hout. }
    pose proof (N.le_trans _ _ _ Hfold Hscan) as Hbodycost.
    eapply N.le_trans; [add_budgets|].
    unfold step_charge; lia.
Qed.

Local Lemma initial_cost :
  (Cost.ticks (Tab.initial_c I (Tab.prepare I start)) <= initial_charge I e w m)%N.
Proof.
  unfold Tab.initial_c; rewrite Cost.ticks_bind.
  pose proof (fold_cost (fun s k => Tab.schedule_c I k s) (fun _ => True)
    (Tab.inventory (Tab.prepare I start))
    (Tab.State Map.empty Map.empty Map.empty [] FinSet.empty)
    (2 * (1 + je e w + jw w))%N) as Hschedule.
  assert (Hs : forall s k, True -> In k (Tab.inventory (Tab.prepare I start)) ->
    True /\ (Cost.ticks (Tab.schedule_c I k s) <= 2 * (1 + je e w + jw w))%N).
  { intros s [r v] Htrue Hkey; split; [exact Logic.I|].
    destruct (inventory_coordinates (r, v) Hkey) as [Hr Hv].
    destruct (jump_budget r v Hr Hv) as [He Hw].
    apply TabCost.schedule_cost; assumption. }
  specialize (Hschedule Hs Logic.I).
  pose proof (fold_cost (fun s r => Tab.update_c I (r, r) (Micro.id (Ide.micro I)) s)
    (fun _ => True) (Tab.roots (Tab.prepare I start))
    (Cost.value (fold_left_c (fun s k => Tab.schedule_c I k s)
      (Tab.inventory (Tab.prepare I start))
      (Tab.State Map.empty Map.empty Map.empty [] FinSet.empty)))
    (update e w m)) as Hupdate.
  assert (Hu : forall s r, True -> In r (Tab.roots (Tab.prepare I start)) ->
    True /\ (Cost.ticks (Tab.update_c I (r, r) (Micro.id (Ide.micro I)) s) <= update e w m)%N).
  { intros s r Htrue Hr; split; [exact Logic.I|].
    rewrite Tab.prepare_equation in Hr.
    apply update_cost; left; exact Hr. }
  specialize (Hupdate Hu Logic.I).
  pose proof (TabPrepareCost.inventory_bound I start) as Hkeys.
  assert (Hroots : (N.of_nat (length (Tab.roots (Tab.prepare I start))) <= roots I)%N).
  { rewrite Tab.prepare_equation; exact root_count. }
  assert (Hscales :
    (N.of_nat (length (Tab.inventory (Tab.prepare I start))) *
      (1 + 2 * (1 + je e w + jw w)) <=
      keys I * (1 + 2 * (1 + je e w + jw w)))%N).
  { apply N.mul_le_mono_r; exact Hkeys. }
  assert (Hscaleu :
    (N.of_nat (length (Tab.roots (Tab.prepare I start))) * (1 + update e w m) <=
      roots I * (1 + update e w m))%N).
  { apply N.mul_le_mono_r; exact Hroots. }
  pose proof (N.le_trans _ _ _ Hschedule Hscales) as Hschedule_total.
  pose proof (N.le_trans _ _ _ Hupdate Hscaleu) as Hupdate_total.
  eapply N.le_trans; [add_budgets|].
  unfold initial_charge; lia.
Qed.

Context (HK : encoding_laws (Jump.enc I)).

(** Raw execution includes preparation, initialized inventory and every binary-driver callback. *)
Theorem raw_cost fuel prep :
  (Cost.ticks (Tab.prepare_c I start) <= prep)%N ->
  (Cost.ticks (Tab.raw_c I start fuel) <=
    prep + initial_charge I e w m + (step_charge I e w m + 2) * N.pos fuel)%N.
Proof.
  intro Hprep.
  pose proof (iterate_cost_amortised (Tab.step_c I (Tab.prepare I start))
    (TabJumpProgress.invariant I start) (fun _ => 0%N) (step_charge I e w m)) as Hloop.
  assert (Hstep : forall s, TabJumpProgress.invariant I start s ->
    (match Cost.value (Tab.step_c I (Tab.prepare I start) s) with
     | inl next => TabJumpProgress.invariant I start next
     | inr _ => True
     end) /\
    (Cost.ticks (Tab.step_c I (Tab.prepare I start) s) +
      result_potential (fun _ => 0%N) (Cost.value (Tab.step_c I (Tab.prepare I start) s)) <=
      step_charge I e w m + 0)%N).
  { intros s Hs; split.
    - pose proof (TabJumpProgress.step_invariant I start HV HK s Hs) as Hnext.
      rewrite Tab.step_c_value.
      destruct (Tab.step I (Tab.prepare I start) s); [exact Hnext|exact Logic.I].
    - rewrite result_potential_zero; pose proof (step_cost s Hs); lia. }
  specialize (Hloop Hstep fuel (Tab.initial I (Tab.prepare I start))
    (TabJumpProgress.initial_invariant I start HK)).
  destruct Hloop as [Hresult Hloop].
  rewrite result_potential_zero in Hloop.
  change (Cost.ticks (iterate (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) + 0 + 1 <=
    (step_charge I e w m + 2) * N.pos fuel + 0)%N in Hloop.
  assert (Hloopcost :
    (Cost.ticks (iterate (Tab.step_c I (Tab.prepare I start)) fuel
      (Tab.initial I (Tab.prepare I start))) <=
      (step_charge I e w m + 2) * N.pos fuel)%N) by lia.
  pose proof initial_cost as Hinitial.
  unfold Tab.raw_c; rewrite !Cost.ticks_bind.
  fold (Tab.prepare I start).
  fold (Tab.initial I (Tab.prepare I start)).
  eapply N.le_trans; [add_budgets|]; lia.
Qed.

(** The public raw bound discharges preparation from genuine input callbacks and scalar encoders. *)
Theorem raw_numeric fuel ko ks kt kk kf kw q :
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (forall edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) edge) e w) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w) ->
  (Cost.ticks (Tab.raw_c I start fuel) <=
    TabPrepareCost.prepare_charge I ko ks kt kk kf kw q e e w w +
      initial_charge I e w m + (step_charge I e w m + 2) * N.pos fuel)%N.
Proof.
  intros HC Hnodes Hfacts; apply raw_cost.
  apply TabPrepareCost.prepare_cost; assumption.
Qed.

End Run.

(** Raw families with supplied fuel retain the preparation, initialization and driver polynomial. *)
Theorem raw_bigO {X N E P D A F} (I : X -> Ide.t N E P D A F)
    (start : X -> N) (fuel : X -> positive)
    (e w m ko ks kt kk kf kw q : X -> BinNums.N) :
  (forall x, primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, encoding_laws (Jump.enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  (forall x edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (I x)))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) edge) (e x) (w x)) ->
  (forall x d, In d (Ifds.facts (Ide.ifds (I x))) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds (I x))) d (e x) (w x)) ->
  bigO
    (fun x => (TabPrepareCost.prepare_charge (I x) (ko x) (ks x) (kt x) (kk x)
      (kf x) (kw x) (q x) (e x) (e x) (w x) (w x) +
      initial_charge (I x) (e x) (w x) (m x) +
      (step_charge (I x) (e x) (w x) (m x) + 2) * N.pos (fuel x))%N)
    (fun x => Cost.ticks (Tab.raw_c (I x) (start x) (fuel x))).
Proof.
  intros HP HV HK HC Hnodes Hfacts; exists 1%N; intro x.
  pose proof (raw_numeric (I x) (start x) (e x) (w x) (m x) (HP x) (HV x) (HK x)
    (fuel x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
    (HC x) (Hnodes x) (Hfacts x)); lia.
Qed.

(** Constructed-height work pays separately for the height numeral and full inventory traversal. *)
Definition complete_charge {N E P D A F} (I : Ide.t N E P D A F)
    ko ks kt kk kf kw q e w m h :=
  (TabPrepareCost.prepare_charge I ko ks kt kk kf kw q e e w w +
    initial_charge I e w m + h + keys I + 1 +
    (step_charge I e w m + 2) * (1 + (1 + h) * keys I))%N.

(** Constructed raw completion pays for the same raw run and its charged fuel constructor. *)
Theorem complete_raw_numeric {N E P D A F} (I : Ide.t N E P D A F) start e w m
    ko ks kt kk kf kw q (H : height (Micro.lat (Ide.micro I))) :
  primitives I start e w m ->
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Jump.enc I) ->
  TabPrepareCost.callbacks I ko ks kt kk kf kw q ->
  (forall edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) edge) e w) ->
  (forall d, In d (Ifds.facts (Ide.ifds I)) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d e w) ->
  (Cost.ticks (TabJumpProgress.complete_raw_c I start H) <=
    complete_charge I ko ks kt kk kf kw q e w m (N.of_nat (bound H)))%N.
Proof.
  intros HP HV HK HC Hnodes Hfacts.
  set (p := Tab.prepare I start).
  set (fuel := TabCost.rank_fuel p (bound H)).
  pose proof (raw_numeric I start e w m HP HV HK fuel ko ks kt kk kf kw q HC Hnodes Hfacts)
    as Hraw.
  assert (Hequation :
    Cost.ticks (TabJumpProgress.complete_raw_c I start H) =
      (Cost.ticks (Tab.raw_c I start fuel) +
        Cost.ticks (TabCost.rank_fuel_c p (bound H)))%N).
  { rewrite TabJumpProgress.complete_raw_cost_equation; cbn zeta.
    unfold Tab.raw_c; rewrite !Cost.ticks_bind.
    change (Cost.value (Tab.prepare_c I start)) with p.
    change (Cost.value (Tab.initial_c I p)) with (Tab.initial I p).
    fold p; fold fuel; lia. }
  assert (Hkeys : (N.of_nat (length (Tab.inventory p)) <= keys I)%N).
  { exact (TabPrepareCost.inventory_bound I start). }
  assert (Hfuel : (N.pos fuel <= 1 + (1 + N.of_nat (bound H)) * keys I)%N).
  { unfold fuel; rewrite TabCost.rank_fuel_equation, N.succ_pos_spec.
    pose proof (N.mul_le_mono_l _ _ (1 + N.of_nat (bound H)) Hkeys) as Hscale.
    lia. }
  assert (Hloop :
    ((step_charge I e w m + 2) * N.pos fuel <=
      (step_charge I e w m + 2) * (1 + (1 + N.of_nat (bound H)) * keys I))%N).
  { apply N.mul_le_mono_l; exact Hfuel. }
  rewrite Hequation, TabCost.rank_fuel_cost.
  unfold complete_charge; lia.
Qed.

(** A family of constructed raw runs has the explicit numeric polynomial as its big-O bound. *)
Theorem complete_raw_bigO {X N E P D A F}
    (I : X -> Ide.t N E P D A F) (start : X -> N)
    (e w m ko ks kt kk kf kw q : X -> BinNums.N)
    (H : forall x, height (Micro.lat (Ide.micro (I x)))) :
  (forall x, primitives (I x) (start x) (e x) (w x) (m x)) ->
  (forall x, encoding_laws (IdeValue.key_enc (I x))) ->
  (forall x, encoding_laws (Jump.enc (I x))) ->
  (forall x, TabPrepareCost.callbacks (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)) ->
  (forall x edge, In edge (Cfg.edges (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) ->
    TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds (I x)))))
      (Graph.source (Cfg.graph (Icfg.cfg (Ifds.icfg (Ide.ifds (I x))))) edge) (e x) (w x)) ->
  (forall x d, In d (Ifds.facts (Ide.ifds (I x))) ->
    TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds (I x))) d (e x) (w x)) ->
  bigO
    (fun x => complete_charge (I x) (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x)
      (e x) (w x) (m x) (N.of_nat (bound (H x))))
    (fun x => Cost.ticks (TabJumpProgress.complete_raw_c (I x) (start x) (H x))).
Proof.
  intros HP HV HK HC Hnodes Hfacts; exists 1%N; intro x.
  pose proof (complete_raw_numeric (I x) (start x) (e x) (w x) (m x)
    (ko x) (ks x) (kt x) (kk x) (kf x) (kw x) (q x) (H x)
    (HP x) (HV x) (HK x) (HC x) (Hnodes x) (Hfacts x)); lia.
Qed.

End TabRunCost.
