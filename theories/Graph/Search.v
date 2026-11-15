(** * Depth-first search

    Search visits roots and successor occurrences in their supplied order.
    For example, an edge to an active vertex produces a back-edge event.
    Builds on: graph data, binary-fuel loops and the search signature. *)

From Stdlib Require Import List NArith PArith Lia Arith Sorting.Permutation.
From Argent Require Import Time Tactics Std BigO Loop.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec DigraphSig SearchSig.
Import List.ListNotations.

Definition search_step (g : digraph) (s : search_state) : search_state + (list event) :=
  match s with
  | SearchState [] _ es => inr (rev_append es [])
  | SearchState (task :: tasks) colours es =>
    match task with
    | SearchRoot v =>
      match trie_get v colours with
      | Some _ => inl (SearchState tasks colours es)
      | None => inl (SearchState (SearchRow v (succs g v) :: SearchLeave v :: tasks)
          (PTrieCode.set v true colours) (Enter v :: es))
      end
    | SearchRow u [] => inl (SearchState tasks colours es)
    | SearchRow u (v :: vs) =>
      match trie_get v colours with
      | None => inl (SearchState (SearchRoot v :: SearchRow u vs :: tasks) colours
          (Edge Tree u v :: es))
      | Some active => inl (SearchState (SearchRow u vs :: tasks) colours
          (Edge (if active then Back else Done) u v :: es))
      end
    | SearchLeave v => inl (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es))
    end
  end.
TimeFun search_step.

Definition raw_search_budget (g : digraph) (roots : list positive) : N :=
  N.of_nat (4 * (length roots +
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)) + 1)).
TimeFun raw_search_budget.

Definition search_trace (g : digraph) (roots : list positive) : list event :=
  match loopN (search_step g) (raw_search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev_append (search_events s) []
  | inr es => es
  end.
TimeFun search_trace.

Definition search_budget (g : prepared) (roots : list positive) : N :=
  N.double (N.double (nv g + ne g + N.of_nat (length roots) + 1))%N.
TimeFun search_budget.

Definition prepared_search_trace (g : prepared) (roots : list positive) : list event :=
  match loopN (search_step (base g)) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty []) with
  | inl s => rev_append (search_events s) []
  | inr es => es
  end.
TimeFun prepared_search_trace.

(** Binary fuel and unary fuel describe the same sequence of task transitions. *)
Lemma search_loopN_fuel {St Out} (step : St -> St + Out) fuel st :
  loopN step fuel st = loop_fuel step (N.to_nat fuel) st.
Proof.
  assert (Hloop : forall fs (Hacc : Acc loopN_lt fs),
      loop loopN_lt (loopN_step step) fs Hacc =
      loop_fuel step (N.to_nat (fst fs)) (snd fs)).
  { intros fs Hacc. induction Hacc as [[n state] Hacc IH] using Acc_ind_dep.
    cbn [fst snd]. destruct n as [|p]; [reflexivity|].
    assert (Hpos : 0 < N.to_nat (N.pos p)) by lia.
    destruct (N.to_nat (N.pos p)) as [|n] eqn:Hn; [lia|].
    cbn [loop loopN_step loop_fuel Acc_inv].
    destruct (step state) as [next|result]; [|reflexivity].
    rewrite IH. cbn [fst snd]. rewrite N2Nat.inj_pred, Hn. reflexivity. }
  unfold loopN. apply Hloop.
Qed.

(** Task validity includes the source and every remaining target of an adjacency row. *)
Definition search_task_valid (domain : positive -> Prop) (task : search_task) : Prop :=
  match task with
  | SearchRoot v | SearchLeave v => domain v
  | SearchRow u vs => domain u /\ Forall domain vs
  end.

(** A successor-closed domain is retained by every continuing task transition. *)
Lemma search_tasks_preserved g domain st next :
  (forall u v, domain u -> edge g u v -> domain v) ->
  Forall (search_task_valid domain) (search_tasks st) ->
  search_step g st = inl next ->
  Forall (search_task_valid domain) (search_tasks next).
Proof.
  intros Hclosed Hvalid Hstep. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hvalid as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [v|u vs|v].
  - cbn [search_step] in Hstep. destruct (trie_get v colours).
    + inversion Hstep; subst next. exact Htail.
    + inversion Hstep; subst next. constructor.
      * split; [exact Htask|]. apply Forall_forall. intros w Hin.
        apply (Hclosed v w Htask). exact Hin.
      * constructor; [exact Htask|exact Htail].
  - destruct vs as [|v vs].
    + inversion Hstep; subst next. exact Htail.
    + destruct Htask as [Hu Hvs]. inversion Hvs as [|v0 vs0 Hv Hrest]; subst v0 vs0.
      cbn [search_step] in Hstep. destruct (trie_get v colours).
      * inversion Hstep; subst next. constructor; [split; assumption|exact Htail].
      * inversion Hstep; subst next. constructor; [exact Hv|].
        constructor; [split; assumption|exact Htail].
  - inversion Hstep; subst next. exact Htail.
Qed.

(** Lookup after one colour update distinguishes its key from all other vertices. *)
Local Lemma search_colour_set x y (b : bool) colours :
  trie_get x (PTrieCode.set y b colours) =
    if Pos.eqb x y then Some b else trie_get x colours.
Proof.
  destruct (Pos.eqb_spec x y) as [Heq|Hneq].
  - subst x. apply PTrie.get_set_same.
  - apply PTrie.get_set_other. exact Hneq.
Qed.

Local Lemma search_colour_empty v : trie_get v (@Empty bool) = None.
Proof.
  apply PTrie.get_empty.
Qed.

(** White work counts two vertex tasks and the outgoing row for each listed occurrence. *)
Definition search_white g vertices (colours : ptrie bool) : nat :=
  fold_right (fun v n =>
    match trie_get v colours with
    | None => 2 + length (succs g v) + n
    | Some _ => n
    end) 0 vertices.

(** Updating any colour can only remove white work. *)
Lemma search_white_set_le g vertices colours v b :
  search_white g vertices (PTrieCode.set v b colours) <= search_white g vertices colours.
Proof.
  induction vertices as [|u rest IH]; [reflexivity|].
  unfold search_white in *. cbn [fold_right]. rewrite search_colour_set.
  destruct (Pos.eqb u v); destruct (trie_get u colours); lia.
Qed.

(** Discovering a listed white vertex transfers at least one copy of its row credit. *)
Lemma search_white_discover g vertices colours v b :
  In v vertices -> trie_get v colours = None ->
  search_white g vertices (PTrieCode.set v b colours) + 2 + length (succs g v) <=
    search_white g vertices colours.
Proof.
  intros Hin Hwhite. induction vertices as [|u rest IH]; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst u. unfold search_white. cbn [fold_right].
    rewrite search_colour_set, Pos.eqb_refl, Hwhite.
    pose proof (search_white_set_le g rest colours v b) as Hle.
    unfold search_white in Hle. lia.
  - specialize (IH Hin). unfold search_white in *. cbn [fold_right].
    rewrite search_colour_set. destruct (Pos.eqb u v); destruct (trie_get u colours); lia.
Qed.

(** Pending rows charge their targets and the administrative empty-row step. *)
Definition search_task_credit tasks : nat :=
  fold_right (fun task n =>
    match task with
    | SearchRoot _ => 1 + n
    | SearchRow _ vs => 2 * length vs + 1 + n
    | SearchLeave _ => 1 + n
    end) 0 tasks.

Definition search_finite_credit g vertices st :=
  2 * search_white g vertices (search_colours st) +
    search_task_credit (search_tasks st).

(** Every continuing task consumes finite-domain credit, including administrative tasks. *)
Lemma search_finite_decreases g vertices st next :
  Forall (search_task_valid (fun v => In v vertices)) (search_tasks st) ->
  search_step g st = inl next ->
  search_finite_credit g vertices next < search_finite_credit g vertices st.
Proof.
  intros Hvalid Hstep. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hvalid as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [v|u vs|v].
  - cbn [search_step] in Hstep. destruct (trie_get v colours) eqn:Hcolour.
    + inversion Hstep; subst next. unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right]. lia.
    + inversion Hstep; subst next.
      pose proof (search_white_discover g vertices colours v true Htask Hcolour) as Hwhite.
      unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right]. lia.
  - destruct vs as [|v vs]; cbn [search_step] in Hstep.
    + inversion Hstep; subst next. unfold search_finite_credit, search_task_credit.
      cbn [search_colours search_tasks fold_right length]. lia.
    + destruct (trie_get v colours); inversion Hstep; subst next;
        unfold search_finite_credit, search_task_credit;
        cbn [search_colours search_tasks fold_right length]; lia.
  - inversion Hstep; subst next.
    pose proof (search_white_set_le g vertices colours v false) as Hwhite.
    unfold search_finite_credit, search_task_credit.
    cbn [search_colours search_tasks fold_right]. lia.
Qed.

(** Initial credit charges every listed occurrence, allowing duplicate vertices. *)
Lemma search_finite_initial g vertices roots :
  search_finite_credit g vertices (SearchState (map SearchRoot roots) Empty []) =
    4 * length vertices +
    2 * fold_right (fun v n => length (succs g v) + n) 0 vertices + length roots.
Proof.
  unfold search_finite_credit. cbn [search_colours search_tasks].
  assert (Htasks : search_task_credit (map SearchRoot roots) = length roots).
  { induction roots as [|v rest IH].
    - reflexivity.
    - change (1 + search_task_credit (map SearchRoot rest) = S (length rest)).
      rewrite IH. lia. }
  rewrite Htasks. unfold search_white.
  induction vertices as [|v rest IH]; cbn [fold_right length] in *;
    rewrite ?search_colour_empty in *; lia.
Qed.

(** Correct count caches suffice for completion on any successor-closed listed graph. *)
Lemma prepared_search_complete_closed g roots :
  counts_ok g ->
  (forall u v, In u (nodes g) -> edge (base g) u v -> In v (nodes g)) ->
  (forall r, In r roots -> In r (nodes g)) ->
  exists es, loopN (search_step (base g)) (search_budget g roots)
    (SearchState (map SearchRoot roots) Empty []) = inr es.
Proof.
  intros Hcounts Hclosed Hroots.
  eapply (loopN_done search_state (list event) (search_step (base g))
    (fun st => Forall (search_task_valid (fun v => In v (nodes g))) (search_tasks st))
    (search_finite_credit (base g) (nodes g))).
  - intros st next Hvalid Hstep. split.
    + eapply search_tasks_preserved; eassumption.
    + eapply search_finite_decreases; eassumption.
  - cbn [search_tasks]. apply Forall_forall. intros task Hin.
    apply in_map_iff in Hin. destruct Hin as [v [Heq Hin]]. subst task. apply Hroots. exact Hin.
  - rewrite search_finite_initial. unfold search_budget. rewrite !N.double_spec.
    destruct Hcounts as [Hnv Hne]. rewrite Hnv, Hne.
    destruct g as [[vertices adjacency] predecessors n e].
    cbn [nodes base graph_n graph_e]. lia.
Qed.

(** Seen vertices are exactly the keys with a stored search colour. *)
Definition search_seen (colours : ptrie bool) v := trie_get v colours <> None.

Local Lemma search_seen_set colours v b x :
  search_seen (PTrieCode.set v b colours) x <-> x = v \/ search_seen colours x.
Proof.
  unfold search_seen. rewrite search_colour_set.
  destruct (Pos.eqb_spec x v) as [Heq|Hneq].
  - subst x. split; [intros _; now left|intros _; discriminate].
  - split; [intro Hseen; now right|]. intros [Heq|Hseen]; [contradiction|exact Hseen].
Qed.

Local Lemma search_seen_set_keeps colours v b x :
  search_seen colours x -> search_seen (PTrieCode.set v b colours) x.
Proof.
  intro Hseen. apply search_seen_set. now right.
Qed.

(** Pending roots and unread row targets form the current search frontier. *)
Fixpoint search_frontier tasks : list positive :=
  match tasks with
  | [] => []
  | SearchRoot v :: rest => v :: search_frontier rest
  | SearchRow _ vs :: rest => vs ++ search_frontier rest
  | SearchLeave _ :: rest => search_frontier rest
  end.

Definition search_started colours task :=
  match task with
  | SearchRoot _ => True
  | SearchRow u _ | SearchLeave u => search_seen colours u
  end.

Local Lemma search_started_set colours v b tasks :
  Forall (search_started colours) tasks ->
  Forall (search_started (PTrieCode.set v b colours)) tasks.
Proof.
  apply Forall_impl. intros task Hstarted. destruct task; cbn [search_started] in *;
    auto using search_seen_set_keeps.
Qed.

(** Row and leaving tasks retain evidence that their source was entered. *)
Lemma search_started_preserved g st next :
  Forall (search_started (search_colours st)) (search_tasks st) ->
  search_step g st = inl next ->
  Forall (search_started (search_colours next)) (search_tasks next).
Proof.
  intros Hstarted Hstep. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hstarted as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [v|u vs|v].
  - cbn [search_step] in Hstep. destruct (trie_get v colours).
    + inversion Hstep; subst next. exact Htail.
    + inversion Hstep; subst next. constructor.
      * cbn [search_started]. apply search_seen_set. now left.
      * constructor.
        -- cbn [search_started]. apply search_seen_set. now left.
        -- apply search_started_set. exact Htail.
  - destruct vs as [|v vs]; cbn [search_step] in Hstep.
    + inversion Hstep; subst next. exact Htail.
    + destruct (trie_get v colours); inversion Hstep; subst next.
      * constructor; assumption.
      * constructor; [exact I|]. constructor; assumption.
  - inversion Hstep; subst next. apply search_started_set. exact Htail.
Qed.

(** Once a vertex is seen, every later task state still has its colour. *)
Lemma search_seen_preserved g st next v :
  search_step g st = inl next ->
  search_seen (search_colours st) v -> search_seen (search_colours next) v.
Proof.
  intros Hstep Hseen. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  destruct task as [u|u vs|u]; cbn [search_step] in Hstep.
  - destruct (trie_get u colours); inversion Hstep; subst next;
      cbn [search_colours] in *; auto using search_seen_set_keeps.
  - destruct vs as [|x xs]; [inversion Hstep; subst next; exact Hseen|].
    destruct (trie_get x colours); inversion Hstep; subst next; exact Hseen.
  - inversion Hstep; subst next. apply search_seen_set_keeps. exact Hseen.
Qed.

(** A pending target is either retained in the frontier or has become seen. *)
Lemma search_frontier_preserved g st next x :
  search_step g st = inl next -> In x (search_frontier (search_tasks st)) ->
  search_seen (search_colours next) x \/ In x (search_frontier (search_tasks next)).
Proof.
  intros Hstep Hin. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  destruct task as [v|u vs|v]; cbn [search_step] in Hstep.
  - cbn [search_tasks search_frontier] in Hin.
    destruct (trie_get v colours) eqn:Hcolour; inversion Hstep; subst next.
    + destruct Hin as [Heq|Hin].
      * subst x. left. unfold search_seen. cbn [search_colours]. rewrite Hcolour. discriminate.
      * now right.
    + destruct Hin as [Heq|Hin].
      * subst x. left. apply search_seen_set. now left.
      * right. cbn [search_tasks search_frontier]. apply in_or_app. now right.
  - destruct vs as [|v vs].
    + inversion Hstep; subst next. now right.
    + cbn [search_tasks search_frontier app] in Hin.
      destruct (trie_get v colours) eqn:Hcolour; inversion Hstep; subst next.
      * destruct Hin as [Heq|Hin].
        -- subst x. left. unfold search_seen. cbn [search_colours]. rewrite Hcolour.
           discriminate.
        -- now right.
      * now right.
  - inversion Hstep; subst next. now right.
Qed.

(** A newly seen vertex immediately contributes its whole successor row to the frontier. *)
Lemma search_new_successors g st next u v :
  Forall (search_started (search_colours st)) (search_tasks st) ->
  search_step g st = inl next ->
  search_seen (search_colours next) u -> ~ search_seen (search_colours st) u ->
  edge g u v -> In v (search_frontier (search_tasks next)).
Proof.
  intros Hstarted Hstep Hnew Hold Hedge. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hstarted as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [x|x vs|x]; cbn [search_step] in Hstep.
  - destruct (trie_get x colours); inversion Hstep; subst next.
    + contradiction.
    + apply search_seen_set in Hnew. destruct Hnew as [Heq|Hnew]; [subst u|contradiction].
      cbn [search_tasks search_frontier]. apply in_or_app. now left.
  - destruct vs as [|y vs]; [inversion Hstep; subst next; contradiction|].
    destruct (trie_get y colours); inversion Hstep; subst next; contradiction.
  - inversion Hstep; subst next. apply search_seen_set in Hnew.
    destruct Hnew as [Heq|Hnew]; [subst u; contradiction|contradiction].
Qed.

Definition search_cover g roots st : Prop :=
  (forall v, In v roots -> search_seen (search_colours st) v \/
    In v (search_frontier (search_tasks st))) /\
  (forall u v, search_seen (search_colours st) u -> edge g u v ->
    search_seen (search_colours st) v \/ In v (search_frontier (search_tasks st))).

(** The frontier always covers roots and successors not yet seen. *)
Lemma search_cover_preserved g roots st next :
  Forall (search_started (search_colours st)) (search_tasks st) ->
  search_cover g roots st -> search_step g st = inl next -> search_cover g roots next.
Proof.
  intros Hstarted [Hroots Hedges] Hstep. split.
  - intros v Hin. destruct (Hroots v Hin) as [Hseen|Hpending].
    + left. eapply search_seen_preserved; eassumption.
    + eapply search_frontier_preserved; eassumption.
  - intros u v Hseen Hedge. destruct (trie_get u (search_colours st)) eqn:Hcolour.
    + assert (Hold : search_seen (search_colours st) u).
      { unfold search_seen. rewrite Hcolour. discriminate. }
      destruct (Hedges u v Hold Hedge) as [Htarget|Hpending].
      * left. eapply search_seen_preserved; eassumption.
      * eapply search_frontier_preserved; eassumption.
    + right. eapply search_new_successors; try eassumption.
      unfold search_seen. rewrite Hcolour. tauto.
Qed.

Local Lemma search_colours_domain g domain st next :
  Forall (search_task_valid domain) (search_tasks st) ->
  (forall v, search_seen (search_colours st) v -> domain v) ->
  search_step g st = inl next ->
  forall v, search_seen (search_colours next) v -> domain v.
Proof.
  intros Hvalid Hdomain Hstep v Hseen. destruct st as [tasks colours es].
  destruct tasks as [|task tasks]; [discriminate Hstep|].
  inversion Hvalid as [|task0 tasks0 Htask Htail]; subst task0 tasks0.
  destruct task as [u|u vs|u]; cbn [search_step] in Hstep.
  - destruct (trie_get u colours); inversion Hstep; subst next.
    + apply Hdomain. exact Hseen.
    + apply search_seen_set in Hseen. destruct Hseen as [Heq|Hseen].
      * subst v. exact Htask.
      * apply Hdomain. exact Hseen.
  - destruct vs as [|x xs]; [inversion Hstep; subst next; apply Hdomain; exact Hseen|].
    destruct (trie_get x colours); inversion Hstep; subst next; apply Hdomain; exact Hseen.
  - inversion Hstep; subst next. apply search_seen_set in Hseen.
    destruct Hseen as [Heq|Hseen]; [subst v; exact Htask|apply Hdomain; exact Hseen].
Qed.

Local Lemma search_path_extend g u vs v w :
  path g u vs v -> edge g v w -> path g u (vs ++ [w]) w.
Proof.
  intro Hpath. induction Hpath as [u|u v vs x Huv Hpath IH]; intro Hedge.
  - cbn [app]. econstructor; [exact Hedge|constructor].
  - cbn [app]. econstructor; [exact Huv|]. apply IH. exact Hedge.
Qed.

Lemma search_reach_edge g roots u v : reach g roots u -> edge g u v -> reach g roots v.
Proof.
  intros [r [vs [Hroot Hpath]]] Hedge. exists r, (vs ++ [v]). split; [exact Hroot|].
  eapply search_path_extend; eassumption.
Qed.

Definition search_reach_invariant g roots st : Prop :=
  Forall (search_task_valid (reach g roots)) (search_tasks st) /\
  Forall (search_started (search_colours st)) (search_tasks st) /\
  (forall v, search_seen (search_colours st) v -> reach g roots v) /\
  search_cover g roots st.

Local Lemma search_frontier_roots roots : search_frontier (map SearchRoot roots) = roots.
Proof.
  induction roots as [|v rest IH]; cbn [map search_frontier]; [reflexivity|].
  now rewrite IH.
Qed.

(** Initially the frontier is exactly the supplied root list and no vertex is seen. *)
Lemma search_reach_initial g roots :
  search_reach_invariant g roots (SearchState (map SearchRoot roots) Empty []).
Proof.
  unfold search_reach_invariant. cbn [search_tasks search_colours]. split.
  - apply Forall_forall. intros task Hin. apply in_map_iff in Hin.
    destruct Hin as [v [Heq Hin]]. subst task. exists v, [v]. split; [exact Hin|constructor].
  - split.
    + induction roots as [|v rest IH]; cbn [map]; constructor; [exact I|exact IH].
    + split.
      * intros v Hseen. unfold search_seen in Hseen. rewrite search_colour_empty in Hseen.
        contradiction.
      * split.
        -- intros v Hin. right. cbn [search_tasks]. now rewrite search_frontier_roots.
        -- intros u v Hseen Hedge. unfold search_seen in Hseen.
           cbn [search_colours] in Hseen. rewrite search_colour_empty in Hseen. contradiction.
Qed.

(** Continuing search preserves reachability and complete frontier coverage. *)
Lemma search_reach_preserved g roots st next :
  search_reach_invariant g roots st -> search_step g st = inl next ->
  search_reach_invariant g roots next.
Proof.
  intros [Hvalid [Hstarted [Hdomain Hcover]]] Hstep. split.
  - eapply search_tasks_preserved; [|exact Hvalid|exact Hstep].
    intros u v Hu Hedge. eapply search_reach_edge; eassumption.
  - split; [eapply search_started_preserved; eassumption|]. split.
    + eapply search_colours_domain; eassumption.
    + eapply search_cover_preserved; eassumption.
Qed.

(** With an empty frontier, the seen set is exactly the rooted reachable set. *)
Lemma search_reach_finished g roots st :
  search_reach_invariant g roots st -> search_tasks st = [] ->
  forall v, search_seen (search_colours st) v <-> reach g roots v.
Proof.
  intros [Hvalid [Hstarted [Hsound [Hroots Hedges]]]] Htasks v. split; [apply Hsound|].
  intros [r [vs [Hroot Hpath]]].
  assert (Hfirst : search_seen (search_colours st) r).
  { destruct (Hroots r Hroot) as [Hseen|Hin]; [exact Hseen|].
    rewrite Htasks in Hin. contradiction. }
  clear Hroot. revert Hfirst.
  induction Hpath as [u|u v vs w Huv Hpath IH]; intro Hfirst; [exact Hfirst|].
  apply IH. destruct (Hedges u v Hfirst Huv) as [Hseen|Hin]; [exact Hseen|].
  rewrite Htasks in Hin. contradiction.
Qed.

(** Any loop result retains its invariant or is produced by an invariant terminal state. *)
Lemma search_loop_fuel_invariant {St Out} (step : St -> St + Out) (Inv : St -> Prop) :
  (forall st next, Inv st -> step st = inl next -> Inv next) ->
  forall fuel st, Inv st ->
  match loop_fuel step fuel st with
  | inl next => Inv next
  | inr result => exists last, Inv last /\ step last = inr result
  end.
Proof.
  intros Hstep fuel. induction fuel as [|fuel IH]; intros st Hinv; [exact Hinv|].
  cbn [loop_fuel]. destruct (step st) as [next|result] eqn:Hnext.
  - apply IH. eapply Hstep; eassumption.
  - exists st. auto.
Qed.


(** The pending leave tasks, from innermost to outermost, form the active stack. *)
Fixpoint search_active_tasks (tasks : list search_task) : list positive :=
  match tasks with
  | [] => []
  | SearchLeave v :: rest => v :: search_active_tasks rest
  | _ :: rest => search_active_tasks rest
  end.

(** Every pending row belongs to the innermost leave task following that row. *)
Fixpoint search_tasks_nested (tasks : list search_task) : Prop :=
  match tasks with
  | [] => True
  | SearchRow u _ :: rest =>
      (exists outer, search_active_tasks rest = u :: outer) /\ search_tasks_nested rest
  | _ :: rest => search_tasks_nested rest
  end.

(** Colours describe exactly the entering and leaving events already emitted. *)
Definition search_colours_ok (colours : ptrie bool) (es : list event) : Prop :=
  forall v,
    (trie_get v colours = None <-> ~ In (Enter v) es) /\
    (trie_get v colours = Some true <-> In (Enter v) es /\ ~ In (Leave v) es) /\
    (trie_get v colours = Some false <-> In (Leave v) es).

(** Structural search invariants hold even for truncated runs and malformed graphs. *)
Record search_shape (st : search_state) : Prop := {
  search_shape_tasks : search_tasks_nested (search_tasks st);
  search_shape_active_unique : NoDup (search_active_tasks (search_tasks st));
  search_shape_stack :
    trace_stack [] (rev (search_events st)) (search_active_tasks (search_tasks st));
  search_shape_entered_unique : NoDup (entered (rev (search_events st)));
  search_shape_colours : search_colours_ok (search_colours st) (search_events st);
  search_shape_active : forall v,
    trie_get v (search_colours st) = Some true <->
    In v (search_active_tasks (search_tasks st))
}.

(** Absent colours identify precisely the vertices not yet entered. *)
Lemma search_shape_none st : search_shape st -> forall v,
  trie_get v (search_colours st) = None <-> ~ In (Enter v) (search_events st).
Proof.
  intros Hshape v. exact (proj1 (search_shape_colours st Hshape v)).
Qed.

(** True colours identify entries whose matching leave has not yet occurred. *)
Lemma search_shape_true st : search_shape st -> forall v,
  trie_get v (search_colours st) = Some true <->
  In (Enter v) (search_events st) /\ ~ In (Leave v) (search_events st).
Proof.
  intros Hshape v. exact (proj1 (proj2 (search_shape_colours st Hshape v))).
Qed.

(** False colours identify precisely the vertices already left. *)
Lemma search_shape_false st : search_shape st -> forall v,
  trie_get v (search_colours st) = Some false <-> In (Leave v) (search_events st).
Proof.
  intros Hshape v. exact (proj2 (proj2 (search_shape_colours st Hshape v))).
Qed.

(** Filtering entering events commutes with concatenation. *)
Lemma search_entered_app first last :
  entered (first ++ last) = entered first ++ entered last.
Proof.
  induction first as [|e first IH]; [reflexivity|].
  destruct e; cbn [app entered]; now rewrite IH.
Qed.

(** Entered vertices and entering events have the same membership relation. *)
Lemma search_entered_member es v : In v (entered es) <-> In (Enter v) es.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  destruct e; cbn [entered In]; intuition congruence.
Qed.

(** A present colour identifies precisely an entry already recorded in the trace. *)
Lemma search_shape_seen st : search_shape st -> forall v,
  trie_get v (search_colours st) <> None <-> In (Enter v) (search_events st).
Proof.
  intros Hshape v. pose proof (search_shape_none st Hshape v) as Hnone. split.
  - intros Hseen.
    destruct (in_dec Pos.eq_dec v (entered (search_events st))) as [Hin|Hnot].
    + now apply search_entered_member in Hin.
    + exfalso. apply Hseen. apply Hnone. intros Hin. apply Hnot.
      now apply search_entered_member.
  - intros Hin Hwhite. exact (proj1 Hnone Hwhite Hin).
Qed.

(** Stack derivations compose at a common intermediate stack. *)
Lemma search_trace_stack_app initial first middle last final :
  trace_stack initial first middle -> trace_stack middle last final ->
  trace_stack initial (first ++ last) final.
Proof.
  intros Hfirst Hlast. induction Hfirst; cbn; eauto using trace_stack.
Qed.

Local Lemma search_colours_enter colours es v :
  search_colours_ok colours es -> trie_get v colours = None ->
  search_colours_ok (PTrieCode.set v true colours) (Enter v :: es).
Proof.
  intros Hcolours Hwhite u. destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. destruct (Hcolours v) as [Hnone [Htrue Hfalse]].
    assert (Henter : ~ In (Enter v) es) by now apply Hnone.
    assert (Hleave : ~ In (Leave v) es).
    { intro Hin. apply Hfalse in Hin. congruence. }
    rewrite PTrie.get_set_same. cbn. intuition congruence.
  - rewrite PTrie.get_set_other by exact Hneq.
    destruct (Hcolours u) as [Hnone [Htrue Hfalse]]. cbn. intuition congruence.
Qed.

Local Lemma search_colours_leave colours es v :
  search_colours_ok colours es -> trie_get v colours = Some true ->
  search_colours_ok (PTrieCode.set v false colours) (Leave v :: es).
Proof.
  intros Hcolours Hactive u. destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. destruct (Hcolours v) as [Hnone [Htrue Hfalse]].
    destruct (proj1 Htrue Hactive) as [Henter Hleave].
    rewrite PTrie.get_set_same. cbn. intuition congruence.
  - rewrite PTrie.get_set_other by exact Hneq.
    destruct (Hcolours u) as [Hnone [Htrue Hfalse]]. cbn. intuition congruence.
Qed.

Local Lemma search_colours_edge colours es kind u v :
  search_colours_ok colours es -> search_colours_ok colours (Edge kind u v :: es).
Proof.
  intros Hcolours w. destruct (Hcolours w) as [Hnone [Htrue Hfalse]].
  cbn. intuition congruence.
Qed.

(** Appending one fresh entry preserves uniqueness of the chronological entries. *)
Local Lemma search_entered_new es v :
  NoDup (entered (rev es)) -> ~ In (Enter v) es ->
  NoDup (entered (rev (Enter v :: es))).
Proof.
  intros Hunique Hfresh. cbn [rev]. rewrite search_entered_app. cbn [entered].
  apply NoDup_app; [exact Hunique|constructor; [tauto|constructor]|].
  intros u Hu [Heq|Hfalse]; [subst u|contradiction].
  apply Hfresh. apply (proj2 (in_rev es (Enter v))).
  now apply search_entered_member in Hu.
Qed.

(** Initial root tasks have no active vertices or events. *)
Lemma search_shape_initial roots :
  search_shape (SearchState (map SearchRoot roots) Empty []).
Proof.
  assert (Hactive : search_active_tasks (map SearchRoot roots) = []).
  { induction roots as [|r roots IH]; cbn; assumption || reflexivity. }
  assert (Hnested : search_tasks_nested (map SearchRoot roots)).
  { clear Hactive. induction roots as [|r roots IH]; cbn; assumption || exact I. }
  constructor; cbn [search_tasks search_events search_colours]; rewrite ?Hactive.
  - exact Hnested.
  - constructor.
  - constructor.
  - constructor.
  - intros v. rewrite PTrie.get_empty. cbn. intuition congruence.
  - intros v. rewrite PTrie.get_empty. cbn. intuition congruence.
Qed.

(** Replacing pending tasks preserves shape when their active stack is unchanged. *)
Local Lemma search_shape_retask tasks next colours es :
  search_shape (SearchState tasks colours es) -> search_tasks_nested next ->
  search_active_tasks next = search_active_tasks tasks ->
  search_shape (SearchState next colours es).
Proof.
  intros Hshape Hnested Hsame.
  destruct Hshape as [Htasks Hunique Hstack Hentered Hcolours Hactive].
  constructor; cbn [search_tasks search_colours search_events] in *;
    rewrite ?Hsame; assumption.
Qed.

(** Entering a fresh vertex pushes its row and leave task together. *)
Local Lemma search_shape_enter tasks colours es v row :
  search_shape (SearchState tasks colours es) -> trie_get v colours = None ->
  search_shape (SearchState (SearchRow v row :: SearchLeave v :: tasks)
    (PTrieCode.set v true colours) (Enter v :: es)).
Proof.
  intros Hshape Hwhite.
  destruct Hshape as [Htasks Hunique Hstack Hentered Hcolours Hactive].
  cbn [search_tasks search_colours search_events] in *.
  assert (Hfresh : ~ In (Enter v) es) by now apply (proj1 (Hcolours v)).
  assert (Hfresh_active : ~ In v (search_active_tasks tasks)).
  { intro Hin. apply Hactive in Hin. congruence. }
  constructor; cbn [search_tasks search_colours search_events
    search_tasks_nested search_active_tasks].
  - split; [eexists; reflexivity|exact Htasks].
  - now constructor.
  - cbn [rev]. eapply search_trace_stack_app; [exact Hstack|].
    constructor. constructor.
  - now apply search_entered_new.
  - now apply search_colours_enter.
  - intros u. destruct (Pos.eq_dec u v) as [Heq|Hneq].
    + subst u. rewrite PTrie.get_set_same. cbn. intuition congruence.
    + rewrite PTrie.get_set_other by exact Hneq.
      specialize (Hactive u). cbn. intuition congruence.
Qed.

(** An edge event leaves the active stack and all vertex colours unchanged. *)
Local Lemma search_shape_edge tasks colours es kind u v outer :
  search_shape (SearchState tasks colours es) ->
  search_active_tasks tasks = u :: outer ->
  search_shape (SearchState tasks colours (Edge kind u v :: es)).
Proof.
  intros Hshape Hhead.
  destruct Hshape as [Htasks Hunique Hstack Hentered Hcolours Hactive].
  cbn [search_tasks search_colours search_events] in *.
  constructor; cbn [search_tasks search_colours search_events].
  - exact Htasks.
  - exact Hunique.
  - cbn [rev]. eapply search_trace_stack_app; [exact Hstack|].
    rewrite Hhead. constructor. constructor.
  - cbn [rev]. rewrite search_entered_app. cbn [entered].
    now rewrite app_nil_r.
  - now apply search_colours_edge.
  - exact Hactive.
Qed.

(** Leaving a vertex pops its unique active occurrence and records its final colour. *)
Local Lemma search_shape_leave tasks colours es v :
  search_shape (SearchState (SearchLeave v :: tasks) colours es) ->
  search_shape (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es)).
Proof.
  intros Hshape.
  destruct Hshape as [Htasks Hunique Hstack Hentered Hcolours Hactive].
  cbn [search_tasks search_colours search_events
    search_tasks_nested search_active_tasks] in *.
  apply NoDup_cons_iff in Hunique. destruct Hunique as [Hfresh Hunique].
  assert (Htrue : trie_get v colours = Some true).
  { apply Hactive. now left. }
  constructor; cbn [search_tasks search_colours search_events].
  - exact Htasks.
  - exact Hunique.
  - cbn [rev]. eapply search_trace_stack_app; [exact Hstack|].
    constructor. constructor.
  - cbn [rev]. rewrite search_entered_app. cbn [entered].
    now rewrite app_nil_r.
  - now apply search_colours_leave.
  - intros u. destruct (Pos.eq_dec u v) as [Heq|Hneq].
    + subst u. rewrite PTrie.get_set_same. intuition congruence.
    + rewrite PTrie.get_set_other by exact Hneq.
      specialize (Hactive u). cbn in Hactive. intuition congruence.
Qed.

(** Every continuing machine step preserves the complete structural invariant. *)
Lemma search_shape_step g st next :
  search_shape st -> search_step g st = inl next -> search_shape next.
Proof.
  intros Hshape Hstep. destruct st as [[|task tasks] colours es];
    [discriminate Hstep|].
  destruct task as [v|u row|v].
  - cbn [search_step] in Hstep.
    destruct (trie_get v colours) as [active|] eqn:Hget;
      injection Hstep as Hnext; subst next.
    + eapply search_shape_retask; [exact Hshape| |reflexivity].
      exact (search_shape_tasks _ Hshape).
    + apply search_shape_enter; [|exact Hget].
      eapply search_shape_retask; [exact Hshape| |reflexivity].
      exact (search_shape_tasks _ Hshape).
  - pose proof (search_shape_tasks _ Hshape) as Hnested.
    cbn [search_tasks search_tasks_nested] in Hnested.
    destruct Hnested as [[outer Hhead] Htail].
    destruct row as [|v row].
    + cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
      eapply search_shape_retask; [exact Hshape|exact Htail|reflexivity].
    + cbn [search_step] in Hstep.
      destruct (trie_get v colours) as [active|] eqn:Hget;
        injection Hstep as Hnext; subst next.
      * eapply search_shape_edge with (outer := outer); [|exact Hhead].
        eapply search_shape_retask; [exact Hshape| |reflexivity].
        cbn [search_tasks_nested]. split; [now exists outer|exact Htail].
      * eapply search_shape_edge with (outer := outer); [|exact Hhead].
        eapply search_shape_retask; [exact Hshape| |reflexivity].
        cbn [search_tasks_nested]. split; [now exists outer|exact Htail].
  - cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
    now apply search_shape_leave.
Qed.

(** Stopping with an empty task list closes the stack and retains unique entries. *)
Lemma search_shape_stop g st es :
  search_shape st -> search_step g st = inr es ->
  NoDup (entered es) /\ trace_stack [] es [].
Proof.
  intros Hshape Hstop. destruct st as [[|task tasks] colours events].
  - cbn [search_step] in Hstop. injection Hstop as Hevents. subst es.
    rewrite rev_append_rev, app_nil_r. split.
    + exact (search_shape_entered_unique _ Hshape).
    + exact (search_shape_stack _ Hshape).
  - destruct task as [v|u row|v]; cbn [search_step] in Hstop.
    + destruct (trie_get v colours); discriminate Hstop.
    + destruct row as [|v row]; [discriminate Hstop|].
      destruct (trie_get v colours); discriminate Hstop.
    + discriminate Hstop.
Qed.

(** Every finite run either preserves a prefix shape or returns a complete nested trace. *)
Lemma search_shape_loop_fuel g fuel st : search_shape st ->
  match loop_fuel (search_step g) fuel st with
  | inl next => search_shape next
  | inr es => NoDup (entered es) /\ trace_stack [] es []
  end.
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hshape; cbn [loop_fuel].
  - exact Hshape.
  - destruct (search_step g st) as [next|es] eqn:Hstep.
    + apply IH. now apply (search_shape_step g st).
    + now apply (search_shape_stop g st).
Qed.

Local Opaque loopN.

(** A terminal search result reverses the stored chronology and has no tasks left. *)
Lemma search_stop_events g st es : search_step g st = inr es ->
  es = rev (search_events st) /\ search_tasks st = [].
Proof.
  intros Hstop. destruct st as [[|task tasks] colours events].
  - cbn [search_step] in Hstop. injection Hstop as Hevents. subst es.
    rewrite rev_append_rev, app_nil_r. split; reflexivity.
  - destruct task as [v|u row|v]; cbn [search_step] in Hstop.
    + destruct (trie_get v colours); discriminate Hstop.
    + destruct row as [|v row]; [discriminate Hstop|].
      destruct (trie_get v colours); discriminate Hstop.
    + discriminate Hstop.
Qed.

(** Every completed search visits exactly the rooted reachable vertices on any graph. *)
Lemma search_finished_reach g roots fuel es :
  loopN (search_step g) fuel (SearchState (map SearchRoot roots) Empty []) = inr es ->
  forall v, In v (entered es) <-> reach g roots v.
Proof.
  intro Hdone.
  pose proof (search_loop_fuel_invariant (search_step g)
    (fun st => search_reach_invariant g roots st /\ search_shape st)) as Hrun.
  assert (Hstep : forall st next,
      search_reach_invariant g roots st /\ search_shape st ->
      search_step g st = inl next ->
      search_reach_invariant g roots next /\ search_shape next).
  { intros st next [Hreach Hshape] Hnext. split.
    - eapply search_reach_preserved; eassumption.
    - eapply search_shape_step; eassumption. }
  specialize (Hrun Hstep (N.to_nat fuel) (SearchState (map SearchRoot roots) Empty [])
    (conj (search_reach_initial g roots) (search_shape_initial roots))).
  rewrite <- search_loopN_fuel, Hdone in Hrun.
  destruct Hrun as [last [[Hreach Hshape] Hstop]].
  destruct (search_stop_events g last es Hstop) as [Hes Htasks].
  intro v. rewrite Hes, search_entered_member, <- in_rev.
  rewrite <- (search_shape_seen last Hshape v).
  apply (search_reach_finished g roots last Hreach Htasks v).
Qed.

(** Count-correct successor-closed listed graphs need no distinctness assumption for reach. *)
Lemma prepared_search_reach_closed g roots :
  counts_ok g ->
  (forall u v, In u (nodes g) -> edge (base g) u v -> In v (nodes g)) ->
  (forall r, In r roots -> In r (nodes g)) ->
  forall v, In v (entered (prepared_search_trace g roots)) <-> reach (base g) roots v.
Proof.
  intros Hcounts Hclosed Hroots.
  destruct (prepared_search_complete_closed g roots Hcounts Hclosed Hroots) as [es Hdone].
  unfold prepared_search_trace. rewrite Hdone.
  apply (search_finished_reach (base g) roots (search_budget g roots) es Hdone).
Qed.

(** Even a truncated search never enters a vertex twice. *)
Lemma prepared_search_unique_raw g roots :
  NoDup (entered (prepared_search_trace g roots)).
Proof.
  pose proof (search_shape_loop_fuel (base g) (N.to_nat (search_budget g roots))
    (SearchState (map SearchRoot roots) Empty []) (search_shape_initial roots)) as Hshape.
  rewrite <- search_loopN_fuel in Hshape. unfold prepared_search_trace.
  destruct (loopN (search_step (base g)) (search_budget g roots)
    (SearchState (map SearchRoot roots) Empty [])) as [st|es].
  - rewrite rev_append_rev, app_nil_r. exact (search_shape_entered_unique st Hshape).
  - exact (proj1 Hshape).
Qed.

(** Completion closes every active DFS frame, including on duplicate listed vertices. *)
Lemma prepared_search_nested_closed g roots :
  counts_ok g ->
  (forall u v, In u (nodes g) -> edge (base g) u v -> In v (nodes g)) ->
  (forall r, In r roots -> In r (nodes g)) ->
  trace_stack [] (prepared_search_trace g roots) [].
Proof.
  intros Hcounts Hclosed Hroots.
  destruct (prepared_search_complete_closed g roots Hcounts Hclosed Hroots) as [es Hdone].
  pose proof (search_shape_loop_fuel (base g) (N.to_nat (search_budget g roots))
    (SearchState (map SearchRoot roots) Empty []) (search_shape_initial roots)) as Hshape.
  rewrite <- search_loopN_fuel, Hdone in Hshape. unfold prepared_search_trace. rewrite Hdone.
  exact (proj2 Hshape).
Qed.

(** Every edge records the target colour at precisely its preceding event prefix. *)
Definition search_event_kinds (es : list event) : Prop :=
  forall prefix kind u v suffix, es = prefix ++ Edge kind u v :: suffix ->
    event_kind_correct prefix kind v.

Local Lemma search_event_kinds_snoc es e :
  search_event_kinds es ->
  (forall kind u v, e = Edge kind u v -> event_kind_correct es kind v) ->
  search_event_kinds (es ++ [e]).
Proof.
  intros Hhistory Hlast prefix kind u v suffix Heq.
  apply app_eq_app in Heq.
  destruct Heq as [middle [[Hprefix Htail]|[Hprefix Htail]]].
  - destruct middle as [|first middle].
    + rewrite app_nil_r in Hprefix. subst es. cbn in Htail.
      injection Htail as Hevent Hsuffix. apply (Hlast kind u v). now symmetry.
    + cbn in Htail. injection Htail as Hevent Hsuffix. subst first.
      eapply Hhistory. exact Hprefix.
  - symmetry in Htail. apply elt_eq_unit in Htail as [Hevent [Hmiddle Hsuffix]].
    subst middle suffix. rewrite app_nil_r in Hprefix. subst prefix.
    apply (Hlast kind u v). now symmetry.
Qed.

(** The empty event history has no edge-kind obligations. *)
Lemma search_event_kinds_nil : search_event_kinds [].
Proof.
  intros prefix kind u v suffix Heq. destruct prefix; discriminate Heq.
Qed.

(** The next edge kind can be read directly from the exact colour observations. *)
Lemma search_shape_next_kind st v : search_shape st ->
  event_kind_correct (rev (search_events st))
    (match trie_get v (search_colours st) with
     | None => Tree
     | Some active => if active then Back else Done
     end) v.
Proof.
  intros Hshape. destruct (trie_get v (search_colours st)) as [[|]|] eqn:Hcolour;
    cbn [event_kind_correct].
  - destruct (proj1 (search_shape_true st Hshape v) Hcolour) as [Henter Hleave].
    split.
    + now apply (proj1 (in_rev (search_events st) (Enter v))).
    + intros Hin. apply Hleave. now apply (proj2 (in_rev (search_events st) (Leave v))).
  - apply (proj1 (in_rev (search_events st) (Leave v))).
    exact (proj1 (search_shape_false st Hshape v) Hcolour).
  - intros Hin. apply (proj1 (search_shape_none st Hshape v) Hcolour).
    now apply (proj2 (in_rev (search_events st) (Enter v))).
Qed.

(** Each continuing step retains old edge facts and gives a correct new edge kind. *)
Lemma search_event_kinds_step g st next :
  search_shape st -> search_event_kinds (rev (search_events st)) ->
  search_step g st = inl next -> search_event_kinds (rev (search_events next)).
Proof.
  intros Hshape Hhistory Hstep.
  destruct st as [[|task tasks] colours es]; [discriminate Hstep|].
  cbn [search_events] in Hhistory. destruct task as [v|u row|v].
  - cbn [search_step] in Hstep.
    destruct (trie_get v colours) as [active|] eqn:Hcolour;
      injection Hstep as Hnext; subst next; cbn [search_events rev].
    + exact Hhistory.
    + apply search_event_kinds_snoc; [exact Hhistory|].
      intros kind u w Hevent. discriminate Hevent.
  - destruct row as [|v row].
    + cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
      exact Hhistory.
    + pose proof (search_shape_next_kind _ v Hshape) as Hkind.
      cbn [search_colours search_events] in Hkind.
      cbn [search_step] in Hstep.
      destruct (trie_get v colours) as [active|] eqn:Hcolour;
        injection Hstep as Hnext; subst next; cbn [search_events rev].
      * apply search_event_kinds_snoc; [exact Hhistory|].
        intros kind source target Hevent. injection Hevent as Hkind' Hsource Htarget.
        now subst kind source target.
      * apply search_event_kinds_snoc; [exact Hhistory|].
        intros kind source target Hevent. injection Hevent as Hkind' Hsource Htarget.
        now subst kind source target.
  - cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
    cbn [search_events rev]. apply search_event_kinds_snoc; [exact Hhistory|].
    intros kind u w Hevent. discriminate Hevent.
Qed.

(** Correct edge kinds survive every finite run, including fuel exhaustion. *)
Lemma search_event_kinds_loop_fuel g fuel st :
  search_shape st -> search_event_kinds (rev (search_events st)) ->
  match loop_fuel (search_step g) fuel st with
  | inl next => search_event_kinds (rev (search_events next))
  | inr es => search_event_kinds es
  end.
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hshape Hhistory; cbn [loop_fuel].
  - exact Hhistory.
  - destruct (search_step g st) as [next|es] eqn:Hstep.
    + apply IH.
      * now apply (search_shape_step g st).
      * now apply (search_event_kinds_step g st).
    + destruct (search_stop_events g st es Hstep) as [Heq Htasks].
      now rewrite Heq.
Qed.

(** Pending rows retain their remaining successor occurrences for each source. *)
Fixpoint search_pending_targets (u : positive) (tasks : list search_task) : list positive :=
  match tasks with
  | [] => []
  | SearchRow v row :: rest =>
      if Pos.eqb u v then row ++ search_pending_targets u rest
      else search_pending_targets u rest
  | _ :: rest => search_pending_targets u rest
  end.

(** Emitted and pending targets partition the adjacency row of every entered source. *)
Definition search_row_ledger (g : digraph) (st : search_state) : Prop :=
  forall u, edge_targets u (rev (search_events st)) ++
      search_pending_targets u (search_tasks st) =
    match trie_get u (search_colours st) with
    | None => []
    | Some _ => succs g u
    end.

(** Collecting edge targets commutes with chronological concatenation. *)
Lemma search_edge_targets_app u first last :
  edge_targets u (first ++ last) = edge_targets u first ++ edge_targets u last.
Proof.
  induction first as [|e first IH]; [reflexivity|].
  destruct e as [v|v|kind v w]; cbn [app edge_targets]; try now rewrite IH.
  destruct (Pos.eqb u v); cbn [app]; now rewrite IH.
Qed.

(** Initial root tasks carry no pending adjacency rows. *)
Lemma search_pending_targets_roots u roots :
  search_pending_targets u (map SearchRoot roots) = [].
Proof.
  induction roots as [|v roots IH]; cbn; assumption || reflexivity.
Qed.

(** No row has been entered or emitted in the initial machine state. *)
Lemma search_row_ledger_initial g roots :
  search_row_ledger g (SearchState (map SearchRoot roots) Empty []).
Proof.
  intros u. cbn [search_events search_tasks search_colours rev edge_targets app].
  now rewrite search_pending_targets_roots, PTrie.get_empty.
Qed.

Local Lemma search_row_ledger_enter g tasks colours es v :
  search_row_ledger g (SearchState tasks colours es) -> trie_get v colours = None ->
  search_row_ledger g (SearchState (SearchRow v (succs g v) :: SearchLeave v :: tasks)
    (PTrieCode.set v true colours) (Enter v :: es)).
Proof.
  intros Hledger Hwhite u. specialize (Hledger u).
  cbn [search_events search_tasks search_colours] in *.
  cbn [rev]. rewrite search_edge_targets_app. cbn [edge_targets]. rewrite app_nil_r.
  cbn [search_pending_targets]. destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite Pos.eqb_refl, PTrie.get_set_same.
    rewrite Hwhite in Hledger. apply app_eq_nil in Hledger as [Hdone Hpending].
    now rewrite Hdone, Hpending, app_nil_r.
  - assert (Hdifferent : Pos.eqb u v = false) by now apply Pos.eqb_neq.
    rewrite Hdifferent, PTrie.get_set_other by exact Hneq. exact Hledger.
Qed.

Local Lemma search_row_ledger_edge g tasks colours es kind u v row :
  search_row_ledger g (SearchState (SearchRow u (v :: row) :: tasks) colours es) ->
  search_row_ledger g (SearchState (SearchRow u row :: tasks) colours (Edge kind u v :: es)).
Proof.
  intros Hledger source. specialize (Hledger source).
  cbn [search_events search_tasks search_colours] in *.
  cbn [rev]. rewrite search_edge_targets_app.
  cbn [edge_targets search_pending_targets] in *.
  destruct (Pos.eqb source u); cbn [app] in *.
  - rewrite <- app_assoc. exact Hledger.
  - now rewrite app_nil_r.
Qed.

Local Lemma search_row_ledger_leave g tasks colours es v :
  search_row_ledger g (SearchState (SearchLeave v :: tasks) colours es) ->
  trie_get v colours = Some true ->
  search_row_ledger g (SearchState tasks (PTrieCode.set v false colours) (Leave v :: es)).
Proof.
  intros Hledger Hactive u. specialize (Hledger u).
  cbn [search_events search_tasks search_colours search_pending_targets] in *.
  cbn [rev]. rewrite search_edge_targets_app. cbn [edge_targets]. rewrite app_nil_r.
  destruct (Pos.eq_dec u v) as [Heq|Hneq].
  - subst u. rewrite PTrie.get_set_same. now rewrite Hactive in Hledger.
  - rewrite PTrie.get_set_other by exact Hneq. exact Hledger.
Qed.

(** Each continuing transition preserves the exact row-occurrence accounting. *)
Lemma search_row_ledger_step g st next : search_shape st -> search_row_ledger g st ->
  search_step g st = inl next -> search_row_ledger g next.
Proof.
  intros Hshape Hledger Hstep. destruct st as [[|task tasks] colours es];
    [discriminate Hstep|].
  destruct task as [v|u row|v].
  - cbn [search_step] in Hstep.
    destruct (trie_get v colours) as [active|] eqn:Hcolour;
      injection Hstep as Hnext; subst next.
    + exact Hledger.
    + apply search_row_ledger_enter; [exact Hledger|exact Hcolour].
  - destruct row as [|v row].
    + cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
      intros source. specialize (Hledger source).
      cbn [search_events search_tasks search_colours search_pending_targets] in *.
      destruct (Pos.eqb source u); exact Hledger.
    + cbn [search_step] in Hstep.
      destruct (trie_get v colours) as [active|] eqn:Hcolour;
        injection Hstep as Hnext; subst next; now apply search_row_ledger_edge.
  - cbn [search_step] in Hstep. injection Hstep as Hnext. subst next.
    apply search_row_ledger_leave; [exact Hledger|].
    apply (proj2 (search_shape_active _ Hshape v)). now left.
Qed.

(** Completed traces enumerate every entered row and no unentered row. *)
Definition search_trace_rows (g : digraph) (es : list event) : Prop :=
  forall u,
    (In u (entered es) -> edge_targets u es = succs g u) /\
    (~ In u (entered es) -> edge_targets u es = []).

(** At a terminal state all pending targets have been emitted. *)
Lemma search_row_ledger_stop g st es :
  search_shape st -> search_row_ledger g st -> search_step g st = inr es ->
  search_trace_rows g es.
Proof.
  intros Hshape Hledger Hstop.
  destruct (search_stop_events g st es Hstop) as [Hevents Htasks].
  intros u. specialize (Hledger u). rewrite Htasks in Hledger.
  cbn [search_pending_targets] in Hledger. rewrite app_nil_r in Hledger. split.
  - intros Hin. apply search_entered_member in Hin. rewrite Hevents in Hin.
    apply (proj2 (in_rev (search_events st) (Enter u))) in Hin.
    apply (proj2 (search_shape_seen st Hshape u)) in Hin.
    destruct (trie_get u (search_colours st)); [now rewrite Hevents|contradiction].
  - intros Hnot. assert (Hwhite : trie_get u (search_colours st) = None).
    { apply (proj2 (search_shape_none st Hshape u)). intros Hin. apply Hnot.
      apply search_entered_member. rewrite Hevents.
      now apply (proj1 (in_rev (search_events st) (Enter u))). }
    rewrite Hwhite in Hledger. now rewrite Hevents.
Qed.

(** Every finite run retains its pending ledger or returns exact completed rows. *)
Lemma search_row_ledger_loop_fuel g fuel st :
  search_shape st -> search_row_ledger g st ->
  match loop_fuel (search_step g) fuel st with
  | inl next => search_row_ledger g next
  | inr es => search_trace_rows g es
  end.
Proof.
  revert st. induction fuel as [|fuel IH]; intros st Hshape Hledger; cbn [loop_fuel].
  - exact Hledger.
  - destruct (search_step g st) as [next|es] eqn:Hstep.
    + apply IH.
      * now apply (search_shape_step g st).
      * now apply (search_row_ledger_step g st).
    + now apply (search_row_ledger_stop g st).
Qed.

Module SearchCode (V : VISITOR_OPS) <: SEARCH_OPS V.
  Definition dfs (g : prepared) (roots : list positive) (s : V.state) : V.state :=
    fold_events V.enter V.leave V.edge (prepared_search_trace g roots) s.
End SearchCode.

Opaque search_trace.
Local Opaque prepared_search_trace.
Local Opaque loopN.

Module Search (V : VISITOR) <: SEARCH V.
  Include SearchCode V.

  Definition trace (g : prepared) (roots : list positive) := prepared_search_trace g roots.

  Lemma trace_depth_first : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists final, dfs_roots (base g) [] roots (trace g roots) final.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma dfs_fold : forall g roots s,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    dfs g roots s = fold_events V.enter V.leave V.edge (trace g roots) s.
  Proof.
    intros g roots s Hcounts Hgraph Hroots. unfold dfs, trace.
    reflexivity.
  Qed.

  Lemma trace_reach : forall g roots v,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In v (entered (trace g roots)) <-> reach (base g) roots v.
  Proof.
    intros [[vertices adjacency] predecessors n e] roots v Hcounts Hgraph Hroots.
    unfold trace. apply prepared_search_reach_closed; [exact Hcounts| |exact Hroots].
    exact (proj2 Hgraph).
  Qed.

  Lemma trace_unique : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> NoDup (entered (trace g roots)).
  Proof.
    intros g roots Hcounts Hgraph Hroots. apply prepared_search_unique_raw.
  Qed.

  Lemma trace_nested : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> trace_stack [] (trace g roots) [].
  Proof.
    intros [[vertices adjacency] predecessors n e] roots Hcounts Hgraph Hroots.
    unfold trace. apply prepared_search_nested_closed; [exact Hcounts| |exact Hroots].
    exact (proj2 Hgraph).
  Qed.

  Lemma trace_edges : forall g roots u,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) -> reach (base g) roots u ->
    Permutation (edge_targets u (trace g roots)) (succs (base g) u).
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_edges_sound : forall g roots kind u v,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    In (Edge kind u v) (trace g roots) -> reach (base g) roots u /\ edge (base g) u v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)

  Lemma trace_kinds : forall g roots prefix kind u v suffix,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    trace g roots = prefix ++ Edge kind u v :: suffix -> event_kind_correct prefix kind v.
  Proof. Admitted. (* CONVERT: GraphSearch: validity premises require the prepared machine proof. *)
End Search.

Module SearchT (V : VISITOR_T) <: SEARCH_ALL V.
  Include Search V.
  TimeFun dfs.
  Definition c_dfs : N := 1%N. (* STUB *)

  Definition n_reach (g : prepared) (roots : list positive) : nat :=
    length (entered (trace g roots)).
  Definition e_reach (g : prepared) (roots : list positive) : nat :=
    fold_right (fun u n => length (succs (base g) u) + n) 0 (entered (trace g roots)).
  Definition run_width (g : prepared) (roots : list positive) : nat :=
    graph_max (vertex_width roots)
      (fold_right (fun u w => graph_max (vertex_width (succs (base g) u)) w) 0
        (entered (trace g roots))).
  Definition work_bounded (g : prepared) (roots : list positive) (s : V.state) (B : nat) :=
    forall prefix suffix, trace g roots = prefix ++ suffix ->
      V.vwork (fold_events V.enter V.leave V.edge prefix s) <= B.

  Lemma T_dfs_le : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <=
      c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma dfs_bigO : bigO
    (fun '(g, roots, s, B) => work_bounded g roots s B)
    (fun '(g, roots, _, B) =>
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
          N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1))%N)
    (fun '(g, roots, s, _) => T_dfs g roots s).
  Proof. Admitted. (* STUB *)

  Definition search_step := search_step.
  TimeFun search_step.
  Definition search_budget := search_budget.
  TimeFun search_budget.
  Definition search_trace := prepared_search_trace.
  TimeFun search_trace.
  Definition k_step : N := 1%N. (* STUB *)
  Definition k_trace : N := 1%N. (* STUB *)
  Definition k_fold : N := 1%N. (* STUB *)
  Definition k_budget : N := 1%N. (* STUB *)

  Definition initial (roots : list positive) : search_state :=
    SearchState (map SearchRoot roots) Empty [].
  Definition advance (g : digraph) (s : search_state) : search_state :=
    match search_step g s with inl next => next | inr _ => s end.
  Definition machine_reachable (g : prepared) roots st : Prop :=
    exists n, Nat.iter n (advance (base g)) (initial roots) = st.
  Definition support (g : prepared) roots := entered (trace g roots).
  Definition unvisited (g : prepared) roots (st : search_state) : nat :=
    fold_right (fun v n =>
      match trie_get v (search_colours st) with
      | None => 2 + length (succs (base g) v) + n
      | Some _ => n
      end) 0 (support g roots).
  Definition pending (st : search_state) : nat :=
    fold_right (fun task n =>
      match task with
      | SearchRoot _ => 1 + n
      | SearchRow _ vs => 2 * length vs + 1 + n
      | SearchLeave _ => 1 + n
      end) 0 (search_tasks st).
  Definition potential g roots st : N := N.of_nat (2 * unvisited g roots st + pending st).
  Definition planned_fuel (g : prepared) : N := (2 * (nv g + ne g) + 1)%N.
  Definition event_width (w : nat) (e : event) : Prop :=
    match e with
    | Enter v | Leave v => Pos.size_nat v <= w
    | Edge _ u v => Pos.size_nat u <= w /\ Pos.size_nat v <= w
    end.
  Definition representation (st : search_state) : Prop :=
    NoDup (entered (rev (search_events st))) /\
    forall v,
      (trie_get v (search_colours st) = None <->
        ~ In (Enter v) (search_events st)) /\
      (trie_get v (search_colours st) = Some true <->
        In (Enter v) (search_events st) /\ ~ In (Leave v) (search_events st)) /\
      (trie_get v (search_colours st) = Some false <->
        In (Leave v) (search_events st)).
  Definition invariant g roots st : Prop :=
    machine_reachable g roots st /\ representation st /\
    exists suffix, trace g roots = rev (search_events st) ++ suffix.
  Definition all_rows (g : digraph) : nat :=
    fold_right (fun entry n => length (snd entry) + n) 0 (PTrieCode.elements (succ g)).
  Definition driver_credit g roots w st :=
    ((k_step * N.of_nat (w + 1) + 1) * potential g roots st)%N.
  Definition stop_budget g roots := (k_trace * N.of_nat (length (trace g roots) + 1))%N.

  Lemma F1_budget : forall g roots,
    search_budget g roots = (4 * (nv g + ne g + N.of_nat (length roots) + 1))%N.
  Proof.
    intros g roots.
    change (N.double (N.double (nv g + ne g + N.of_nat (length roots) + 1)) =
      4 * (nv g + ne g + N.of_nat (length roots) + 1))%N.
    rewrite !N.double_spec. lia.
  Qed.

  Local Transparent prepared_search_trace.

  Lemma F2_trace : forall g roots,
    trace g roots = search_trace g roots /\
    search_trace g roots =
      match loopN (search_step (base g)) (search_budget g roots) (initial roots) with
      | inl st => rev (search_events st)
      | inr es => es
      end.
  Proof.
    intros g roots. split; [reflexivity|].
    unfold search_trace, prepared_search_trace, initial.
    fold search_step search_budget.
    destruct (loopN (search_step (base g)) (search_budget g roots)
      (SearchState (map SearchRoot roots) Empty [])) as [st|es]; [|reflexivity].
    rewrite rev_append_rev, app_nil_r. reflexivity.
  Qed.

  Local Opaque prepared_search_trace.

  Lemma F3_initial : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots (initial roots) /\
    potential g roots (initial roots) =
      N.of_nat (4 * n_reach g roots + 2 * e_reach g roots + length roots).
  Proof. Admitted. (* STUB *)

  Lemma F4_step : forall g roots st next,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inl next ->
    invariant g roots next /\ (potential g roots next < potential g roots st)%N.
  Proof. Admitted. (* STUB *)

  Lemma F5_stop : forall g roots st es,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    search_tasks st = [] /\ es = trace g roots.
  Proof. Admitted. (* STUB *)

  Lemma F6_width : forall g roots st,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width (run_width g roots)) (search_events st).
  Proof. Admitted. (* STUB *)

  Lemma F7_events : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    length (trace g roots) = 2 * n_reach g roots + e_reach g roots.
  Proof. Admitted. (* STUB *)

  Lemma F8_fuel : forall g roots,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    exists es, loopN (search_step (base g)) (search_budget g roots)
      (initial roots) = inr es.
  Proof.
    intros [[vertices adjacency] predecessors n e] roots Hcounts Hgraph Hroots.
    apply prepared_search_complete_closed; [exact Hcounts| |exact Hroots].
    exact (proj2 Hgraph).
  Qed.

  Lemma T1_step : forall g roots st next w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> Forall (event_width w) (trace g roots) ->
    vertex_width roots <= w -> search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (w + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_stop : forall g roots st es,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    invariant g roots st -> search_step (base g) st = inr es ->
    (T_search_step (base g) st <= stop_budget g roots)%N.
  Proof. Admitted. (* STUB *)

  Lemma T3_loop : forall g roots w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget g roots) (initial roots) <=
    c_loopN * (driver_credit g roots w (initial roots) + stop_budget g roots +
      N.of_nat (N.size_nat (search_budget g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T4_trace : forall g roots w,
    counts_ok g -> wf_graph (base g) ->
    (forall r, In r roots -> In r (nodes g)) ->
    Forall (event_width w) (trace g roots) -> vertex_width roots <= w ->
    (T_search_trace g roots <= k_trace *
      (T_search_budget g roots + N.of_nat (length roots) +
        T_loopN (search_step (base g)) (T_search_step (base g))
          (search_budget g roots) (initial roots) +
        N.of_nat (length (trace g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** A continuing step taken within the fuel costs one key width of the run. *)
  Lemma T1_raw_step : forall g roots n st next,
    (N.of_nat n < search_budget g roots)%N ->
    Nat.iter n (advance (base g)) (initial roots) = st ->
    search_step (base g) st = inl next ->
    (T_search_step (base g) st <= k_step * N.of_nat (run_width g roots + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Steps taken within the fuel emit an event, retire a root or finish a row. *)
  Lemma F9_raw_count : forall g roots n,
    (N.of_nat n <= search_budget g roots)%N ->
    (forall i, i < n -> exists next,
      search_step (base g) (Nat.iter i (advance (base g)) (initial roots)) = inl next) ->
    n <= length (trace g roots) + length roots + n_reach g roots.
  Proof. Admitted. (* STUB *)

  (** The truncated loop pays its steps, one stop and the binary fuel width. *)
  Lemma T3_raw_loop : forall g roots,
    (T_loopN (search_step (base g)) (T_search_step (base g))
      (search_budget g roots) (initial roots) <=
    c_loopN * (k_step * N.of_nat (run_width g roots + 1) *
      N.of_nat (length (trace g roots) + length roots + n_reach g roots + 1) +
      stop_budget g roots + N.of_nat (N.size_nat (search_budget g roots)) + 1))%N.
  Proof. Admitted. (* STUB *)

  (** Every step emits an event or retires a root or row task, at the width of the run. *)
  Lemma T4_raw : forall g roots,
    (T_search_trace g roots <= k_trace *
      (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
        N.of_nat (run_width g roots + 1) +
       N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  Lemma T5_fold : forall g roots s B,
    work_bounded g roots s B ->
    (T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
      (trace g roots) s <=
    k_fold * N.of_nat (length (trace g roots) + 1) *
      (V.c_vis * N.of_nat (B + 1) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T6_dfs : forall g roots s,
    (T_dfs g roots s <= k_trace * (T_search_trace g roots +
      T_fold_events V.enter V.T_enter V.leave V.T_leave V.edge V.T_edge
        (trace g roots) s + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T7_public : forall g roots s B, work_bounded g roots s B ->
    (T_dfs g roots s <= c_dfs * (N.of_nat (n_reach g roots + e_reach g roots + length roots + 1) *
      (N.of_nat (run_width g roots) + V.c_vis * N.of_nat (B + 1)) +
        N.of_nat (N.size_nat (nv g) + N.size_nat (ne g) + 1)))%N.
  Proof. Admitted. (* STUB *)

  (** Each entered vertex contributes at most two events and its row on every input. *)
  Lemma F7b_events_raw : forall g roots,
      length (trace g roots) <= 2 * n_reach g roots + e_reach g roots.
  Proof. Admitted. (* STUB *)

End SearchT.

Transparent search_trace.
Transparent prepared_search_trace.
Transparent loopN.
