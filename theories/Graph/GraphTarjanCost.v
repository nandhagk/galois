(** * Tarjan visitor potential

    Stack credit pays for all popped-key work and component credit pays for final reversal.
    For example, emitting a large component consumes the credit of each removed stack cell.
    Builds on: GraphTarjanExact, GraphSearchCost and the public container cost laws. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostBound.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchCost GraphSccSpec GraphTarjan GraphTarjanExact GraphCondense GraphTarjanCondenseCost.
Import List.ListNotations Cost.Notations.

Module TarjanCost.
Local Open Scope N_scope.

(** A stack domain bounds precisely the keys that a later component pop can inspect. *)
Definition stack_domain w (s : Tarjan.state) :=
  Forall (fun v => key_bits positive_encoding v <= w) (Tarjan.stack s).

(** Event widths cover the vertex keys and the optional parent used by exit propagation. *)
Definition event_domain {E} w (ev : Search.event E) :=
  match ev with
  | Search.Enter v _ => key_bits positive_encoding v <= w
  | Search.Edge _ u v _ =>
    key_bits positive_encoding u <= w /\ key_bits positive_encoding v <= w
  | Search.Exit v parent =>
    key_bits positive_encoding v <= w /\
      match parent with
      | None => True
      | Some u => key_bits positive_encoding u <= w
      end
  end.

Definition id_cost w := 1 + 2 * w.
Definition pop_k w := 1 + 3 * id_cost w + w.
Definition scc_k : N := 32.

(** The potential reserves per-stack-cell pop work and one reversal tick per emitted component. *)
Definition potential w (s : Tarjan.state) :=
  N.of_nat (length (Tarjan.stack s)) * pop_k w +
    N.of_nat (length (Tarjan.emitted_rev s)).

Local Lemma get_cost {A} w v (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Map.get_c positive_encoding v m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.get_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma set_cost {A} w v a (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Map.set_c positive_encoding v a m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.set_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma remove_cost {A} w v (m : Map.t positive A) :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Map.remove_c positive_encoding v m) <= id_cost w.
Proof.
  intro Hwidth. rewrite Map.remove_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma mem_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (FinSet.mem_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.mem_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma add_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (FinSet.add_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.add_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

Local Lemma set_remove_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (FinSet.remove_c positive_encoding v s) <= id_cost w.
Proof.
  intro Hwidth. rewrite FinSet.remove_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws v).
  fold (key_bits positive_encoding v). unfold id_cost. nia.
Qed.

(** Popping spends at most the credit of its actual consumed prefix, for arbitrary maps and sets. *)
Theorem pop_cost w root i xs lows active own :
  Forall (fun v => key_bits positive_encoding v <= w) xs ->
  Cost.ticks (Tarjan.pop_c root i xs lows active own) +
    N.of_nat (length (Tarjan.tail (Tarjan.pop root i xs lows active own))) * pop_k w <=
      N.of_nat (length xs) * pop_k w.
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own Hwidth.
  - cbn [Tarjan.pop_c]. rewrite Tarjan.pop_equation.
    cbn [Tarjan.tail length]. autorewrite with galois_cost. lia.
  - inversion Hwidth as [|? ? Hv Hrest]; subst.
    specialize (IH (Map.remove positive_encoding v lows)
      (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own) Hrest).
    pose proof (remove_cost w v lows Hv).
    pose proof (set_remove_cost w v active Hv).
    pose proof (set_cost w v i own Hv).
    pose proof (Map.code_compare_cost v root).
    change (N.pos (Pos.size v) <= w) in Hv.
    cbn [Tarjan.pop_c]. autorewrite with galois_cost.
    fold (Map.remove positive_encoding v lows).
    fold (FinSet.remove positive_encoding v active).
    fold (Map.set positive_encoding v i own).
    fold (Map.code_compare v root).
    rewrite Tarjan.pop_equation.
    destruct (Map.code_compare v root);
      cbn [Tarjan.tail length]; autorewrite with galois_cost;
      rewrite Nat2N.inj_succ; unfold pop_k in *; nia.
Qed.

(** A pop leaves only keys from its original stack domain. *)
Theorem pop_domain w root i xs lows active own :
  Forall (fun v => key_bits positive_encoding v <= w) xs ->
  Forall (fun v => key_bits positive_encoding v <= w)
    (Tarjan.tail (Tarjan.pop root i xs lows active own)).
Proof.
  intro Hwidth.
  destruct (TarjanExact.pop_split root i xs lows active own) as [Hsplit _].
  rewrite Hsplit, Forall_app in Hwidth. exact (proj2 Hwidth).
Qed.

(** Entry pays its three insertions and reserves credit for the newly pushed vertex. *)
Theorem enter_cost w v s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Tarjan.enter_c v s) + potential w (Tarjan.enter v s) <=
    1 + 3 * id_cost w + pop_k w + potential w s.
Proof.
  intro Hwidth.
  pose proof (set_cost w v (Tarjan.clock s) (Tarjan.disc s) Hwidth).
  pose proof (set_cost w v (Tarjan.clock s) (Tarjan.low s) Hwidth).
  pose proof (add_cost w v (Tarjan.on_stack s) Hwidth).
  unfold Tarjan.enter_c. autorewrite with galois_cost.
  rewrite Tarjan.enter_equation.
  unfold potential. cbn [Tarjan.stack Tarjan.emitted_rev length].
  rewrite Nat2N.inj_succ. nia.
Qed.

(** Lowering spends at most one lookup and one insertion and leaves the potential unchanged. *)
Theorem lower_cost w v n s :
  key_bits positive_encoding v <= w ->
  Cost.ticks (Tarjan.lower_c v n s) + potential w (Tarjan.lower v n s) <=
    1 + 2 * id_cost w + potential w s.
Proof.
  intro Hwidth.
  pose proof (get_cost w v (Tarjan.low s) Hwidth).
  unfold Tarjan.lower_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Tarjan.low s)).
  rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [old|].
  - pose proof (set_cost w v (Pos.min old n) (Tarjan.low s) Hwidth).
    autorewrite with galois_cost. unfold potential.
    cbn [Tarjan.stack Tarjan.emitted_rev]. nia.
  - autorewrite with galois_cost. nia.
Qed.

(** Edge work retains the pending-set test and both discovery and low-link map work. *)
Theorem edge_cost w u v k s :
  key_bits positive_encoding u <= w -> key_bits positive_encoding v <= w ->
  Cost.ticks (Tarjan.edge_c u v k s) + potential w (Tarjan.edge u v k s) <=
    2 + 4 * id_cost w + potential w s.
Proof.
  intros Hu Hv.
  pose proof (mem_cost w v (Tarjan.on_stack s) Hv).
  pose proof (get_cost w v (Tarjan.disc s) Hv).
  destruct k; rewrite Tarjan.edge_equation; unfold Tarjan.edge_c;
    autorewrite with galois_cost; [nia| | |].
  all: fold (FinSet.mem positive_encoding v (Tarjan.on_stack s)).
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s));
    autorewrite with galois_cost; [|nia].
  all: fold (Map.get positive_encoding v (Tarjan.disc s)).
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|];
    autorewrite with galois_cost; [pose proof (lower_cost w u d s Hu); nia|nia].
Qed.

(** Emission pays for popping from stack credit and reserves its component-reversal tick. *)
Theorem emit_cost w root s :
  stack_domain w s ->
  Cost.ticks (Tarjan.emit_c root s) + potential w (Tarjan.emit root s) <=
    2 + potential w s.
Proof.
  intro Hdomain.
  pose proof (pop_cost w root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) Hdomain).
  unfold Tarjan.emit_c. autorewrite with galois_cost.
  fold (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)).
  rewrite Tarjan.emit_equation. unfold potential.
  cbn [Tarjan.stack Tarjan.emitted_rev length].
  rewrite Nat2N.inj_succ. nia.
Qed.

(** Exit retains both rank lookups and either its real component-pop or parent-link charge. *)
Theorem exit_cost w v parent s :
  key_bits positive_encoding v <= w ->
  (match parent with None => True | Some u => key_bits positive_encoding u <= w end) ->
  stack_domain w s ->
  Cost.ticks (Tarjan.exit_c v parent s) + potential w (Tarjan.exit v parent s) <=
    3 + 4 * id_cost w + potential w s.
Proof.
  intros Hv Hparent Hdomain.
  pose proof (get_cost w v (Tarjan.low s) Hv).
  pose proof (get_cost w v (Tarjan.disc s) Hv).
  unfold Tarjan.exit_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (Tarjan.low s)).
  fold (Map.get positive_encoding v (Tarjan.disc s)).
  rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|];
    autorewrite with galois_cost; try nia.
  destruct (Pos.eqb l d).
  - pose proof (emit_cost w v s Hdomain). nia.
  - destruct parent as [u|]; autorewrite with galois_cost; [|nia].
    pose proof (lower_cost w u l s Hparent). nia.
Qed.

(** The finite-domain visitor law bounds actual callback charges without quantifying over unbounded IDs. *)
Theorem amortised {E} w (ev : Search.event E) s :
  event_domain w ev -> stack_domain w s ->
  Cost.ticks (Visitor.apply_c Tarjan.visitor ev s) +
    potential w (Visitor.apply Tarjan.visitor ev s) <=
      scc_k * (1 + w) + potential w s.
Proof.
  intros Hevent Hstack. destruct ev as [v via|e u v k|v parent].
  - pose proof (enter_cost w v s Hevent).
    change (1 + Cost.ticks (Tarjan.enter_c v s) + potential w (Tarjan.enter v s) <=
      scc_k * (1 + w) + potential w s).
    unfold scc_k, pop_k, id_cost in *. nia.
  - destruct Hevent as [Hu Hv]. pose proof (edge_cost w u v k s Hu Hv).
    change (1 + Cost.ticks (Tarjan.edge_c u v k s) + potential w (Tarjan.edge u v k s) <=
      scc_k * (1 + w) + potential w s).
    unfold scc_k, id_cost in *. nia.
  - destruct Hevent as [Hv Hparent].
    pose proof (exit_cost w v parent s Hv Hparent Hstack).
    change (1 + Cost.ticks (Tarjan.exit_c v parent s) + potential w (Tarjan.exit v parent s) <=
      scc_k * (1 + w) + potential w s).
    unfold scc_k, id_cost in *. nia.
Qed.

Local Lemma lower_domain w v n s :
  stack_domain w s -> stack_domain w (Tarjan.lower v n s).
Proof.
  intro Hstack. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); exact Hstack.
Qed.

Local Lemma edge_domain w u v k s :
  stack_domain w s -> stack_domain w (Tarjan.edge u v k s).
Proof.
  intro Hstack. rewrite Tarjan.edge_equation.
  destruct k; try exact Hstack.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hstack.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hstack.
  all: now apply lower_domain.
Qed.

Local Lemma emit_domain w root s :
  stack_domain w s -> stack_domain w (Tarjan.emit root s).
Proof.
  intro Hstack. rewrite Tarjan.emit_equation.
  unfold stack_domain. cbn [Tarjan.stack]. now apply pop_domain.
Qed.

Local Lemma exit_domain w v parent s :
  stack_domain w s -> stack_domain w (Tarjan.exit v parent s).
Proof.
  intro Hstack. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|]; try exact Hstack.
  destruct (Pos.eqb l d); [now apply emit_domain|].
  destruct parent; [now apply lower_domain|exact Hstack].
Qed.

(** Bounded event keys preserve the stack-key domain for every visitor state in that domain. *)
Theorem domain_preserved {E} w (ev : Search.event E) s :
  event_domain w ev -> stack_domain w s ->
    stack_domain w (Visitor.apply Tarjan.visitor ev s).
Proof.
  intros Hevent Hstack. destruct ev as [v via|e u v k|v parent].
  - change (stack_domain w (Tarjan.enter v s)). rewrite Tarjan.enter_equation.
    unfold stack_domain. cbn [Tarjan.stack]. now constructor.
  - change (stack_domain w (Tarjan.edge u v k s)). now apply edge_domain.
  - change (stack_domain w (Tarjan.exit v parent s)). now apply exit_domain.
Qed.

(** The initial state belongs to every finite stack-key domain and has zero potential. *)
Theorem initial_domain w : stack_domain w Tarjan.initial /\ potential w Tarjan.initial = 0.
Proof.
  split; [constructor|reflexivity].
Qed.

(** Final component reversal is paid by the emitted-component part of the visitor potential. *)
Theorem result_cost w s : Cost.ticks (Tarjan.result_c s) <= potential w s.
Proof.
  unfold Tarjan.result_c. autorewrite with galois_cost. unfold potential. nia.
Qed.

Definition condense_k := TarjanCondenseCost.condense_k.

(** Condensation size includes every inspected outgoing occurrence and actual component-key width. *)
Definition condense_size {V E} (p : Prepared.t V E) r w := TarjanCondenseCost.size p r w.

(** Exact scoped condensation has a numeric linear bound without a second search or global scan. *)
Theorem condense_cost {V E} (p : Prepared.t V E) scope roots r w :
  Prepared.ready p -> Scc.exact p scope roots r -> SearchCost.width_bound p [] w ->
  Cost.ticks (Condense.of_scc_c p scope r) <= condense_k * condense_size p r w.
Proof.
  apply TarjanCondenseCost.cost.
Qed.

(** The numeric condensation bound applies uniformly to families of exact scoped SCC partitions. *)
Theorem condense_bigO {X V E} (p : X -> Prepared.t V E) scope roots r w :
  (forall x, Prepared.ready (p x)) ->
  (forall x, Scc.exact (p x) (scope x) (roots x) (r x)) ->
  (forall x, SearchCost.width_bound (p x) [] (w x)) ->
  bigO (fun x => condense_size (p x) (r x) (w x))
    (fun x => Cost.ticks (Condense.of_scc_c (p x) (scope x) (r x))).
Proof.
  intros Hready Hexact Hwidth. exists condense_k. intro x.
  pose proof (condense_cost (p x) (scope x) (roots x) (r x) (w x)
    (Hready x) (Hexact x) (Hwidth x)).
  unfold condense_k, TarjanCondenseCost.condense_k in *. nia.
Qed.

End TarjanCost.
