(** * Recursive SCC hierarchy

    One SCC decomposition supplies each forest layer and its charged entry-header index.
    For example, deleting the outer header of a nested cycle exposes its inner cyclic component.
    Builds on: GraphTarjan, GraphTarjanOperational and CostLoop. *)

From Stdlib Require Import List Bool PArith Arith Lia Permutation.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphTarjan GraphTarjanState GraphTarjanOperational.
Import List.ListNotations Cost.Notations.
Local Open Scope nat_scope.

Module HierRun.

(** A singleton component is cyclic exactly when its cached adjacency contains a self edge. *)
Definition self_loop_c {V E} (p : Prepared.t V E) v :=
  let* es := Prepared.succ_edges_c p v in
  existsb_c (fun eb =>
    let* comparison := Map.code_compare_c v (snd eb) in
    Cost.ret (match comparison with Eq => true | _ => false end)) es.

Definition self_loop {V E} (p : Prepared.t V E) v := Cost.value (self_loop_c p v).

(** The header index keeps the first witnessed entry for each actual component owner. *)
Definition offer_c i v (entries : Map.t positive positive) :=
  let* old := Map.get_c positive_encoding i entries in
  match old with
  | Some _ => Cost.ret entries
  | None => Map.set_c positive_encoding i v entries
  end.

Definition root_entry_c (owners : Map.t positive positive) entries v :=
  let* owner := Map.get_c positive_encoding v owners in
  match owner with
  | None => Cost.ret entries
  | Some i => offer_c i v entries
  end.

Definition edge_entry_c (owners : Map.t positive positive) source entries v :=
  let* target := Map.get_c positive_encoding v owners in
  match source, target with
  | Some i, Some j =>
    let* comparison := Map.code_compare_c i j in
    match comparison with
    | Eq => Cost.ret entries
    | _ => offer_c j v entries
    end
  | _, _ => Cost.ret entries
  end.

Definition vertex_entries_c {V E} (p : Prepared.t V E) owners entries u :=
  let* source := Map.get_c positive_encoding u owners in
  let* es := Prepared.succ_edges_c p u in
  fold_left_c (fun entries eb => edge_entry_c owners source entries (snd eb)) es entries.

(** Entry setup scans every supplied root occurrence and every outgoing occurrence of every member. *)
Definition entries_c {V E} (p : Prepared.t V E) roots (r : Scc.result) :=
  let* seeded := fold_left_c (root_entry_c (Scc.comp_of r)) roots Map.empty in
  fold_left_c (fun entries c =>
    fold_left_c (vertex_entries_c p (Scc.comp_of r)) c entries)
    (Scc.components r) seeded.

(** Selection removes one listed occurrence and prefers the indexed header when it is present. *)
Fixpoint select_c (preferred : option positive) (c : list positive) :
    Cost.t (option (positive * list positive)) :=
  match c with
  | [] => Cost.ret None
  | v :: rest =>
    Cost.step ;;
    let* selected :=
      match preferred with
      | None => Cost.ret false
      | Some h =>
        let* comparison := Map.code_compare_c v h in
        Cost.ret (match comparison with Eq => true | _ => false end)
      end in
    if selected then Cost.ret (Some (v, rest)) else
      let* next := select_c preferred rest in
      Cost.ret
        (match next with
        | None => Some (v, rest)
        | Some (h, body) => Some (h, v :: body)
        end)
  end.

Definition select preferred c := Cost.value (select_c preferred c).

(** Selection exposes its one recursive list step without reducing the key comparator. *)
Theorem select_equation preferred c :
  select preferred c =
  match c with
  | [] => None
  | v :: rest =>
    if match preferred with
      | None => false
      | Some h => match Map.code_compare v h with Eq => true | _ => false end
      end
    then Some (v, rest)
    else match select preferred rest with
      | None => Some (v, rest)
      | Some (h, body) => Some (h, v :: body)
      end
  end.
Proof.
  destruct c as [|v rest]; [reflexivity|].
  unfold select at 1. cbn [select_c]. autorewrite with galois_cost.
  destruct preferred as [h|]; autorewrite with galois_cost.
  - fold (Map.code_compare v h). destruct (Map.code_compare v h);
      autorewrite with galois_cost; reflexivity.
  - autorewrite with galois_cost. reflexivity.
Qed.

(** Every successful selection removes one occurrence from the input's size. *)
Theorem select_length preferred c h body :
  select preferred c = Some (h, body) -> S (length body) = length c.
Proof.
  revert h body. induction c as [|v rest IH]; intros h body;
    rewrite select_equation; [discriminate|].
  destruct (match preferred with
    | None => false
    | Some h => match Map.code_compare v h with Eq => true | _ => false end
    end).
  - intro Heq. inversion Heq. reflexivity.
  - destruct (select preferred rest) as [[head child]|] eqn:Hnext.
    + specialize (IH head child eq_refl).
      intro Heq. inversion Heq; subst. cbn [length]. lia.
    + intro Heq. inversion Heq. reflexivity.
Qed.

(** Selection fails only on the empty component. *)
Theorem select_none preferred c : select preferred c = None <-> c = [].
Proof.
  destruct c as [|v rest]; rewrite select_equation; [tauto|].
  destruct (match preferred with
    | None => false
    | Some h => match Map.code_compare v h with Eq => true | _ => false end
    end); [split; discriminate|].
  destruct (select preferred rest) as [[h body]|]; split; discriminate.
Qed.

(** Selection changes member order by moving its chosen header to the front. *)
Theorem select_permutation preferred c h body :
  select preferred c = Some (h, body) -> Permutation c (h :: body).
Proof.
  revert h body. induction c as [|v rest IH]; intros h body;
    rewrite select_equation; [discriminate|].
  destruct (match preferred with
    | None => false
    | Some h => match Map.code_compare v h with Eq => true | _ => false end
    end).
  - intro Heq. inversion Heq; subst. reflexivity.
  - destruct (select preferred rest) as [[head child]|] eqn:Hnext.
    + specialize (IH head child eq_refl).
      intro Heq. inversion Heq; subst.
      eapply Permutation_trans; [apply perm_skip, IH|apply perm_swap].
    + intro Heq. inversion Heq; subst. reflexivity.
Qed.

(** A child scope retains inherited blocking and restricts admission to the selected body. *)
Definition child_scope_c scope h body :=
  let* blocked := FinSet.add_c positive_encoding h (Scope.blocked scope) in
  let* within := FinSet.of_list_c positive_encoding body in
  Cost.ret (Scope.Make blocked (Some within)).

Definition child_scope scope h body := Cost.value (child_scope_c scope h body).

(** Child preparation stores exactly the selected body as its finite admission region. *)
Theorem child_scope_equation scope h body :
  child_scope scope h body =
    Scope.Make (FinSet.add positive_encoding h (Scope.blocked scope))
      (Some (FinSet.of_list positive_encoding body)).
Proof.
  reflexivity.
Qed.

(** Every member emitted in a child scope belongs to the selected finite body, without graph laws. *)
Theorem child_support {V E} (p : Prepared.t V E) scope h body roots c :
  In c (Scc.components (Tarjan.compute p (child_scope scope h body) roots)) ->
    NoDup c /\ incl c body.
Proof.
  intro Hin.
  destruct (TarjanOperational.component_support p _ roots c Hin) as [Hnodup Hadmits].
  split; [exact Hnodup|]. intros v Hv. specialize (Hadmits v Hv).
  rewrite Scope.admits_equation, child_scope_equation in Hadmits.
  apply andb_true_iff in Hadmits. cbn [Scope.within] in Hadmits.
  apply (proj1 (TarjanStateFacts.member_test v body)).
  rewrite <- FinSet.mem_of_list. exact (proj2 Hadmits).
Qed.

(** Building siblings invokes the supplied expansion once per listed component. *)
Fixpoint assemble_c (cs : list (list positive))
    (expand : forall c, In c cs -> Cost.t (option Hier.tree)) : Cost.t Hier.forest :=
  match cs as current return
      (forall c, In c current -> Cost.t (option Hier.tree)) -> Cost.t Hier.forest with
  | [] => fun _ => Cost.ret Hier.Nil
  | c :: rest => fun expand =>
    Cost.step ;;
    let* tree := expand c (or_introl eq_refl) in
    let* forest := assemble_c rest (fun d Hin => expand d (or_intror Hin)) in
    Cost.ret (match tree with None => forest | Some tree => Hier.Cons tree forest end)
  end expand.

(** Extensional expansion callbacks produce the same sibling forest and cost. *)
Theorem assemble_ext cs f g :
  (forall c Hin, f c Hin = g c Hin) -> assemble_c cs f = assemble_c cs g.
Proof.
  revert f g. induction cs as [|c rest IH]; intros f g Hsame; [reflexivity|].
  cbn [assemble_c]. rewrite Hsame.
  rewrite (IH (fun d Hin => f d (or_intror Hin))
    (fun d Hin => g d (or_intror Hin)) ltac:(intros; apply Hsame)).
  reflexivity.
Qed.

Definition job := (Scope.t * Map.t positive positive * Map.t positive positive *
  list positive)%type.

Definition size (x : job) := length (snd x).

Definition expand_layer {V E} (p : Prepared.t V E) (x : job)
    (recur : forall y, size y < size x -> Cost.t (option Hier.tree)) :
    Cost.t (option Hier.tree).
Proof.
  destruct x as [[[scope entries] owners] c].
  refine (Cost.bind Cost.step (fun _ => _)).
  refine (Cost.bind
    (match c with
    | [] => Cost.ret None
    | v :: _ =>
      let* owner := Map.get_c positive_encoding v owners in
      match owner with None => Cost.ret None | Some i => Map.get_c positive_encoding i entries end
    end)
    (fun preferred => _)).
  refine (Cost.bind
    (Cost.refine (P := fun selection => selection = select preferred c)
      (select_c preferred c) eq_refl) (fun selected => _)).
  destruct selected as [selection Hselection].
  destruct selection as [[h body]|]; [|exact (Cost.ret None)].
  destruct body as [|v rest].
  - exact (let* cyclic := self_loop_c p h in
      Cost.ret (Some (if cyclic then Hier.Component h Hier.Nil else Hier.Vertex h))).
  - set (body := v :: rest) in *.
    refine (Cost.bind
      (Cost.refine (P := fun child => child = child_scope scope h body)
        (child_scope_c scope h body) eq_refl)
      (fun certified_child => _)).
    destruct certified_child as [child Hchild].
    refine (Cost.bind (rev_c body) (fun roots => _)).
    refine (Cost.bind
      (Cost.refine (P := fun r => forall d, In d (Scc.components r) ->
        NoDup d /\ forall z, In z d -> Scope.admits child z = true)
        (Tarjan.compute_c p child roots) _) (fun certified => _)).
    + exact (fun d Hin => TarjanOperational.component_support p child roots d Hin).
    + destruct certified as [r Hr].
      refine (Cost.bind (entries_c p roots r) (fun entries' => _)).
      refine (Cost.bind
        (Cost.refine (P := fun cs => cs = rev (Scc.components r))
          (rev_c (Scc.components r)) _) (fun ordered => _)).
      * apply value_rev_c.
      * destruct ordered as [cs Hcs].
        refine (Cost.bind (assemble_c cs (fun d Hin =>
          recur (child, entries', Scc.comp_of r, d) _))
          (fun forest => Cost.ret (Some (Hier.Component h forest)))).
        unfold size. cbn [snd].
        pose proof (select_length preferred c h body (eq_sym Hselection)) as Hlength.
        destruct (Hr d ltac:(rewrite Hcs in Hin;
          apply (proj2 (in_rev _ _)) in Hin; exact Hin)) as [Hnodup Hadmitted].
        assert (Hsub : incl d body).
        { intros z Hz. specialize (Hadmitted z Hz).
          rewrite Hchild, Scope.admits_equation, child_scope_equation in Hadmitted.
          apply andb_true_iff in Hadmitted. cbn [Scope.within] in Hadmitted.
          apply (proj1 (TarjanStateFacts.member_test z body)).
          rewrite <- FinSet.mem_of_list. exact (proj2 Hadmitted). }
        pose proof (NoDup_incl_length Hnodup Hsub). lia.
Defined.

(** Component-layer results and charges depend pointwise on their recursive computations. *)
Theorem expand_layer_ext {V E} (p : Prepared.t V E) x f g :
  (forall y Hlt, f y Hlt = g y Hlt) -> expand_layer p x f = expand_layer p x g.
Proof.
  intro Hsame. destruct x as [[[scope entries] owners] c].
  unfold expand_layer. cbn beta iota zeta.
  apply Cost.bind_ext. intros [].
  apply Cost.bind_ext. intro preferred.
  apply Cost.bind_ext. intros [selection Hselection].
  destruct selection as [[h body]|]; [|reflexivity].
  destruct body as [|v rest]; [reflexivity|].
  apply Cost.bind_ext. intros [child Hchild].
  apply Cost.bind_ext. intro roots.
  apply Cost.bind_ext. intros [r Hr].
  apply Cost.bind_ext. intro entries'.
  apply Cost.bind_ext. intros [cs Hcs].
  match goal with
  | |- Cost.bind (assemble_c ?rows ?left) ?finish =
      Cost.bind (assemble_c ?rows ?right) ?finish =>
    assert (Hassembly : assemble_c rows left = assemble_c rows right)
      by (apply assemble_ext; intros; apply Hsame);
    now rewrite Hassembly
  end.
Qed.

(** Component expansion recurses on the strict size decrease proved for its actual child SCCs. *)
Definition expand_c {V E} (p : Prepared.t V E) : job -> Cost.t (option Hier.tree) :=
  fix_wf size (expand_layer p).

(** The well-founded expansion unfolds through its own actual SCC layer. *)
Theorem expand_equation {V E} (p : Prepared.t V E) x :
  expand_c p x = expand_layer p x (fun y _ => expand_c p y).
Proof.
  apply fix_wf_unfold, expand_layer_ext.
Qed.

(** The outer layer accepts arbitrary scopes and root occurrences without caller proof arguments. *)
Definition compute_c {V E} (p : Prepared.t V E) scope roots : Cost.t Hier.forest :=
  let* r := Tarjan.compute_c p scope roots in
  let* entries := entries_c p roots r in
  let* ordered := rev_c (Scc.components r) in
  assemble_c ordered (fun c _ => expand_c p (scope, entries, Scc.comp_of r, c)).

Definition compute {V E} (p : Prepared.t V E) scope roots :=
  Cost.value (compute_c p scope roots).

(** The outer computation reverses actual Tarjan emission and expands those same components. *)
Theorem compute_equation {V E} (p : Prepared.t V E) scope roots :
  compute p scope roots =
    let r := Tarjan.compute p scope roots in
    let entries := Cost.value (entries_c p roots r) in
    Cost.value (assemble_c (rev (Scc.components r))
      (fun c _ => expand_c p (scope, entries, Scc.comp_of r, c))).
Proof.
  unfold compute, compute_c. rewrite !Cost.value_bind, value_rev_c. reflexivity.
Qed.

End HierRun.
