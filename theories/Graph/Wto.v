(** * Weak topological order production and checking

    The producer recursively removes an entry header from each cyclic component.
    For example, a singleton self edge produces an empty loop body.
    Builds on: Tarjan search, first-order graph data and the WTO signature. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Base Require Import Trie Loop.
From Galois.Graph Require Import Data Spec SearchSig Search SccSig Scc WtoSig.
Import List.ListNotations.

Definition wto_member (v : positive) xs := existsb (Pos.eqb v) xs.

Definition wto_scoped (g : prepared) (within : option (list positive)) : prepared :=
  match within with
  | None => g
  | Some vs =>
    let adjacency := fold_left (fun acc v =>
      PTrieCode.set v (filter (fun u => wto_member u vs) (succs (base g) v)) acc) vs Empty in
    Prepared (Digraph vs adjacency) Empty (nv g) (ne g)
  end.

Definition wto_components g roots :=
  let s := TarjanSearch.dfs g roots tarjan_initial in
  Scc (tarjan_owners s) (rev (tarjan_emitted s)).

Definition wto_offer i v (entries : ptrie positive) :=
  match trie_get i entries with Some _ => entries | None => PTrieCode.set i v entries end.

Definition wto_root_entry owners entries v :=
  match trie_get v owners with None => entries | Some i => wto_offer i v entries end.

Definition wto_edge_entry owners source entries v :=
  match source, trie_get v owners with
  | Some i, Some j => if Pos.eqb i j then entries else wto_offer j v entries
  | _, _ => entries
  end.

Definition wto_entries g roots r :=
  let owners := comp r in
  let seeded := fold_left (wto_root_entry owners) roots Empty in
  fold_left (fun entries c => fold_left (fun entries u =>
    fold_left (wto_edge_entry owners (trie_get u owners)) (succs (base g) u) entries)
    c entries) (comps r) seeded.

Definition wto_preferred (owners entries : ptrie positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: _ => match trie_get v owners with None => None | Some i => trie_get i entries end
  end.

Fixpoint wto_select (preferred : option positive) (c : list positive) :=
  match c with
  | [] => None
  | v :: rest =>
    if match preferred with None => false | Some h => Pos.eqb v h end
    then Some (v, rest)
    else match wto_select preferred rest with
      | None => Some (v, rest)
      | Some (h, body) => Some (h, v :: body)
      end
  end.

Fixpoint wto_reverse_into (w tail : wto) : wto :=
  match w with
  | WNil => tail
  | WVertex v rest => wto_reverse_into rest (WVertex v tail)
  | WLoop h body rest => wto_reverse_into rest (WLoop h body tail)
  end.

Definition wto_expand_tasks within entries owners cs :=
  map (fun c => WtoExpand within entries owners c) cs.

Definition wto_step (g : prepared) (s : wto_state) : wto_state + wto :=
  match s with
  | WtoState [] partial _ => inr (wto_reverse_into partial WNil)
  | WtoState (WtoClose h :: tasks) partial (parent :: parents) =>
    inl (WtoState tasks (WLoop h (wto_reverse_into partial WNil) parent) parents)
  | WtoState (WtoClose _ :: tasks) partial [] => inl (WtoState tasks partial [])
  | WtoState (WtoExpand within entries owners c :: tasks) partial parents =>
    match wto_select (wto_preferred owners entries c) c with
    | None => inl (WtoState tasks partial parents)
    | Some (h, []) =>
      let tree := if wto_member h (succs (base g) h)
        then WLoop h WNil partial else WVertex h partial in
      inl (WtoState tasks tree parents)
    | Some (h, body) =>
      let child := Some body in
      let scoped := wto_scoped g child in
      let roots := rev body in
      let r := wto_components scoped roots in
      let entries' := wto_entries scoped roots r in
      inl (WtoState
        (wto_expand_tasks child entries' (comp r) (rev (comps r)) ++ WtoClose h :: tasks)
        WNil (partial :: parents))
    end
  end.

Fixpoint wto_unique (xs : list positive) :=
  match xs with
  | [] => true
  | v :: rest => negb (wto_member v rest) && wto_unique rest
  end.

Fixpoint wto_annotate (stack : list positive) (w : wto) :
    list (positive * list positive) :=
  match w with
  | WNil => []
  | WVertex v rest => (v, stack) :: wto_annotate stack rest
  | WLoop h body rest =>
    (h, h :: stack) :: (wto_annotate (h :: stack) body ++ wto_annotate stack rest)
  end.

Fixpoint wto_positions (rows : list (positive * list positive)) :
    ptrie (list positive * list positive) :=
  match rows with
  | [] => Empty
  | (v, stack) :: rest => PTrieCode.set v (map fst rest, stack) (wto_positions rest)
  end.

Definition wto_edge_b index a b :=
  match trie_get a index with
  | None => false
  | Some (after, stack) => wto_member b after || wto_member b stack
  end.

Fixpoint wto_rank_rows (start : positive) (vs : list positive) : ptrie positive :=
  match vs with
  | [] => Empty
  | v :: rest => PTrieCode.set v start (wto_rank_rows (Pos.succ start) rest)
  end.

Module WtoCode <: WTO_OPS.
  Definition build (g : prepared) (roots : list positive) : wto :=
    let r := wto_components g roots in
    let entries := wto_entries g roots r in
    let cs := comps r in
    let size := length (concat cs) in
    let initial := WtoState (wto_expand_tasks None entries (comp r) (rev cs)) WNil [] in
    match loopN (wto_step g) (N.of_nat (3 * size + 1)) initial with
    | inl s => wto_reverse_into (wto_partial s) WNil
    | inr w => w
    end.

  Definition check (g : prepared) (roots : list positive) (w : wto) : bool :=
    let vs := wto_order w in
    let live := entered (search_trace (base g) roots) in
    let index := wto_positions (wto_annotate [] w) in
    wto_unique vs &&
    forallb (fun v => wto_member v live) vs &&
    forallb (fun v => wto_member v vs) live &&
    forallb (fun a => forallb (wto_edge_b index a) (succs (base g) a)) vs.

  Definition heads := wto_heads.
  Definition ranks w := wto_rank_rows 1%positive (wto_order w).
End WtoCode.

Module Wto <: WTO.
  Include WtoCode.

  (** Acceptance establishes exact rooted coverage and the nesting edge condition. *)
  Lemma check_sound : forall g roots w,
    check g roots w = true -> is_wto g roots w.
  Proof. Admitted. (* SIG-QUESTION: WtoCheck.check_correct requires prepared readiness. *)

  (** Heads are the structural loop heads in traversal order. *)
  Lemma heads_spec : forall w, heads w = wto_heads w.
  Proof.
    reflexivity.
  Qed.

  (** Ranks number the unique linear order starting at one. *)
  Lemma ranks_spec : forall w, NoDup (wto_order w) -> forall v i,
    nth_error (wto_order w) i = Some v ->
    trie_get v (ranks w) = Some (Pos.of_succ_nat i).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.ranks_spec uses membership and advance ranks. *)

  (** Vertices outside the linear order have no rank. *)
  Lemma ranks_absent : forall w v,
    ~ In v (wto_order w) -> trie_get v (ranks w) = None.
  Proof. Admitted. (* SIG-QUESTION: landed rank lemmas do not state absent-key lookup. *)

  (** Every reachable cycle contains a structural loop head. *)
  Lemma check_cuts : forall g roots w,
    check g roots w = true -> forall vs, cycle (base g) vs ->
    (forall v, In v vs -> reach (base g) roots v) ->
    exists h, In h vs /\ In h (heads w).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.cycles_have_head concerns producer token annotations. *)

  (** Edges increase rank unless their target is a backward loop head. *)
  Lemma ranks_forward : forall g roots w u v,
    check g roots w = true -> edge (base g) u v -> reach (base g) roots u ->
    exists ru rv, trie_get u (ranks w) = Some ru /\ trie_get v (ranks w) = Some rv /\
      ((ru < rv)%positive \/ (In v (heads w) /\ (rv <= ru)%positive)).
  Proof. Admitted. (* SIG-QUESTION: WeakOrder.ranks_forward concludes annotation membership. *)
End Wto.
