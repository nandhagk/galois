(** * Strongly connected components

    Tarjan's visitor tracks discovery numbers and pending components.
    For example, closing a cycle root emits its pending vertices together.
    Builds on: depth-first search and the SCC signature. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import Trie.
From Galois.Graph Require Import Data Spec SearchSig Search SccSig.
Import List.ListNotations.

Record tarjan_state := TarjanState {
  tarjan_disc : ptrie positive;
  tarjan_low : ptrie positive;
  tarjan_pending : list positive;
  tarjan_active : ptrie bool;
  tarjan_frames : list positive;
  tarjan_emitted : list (list positive);
  tarjan_owners : ptrie positive;
  tarjan_clock : positive;
  tarjan_next : positive
}.

Definition tarjan_initial := TarjanState Empty Empty [] Empty [] [] Empty 1%positive 1%positive.

Fixpoint tarjan_pop (root index : positive) (pending : list positive)
    (low : ptrie positive) (active : ptrie bool) (owners : ptrie positive)
    : list positive * list positive * ptrie positive * ptrie bool * ptrie positive :=
  match pending with
  | [] => ([], [], low, active, owners)
  | v :: rest =>
    let low' := PTrieCode.remove v low in
    let active' := PTrieCode.remove v active in
    let owners' := PTrieCode.set v index owners in
    if Pos.eqb v root then ([v], rest, low', active', owners') else
    let '(members, tail, low'', active'', owners'') :=
      tarjan_pop root index rest low' active' owners' in
    (v :: members, tail, low'', active'', owners'')
  end.

Module TarjanVisitor <: VISITOR_OPS.
  Definition state := tarjan_state.

  Definition enter (v : positive) (s : state) : state :=
    TarjanState (PTrieCode.set v (tarjan_clock s) (tarjan_disc s))
      (PTrieCode.set v (tarjan_clock s) (tarjan_low s)) (v :: tarjan_pending s)
      (PTrieCode.set v true (tarjan_active s)) (v :: tarjan_frames s)
      (tarjan_emitted s) (tarjan_owners s) (Pos.succ (tarjan_clock s)) (tarjan_next s).

  Definition lower (v n : positive) (s : state) : state :=
    match trie_get v (tarjan_low s) with
    | None => s
    | Some old => TarjanState (tarjan_disc s) (PTrieCode.set v (Pos.min old n) (tarjan_low s))
        (tarjan_pending s) (tarjan_active s) (tarjan_frames s) (tarjan_emitted s)
        (tarjan_owners s) (tarjan_clock s) (tarjan_next s)
    end.

  Definition edge (kind : edge_kind) (u v : positive) (s : state) : state :=
    match kind with
    | Tree => s
    | _ => match trie_get v (tarjan_active s), trie_get v (tarjan_disc s) with
           | Some true, Some n => lower u n s
           | _, _ => s
           end
    end.

  Definition leave (v : positive) (s : state) : state :=
    let frames := match tarjan_frames s with [] => [] | _ :: rest => rest end in
    let s' := TarjanState (tarjan_disc s) (tarjan_low s) (tarjan_pending s)
      (tarjan_active s) frames (tarjan_emitted s) (tarjan_owners s)
      (tarjan_clock s) (tarjan_next s) in
    match trie_get v (tarjan_low s), trie_get v (tarjan_disc s) with
    | Some l, Some d =>
      if Pos.eqb l d then
        let '(members, tail, low, active, owners) :=
          tarjan_pop v (tarjan_next s) (tarjan_pending s) (tarjan_low s)
            (tarjan_active s) (tarjan_owners s) in
        TarjanState (tarjan_disc s) low tail active frames
          (members :: tarjan_emitted s) owners (tarjan_clock s) (Pos.succ (tarjan_next s))
      else match frames with [] => s' | parent :: _ => lower parent l s' end
    | _, _ => s'
    end.
End TarjanVisitor.

Module TarjanSearch := SearchCode TarjanVisitor.

Module SccCode <: SCC_OPS.
  Definition run (g : prepared) : scc :=
    let result := TarjanSearch.dfs g (nodes g) tarjan_initial in
    Scc (tarjan_owners result) (rev (tarjan_emitted result)).
End SccCode.

Opaque search_trace.

Module Scc <: SCC.
  Include SccCode.
  Include SCC_SPEC.

  Lemma comp_spec : forall g, wf_graph (base g) -> forall u v,
    (exists i, trie_get u (comp (run g)) = Some i /\
      trie_get v (comp (run g)) = Some i) <->
    In u (nodes g) /\ In v (nodes g) /\ mutually_reachable (base g) u v.
  Proof. Admitted. (* SIG-QUESTION: landed Tarjan correctness assumes prepared readiness. *)

  Lemma comps_partition : forall g, wf_graph (base g) ->
    NoDup (concat (comps (run g))) /\
    (forall v, In v (concat (comps (run g))) <-> In v (nodes g)).
  Proof. Admitted. (* SIG-QUESTION: landed Tarjan correctness assumes prepared readiness. *)

  Lemma comps_nonempty : forall g, wf_graph (base g) ->
    Forall (fun vs => vs <> []) (comps (run g)).
  Proof. Admitted. (* SIG-QUESTION: landed Tarjan correctness assumes prepared readiness. *)

  Lemma owners_spec : forall g, wf_graph (base g) -> forall v i,
    trie_get v (comp (run g)) = Some i <->
    exists vs, nth_error (comps (run g)) (Nat.pred (Pos.to_nat i)) = Some vs /\ In v vs.
  Proof. Admitted. (* SIG-QUESTION: landed Tarjan correctness assumes prepared readiness. *)

  Lemma comps_order : forall g, wf_graph (base g) -> forall u v i j,
    edge (base g) u v -> trie_get u (comp (run g)) = Some i ->
    trie_get v (comp (run g)) = Some j -> (j <= i)%positive.
  Proof. Admitted. (* SIG-QUESTION: landed Tarjan correctness assumes prepared readiness. *)
End Scc.

Transparent search_trace.
