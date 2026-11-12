(** * Variable presentations

    Edge readers list uses before definitions and node readers list exit observations.
    For example, an assignment reads its operands before replacing its destination.
    Builds on: Program.CfgSig and Base keys. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time BigO.
From Galois.Base Require Import KeySig Trie.
From Galois.Program Require Import SemanticsSig CfgSig.

Module Type VARS_OPS (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS).
  Parameter uses defs : P.t -> E.t -> list X.t.
  Parameter exits : P.t -> N.t -> list X.t.
  Parameter universe : P.t -> list X.t.
End VARS_OPS.

Module Type VARS_SPEC (P : TYPE) (N : KEY_OPS) (E : TYPE)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (Import V : VARS_OPS P N E C X).
  Definition occurrences p :=
    flat_map (fun e => uses p e ++ defs p e) (C.edges p) ++
      flat_map (exits p) (C.nodes p).
  Definition occurs p x :=
    (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
    (exists n, In n (C.nodes p) /\ In x (exits p n)).
  Definition occurrence_width p :=
    fold_right Nat.max 0%nat (map (fun x => Pos.size_nat (X.encode x)) (occurrences p)).
End VARS_SPEC.

Module Type VARS_LAWS (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (X : KEY) (Import V : VARS_OPS P N E C X).
  (** The universe contains exactly the syntactic variable occurrences. *)
  Parameter universe_spec : forall p x,
    In x (universe p) <->
      (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
      (exists n, In n (C.nodes p) /\ In x (exits p n)).
  (** The prepared universe contains each variable once. *)
  Parameter universe_nodup : forall p, NoDup (universe p).
End VARS_LAWS.

Module Type VARS (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (X : KEY) :=
  VARS_OPS P N E C X <+ VARS_SPEC P N E C X <+ VARS_LAWS P N E C X.

Module Type VARS_TIME (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T) (Import V : VARS P N E C X).
  Parameter T_uses T_defs : P.t -> E.t -> N.
  Parameter T_exits : P.t -> N.t -> N.
  Parameter T_universe : P.t -> N.
  Parameter c_vars : N.
  (** Edge uses pay for the edge key and the returned variables. *)
  Parameter T_uses_le : forall p e,
    (T_uses p e <= c_vars * N.of_nat (E.bits e + length (uses p e) + 1))%N.
  (** Edge definitions pay for the edge key and the returned variables. *)
  Parameter T_defs_le : forall p e,
    (T_defs p e <= c_vars * N.of_nat (E.bits e + length (defs p e) + 1))%N.
  (** Exit observations pay for the node key and the returned variables. *)
  Parameter T_exits_le : forall p n,
    (T_exits p n <= c_vars * N.of_nat (N.bits n + length (exits p n) + 1))%N.
  Definition universe_work p :=
    (C.T_edges p + C.T_nodes p +
      fold_right N.add 0%N (map (fun e => T_uses p e + T_defs p e)%N (C.edges p)) +
      fold_right N.add 0%N (map (T_exits p) (C.nodes p)) +
      N.of_nat (length (C.edges p) + length (C.nodes p) + length (occurrences p) + 1) *
        N.of_nat (occurrence_width p + 1) +
      fold_right N.add 0%N (map X.T_encode (occurrences p)))%N.
  (** Universe preparation charges every reader, encoding and trie traversal. *)
  Parameter T_universe_le : forall p, (T_universe p <= c_vars * universe_work p)%N.
  (** The universe has the aggregate reader and bit-width bound. *)
  Parameter universe_bigO : bigO (fun _ : P.t => True) universe_work T_universe.
End VARS_TIME.

Module Type VARS_T (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T) :=
  VARS P N E C X <+ VARS_TIME P N E C X.

Module Type VARS_PLAN (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T) (Import V : VARS_T P N E C X).
  (** Flattening syntax preserves exactly the edge and exit occurrences. *)
  Parameter F1_occurrences : forall p x, In x (occurrences p) <-> occurs p x.
  (** Deduplicating the occurrence scan gives the prepared universe. *)
  Parameter F2_universe : forall p x, In x (universe p) <-> In x (occurrences p).
  Parameter seen : P.t -> ptrie X.t.
  Parameter T_seen : P.t -> N.
  Parameter k_seen k_collect : N.
  (** The deduplicating trie stores each occurrence at its own encoding. *)
  Parameter F3_seen : forall p,
    seen p = fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p)
      PTrieCode.empty.
  (** The deduplicating trie has at most one skeleton node per occurrence key bit. *)
  Parameter F4_seen_nodes : forall p,
    PTrie.nodes (seen p) <= length (occurrences p) * occurrence_width p.
  (** Building the trie pays each reader, encoding and insertion path. *)
  Parameter T1_seen : forall p,
    (T_seen p <= k_seen * universe_work p)%N.
  (** Collecting values pays one skeleton walk and one reversal. *)
  Parameter T2_universe : forall p,
    (T_universe p <= k_collect * (T_seen p +
      N.of_nat (length (occurrences p) + 1) * N.of_nat (occurrence_width p + 1)))%N.
End VARS_PLAN.

Module Type VARS_ALL (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T) :=
  VARS_T P N E C X <+ VARS_PLAN P N E C X.

Module Type VARS_LINK (P : TYPE) (N : KEY) (E : TYPE)
    (C : CFG P N E) (X : KEY) (V : VARS P N E C X)
    (M : SEMANTICS P) (T : TRACES P M) (L : CFG_LINK P N E C M) (Val : TYPE).
  Parameter get : M.state -> X.t -> Val.t.
  (** A variable omitted from the definitions retains its value across the edge. *)
  Parameter defs_frame : forall p s t e x,
    reachable (M.initial p) (M.step p) s -> M.step p s t -> L.taken p s t e ->
    ~ In x (V.defs p e) -> get t x = get s x.
  (** Agreement on uses reproduces the same labelled edge and agrees on its definitions. *)
  Parameter uses_determine : forall p s s' t e tr,
    reachable (M.initial p) (M.step p) s -> T.lstep p s tr s' ->
    reachable (M.initial p) (M.step p) t -> L.point t = L.point s ->
    L.taken p s s' e -> (forall x, In x (V.uses p e) -> get s x = get t x) ->
    exists t', T.lstep p t tr t' /\ L.taken p t t' e /\
      forall x, In x (V.defs p e) -> get s' x = get t' x.
  (** Agreement on exit observations determines every ending classification. *)
  Parameter exits_determine : forall p s t,
    reachable (M.initial p) (M.step p) s -> reachable (M.initial p) (M.step p) t ->
    L.point t = L.point s ->
    (forall x, In x (V.exits p (L.point s)) -> get s x = get t x) ->
    (T.final p s <-> T.final p t) /\ (T.trapped p s <-> T.trapped p t) /\
      (T.stopped p s <-> T.stopped p t).
End VARS_LINK.
