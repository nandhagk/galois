(** * Variable presentations

    Edge and exit readers use first-order tables keyed by encoded identities.
    For example, an absent edge binding has no uses or definitions.
    Builds on: Program.VarsSig and Base.Trie. *)

From Stdlib Require Import List NArith.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Trie Code.
From Galois.Program Require Import CfgSig VarsSig.
Import Code.List.

Module Nat.
  TimeFun Nat.max.
End Nat.

Record var_tables (X : Type) := VarTables {
  edge_uses : ptrie (list X);
  edge_defs : ptrie (list X);
  node_exits : ptrie (list X)
}.

Arguments VarTables {X}.
Arguments edge_uses {X}.
Arguments edge_defs {X}.
Arguments node_exits {X}.

TimeFun edge_uses.
TimeFun edge_defs.
TimeFun node_exits.

Module Type VARS_DATA (P : TYPE) (X : KEY_OPS).
  Parameter tables : P.t -> var_tables X.t.
End VARS_DATA.

Module Type VARS_DATA_TIME (P : TYPE) (X : KEY_T) (Import D : VARS_DATA P X).
  Parameter T_tables : P.t -> N.
  Parameter c_tables : N.
  Parameter T_tables_le : forall p, (T_tables p <= c_tables)%N.
End VARS_DATA_TIME.

Module Type VARS_DATA_T (P : TYPE) (X : KEY_T) :=
  VARS_DATA P X <+ VARS_DATA_TIME P X.

Module VarsCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (D : VARS_DATA P X)
    <: VARS_OPS P N E C X.
  Definition uses p e :=
    match trie_get (E.encode e) (edge_uses (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition defs p e :=
    match trie_get (E.encode e) (edge_defs (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition exits p n :=
    match trie_get (N.encode n) (node_exits (D.tables p)) with
    | Some xs => xs
    | None => nil
    end.
  Definition universe p :=
    List.rev_append (PTrieCode.fold (fun acc _ x => x :: acc)
      (fold_left (fun s x => PTrieCode.set (X.encode x) x s)
      (flat_map (fun e => uses p e ++ defs p e) (C.edges p) ++
        flat_map (exits p) (C.nodes p)) PTrieCode.empty) nil) nil.
End VarsCode.

Module Vars (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (X : KEY) (D : VARS_DATA P X)
    <: VARS P N E C X.
  Include VarsCode P N E C X D.
  Include VARS_SPEC P N E C X.
  Lemma universe_spec : forall p x,
    In x (universe p) <->
      (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
      (exists n, In n (C.nodes p) /\ In x (exits p n)).
  Proof. Admitted. (* CONVERT: universe_spec: The reference FinSet.elements_spec was not found. *)
  Lemma universe_nodup : forall p, NoDup (universe p).
  Proof. Admitted. (* STUB *)
End Vars.

Module VarsT (P : TYPE) (N : KEY_T) (E : KEY_T)
    (C : CFG_T P N E) (X : KEY_T)
    (D : VARS_DATA_T P X) <: VARS_ALL P N E C X.
  Include Vars P N E C X D.
  TimeFun uses.
  TimeFun defs.
  TimeFun exits.
  TimeFun occurrences.
  TimeFun occurrence_width.
  TimeFun universe.

  Definition universe_work p :=
    (C.T_edges p + C.T_nodes p +
      fold_right N.add 0%N (map (fun e => T_uses p e + T_defs p e)%N (C.edges p)) +
      fold_right N.add 0%N (map (T_exits p) (C.nodes p)) +
      N.of_nat (length (C.edges p) + length (C.nodes p) + length (occurrences p) + 1) *
        N.of_nat (occurrence_width p + 1) +
      fold_right N.add 0%N (map X.T_encode (occurrences p)))%N.

  Definition c_vars : N := 1%N. (* STUB *)

  (** Universe preparation pays for each encoded occurrence lookup. *)
  Lemma T_universe_le : forall p,
    (T_universe p <= c_vars * universe_work p)%N.
  Proof. Admitted. (* STUB *)

  (** The universe bound includes every reader, encoding and occurrence width. *)
  Lemma universe_bigO : bigO (fun _ : P.t => True) universe_work T_universe.
  Proof. Admitted. (* STUB *)

  (** Flattening syntax preserves exactly the occurrence predicate. *)
  Lemma F1_occurrences : forall p x, In x (occurrences p) <-> occurs p x.
  Proof. Admitted. (* STUB *)

  (** Deduplicating occurrences gives the prepared variable universe. *)
  Lemma F2_universe : forall p x, In x (universe p) <-> In x (occurrences p).
  Proof. Admitted. (* STUB *)
  Definition seen p :=
    fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p) PTrieCode.empty.
  TimeFun seen.
  Definition k_seen : N := 1%N. (* STUB *)
  Definition k_collect : N := 1%N. (* STUB *)

  Lemma T_uses_le : forall p e,
    (T_uses p e <= c_vars * N.of_nat (E.bits e + length (uses p e) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_defs_le : forall p e,
    (T_defs p e <= c_vars * N.of_nat (E.bits e + length (defs p e) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_exits_le : forall p n,
    (T_exits p n <= c_vars * N.of_nat (N.bits n + length (exits p n) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma F3_seen : forall p,
    seen p = fold_left (fun s x => PTrieCode.set (X.encode x) x s) (occurrences p)
      PTrieCode.empty.
  Proof. Admitted. (* STUB *)

  Lemma F4_seen_nodes : forall p,
    PTrie.nodes (seen p) <= length (occurrences p) * occurrence_width p.
  Proof. Admitted. (* STUB *)

  Lemma T1_seen : forall p,
    (T_seen p <= k_seen * universe_work p)%N.
  Proof. Admitted. (* STUB *)

  Lemma T2_universe : forall p,
    (T_universe p <= k_collect * (T_seen p +
      N.of_nat (length (occurrences p) + 1) * N.of_nat (occurrence_width p + 1)))%N.
  Proof. Admitted. (* STUB *)
End VarsT.
