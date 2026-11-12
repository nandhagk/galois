(** * Variable presentations

    Edge and exit readers use first-order tables keyed by encoded identities.
    For example, an absent edge binding has no uses or definitions.
    Builds on: Program.VarsSig and Base.SetSig. *)

From Stdlib Require Import List.
From Galois.Base Require Import KeySig SetSig Trie.
From Galois.Program Require Import CfgSig VarsSig.

Record var_tables (X : Type) := VarTables {
  edge_uses : ptrie (list X);
  edge_defs : ptrie (list X);
  node_exits : ptrie (list X)
}.

Arguments VarTables {X}.
Arguments edge_uses {X}.
Arguments edge_defs {X}.
Arguments node_exits {X}.

Module Type VARS_DATA (P : TYPE) (X : KEY_OPS).
  Parameter tables : P.t -> var_tables X.t.
End VARS_DATA.

Module VarsCode (P : TYPE) (N : KEY_OPS) (E : KEY_OPS)
    (C : CFG_INDEXED_OPS P N E) (X : KEY_OPS) (D : VARS_DATA P X)
    (S : SET_OPS X) <: VARS_OPS P N E C X.
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
    S.elements (fold_left (fun s x => S.add x s)
      (flat_map (fun e => uses p e ++ defs p e) (C.edges p) ++
        flat_map (exits p) (C.nodes p)) S.empty).
End VarsCode.

Module Vars (P : TYPE) (N : KEY) (E : KEY)
    (C : CFG P N E) (X : KEY) (D : VARS_DATA P X) (S : SET X)
    <: VARS P N E C X.
  Include VarsCode P N E C X D S.
  Include VARS_SPEC P N E C X.
  Lemma universe_spec : forall p x,
    In x (universe p) <->
      (exists e, In e (C.edges p) /\ (In x (uses p e) \/ In x (defs p e))) \/
      (exists n, In n (C.nodes p) /\ In x (exits p n)).
  Proof. Admitted. (* CONVERT: universe_spec: The reference FinSet.elements_spec was not found. *)
  Lemma universe_nodup : forall p, NoDup (universe p).
  Proof. Admitted.
End Vars.
