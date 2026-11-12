(** * Threshold mining

    Mining collects literals and their neighbors for threshold widening.
    For example, a literal 4 contributes 3, 4 and 5.
    Builds on: LangSig and ThresholdsSig. *)

From Stdlib Require Import List ZArith.
From Argent Require Import Std.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ThresholdsSig.

Module Type MINING_OPS (X : KEY_OPS) (L : LANG_OPS) (T : THRESHOLDS_OPS).
  Parameter lits : term L.op X.t -> list Z.
  Parameter mine : list (term L.op X.t) -> list Z -> ttree.
End MINING_OPS.

Module Type MINING_LAWS (X : KEY) (L : LANG) (T : THRESHOLDS)
    (Import M : MINING_OPS X L T).
  (** A leaf contributes no literal. *)
  Parameter lits_leaf : forall x, lits (Leaf x) = nil.
  (** A node lists its own literal before its children's literals. *)
  Parameter lits_node : forall o es, lits (Node o es) =
    (match L.literal o with Some z => z :: nil | None => nil end) ++ flat_map lits es.
  (** Mining retains precisely the literals, extras and their neighbors. *)
  Parameter mine_vals : forall es extra z, In z (T.vals (mine es extra)) <->
    exists q, In q (flat_map lits es ++ extra) /\
      (z = (q - 1)%Z \/ z = q \/ z = (q + 1)%Z).
  (** Mined trees satisfy the threshold ordering invariant. *)
  Parameter mine_ordered : forall es extra, T.ordered (mine es extra).
End MINING_LAWS.

Module Type MINING (X : KEY) (L : LANG) (T : THRESHOLDS) :=
  MINING_OPS X L T <+ MINING_LAWS X L T.

Module Type MINING_TIME (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T)
    (Import M : MINING X L T).
  Parameter T_lits : term L.op X.t -> N.
  Parameter T_mine : list (term L.op X.t) -> list Z -> N.
  Parameter c_mining : N.
  Definition seeds es extra := flat_map lits es ++ extra.
  Definition expanded es extra := flat_map (fun z => ((z-1)%Z :: z :: (z+1)%Z :: nil))
    (seeds es extra).
  (** Literal collection charges one traversal of the term. *)
  Parameter T_lits_le : forall e, (T_lits e <= c_mining * N.of_nat ((tsize e)%nat))%N.
  (** Mining charges traversal, neighbor arithmetic and threshold construction. *)
  Parameter T_mine_le : forall es extra, (T_mine es extra <= c_mining *
    (N.of_nat ((fold_right Nat.add 0 (map tsize es) +
     fold_right Nat.add 0 (map (fun z => Z.size_nat z + 1) (seeds es extra)))%nat) +
     T.T_make (expanded es extra) + 1))%N.
End MINING_TIME.

Module Type MINING_T (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T) :=
  MINING X L T <+ MINING_TIME X L T.

Module Type MINING_PLAN (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T)
    (Import M : MINING_T X L T).
  Parameter lits_acc : term L.op X.t -> list Z -> list Z.
  Parameter T_lits_acc : term L.op X.t -> list Z -> N.
  Parameter k_mining : N.
  (** Accumulator collection agrees with the literal order. *)
  Parameter F3_lits_acc : forall e acc, lits_acc e acc = lits e ++ acc.
  (** Accumulator collection traverses each syntax node once. *)
  Parameter T1_lits_acc : forall e acc,
    (T_lits_acc e acc <= k_mining * N.of_nat (tsize e))%N.
  (** Mining constructs the expanded threshold set. *)
  Parameter F1_mine : forall es extra, mine es extra = T.make (expanded es extra).
  (** Expansion contributes three entries for each seed. *)
  Parameter F2_expanded_length : forall es extra,
    length (expanded es extra) = 3 * length (seeds es extra).
End MINING_PLAN.

Module Type MINING_ALL (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T) :=
  MINING_T X L T <+ MINING_PLAN X L T.
