(** * Threshold mining code

    Mining traverses terms once to collect literals before expanding their neighbors.
    For example, the literal four contributes three, four and five to the threshold tree.
    Builds on: MiningSig and ThresholdsSig. *)

From Stdlib Require Import List NArith ZArith.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ThresholdsSig.
From Galois.Widening Require Import MiningSig.

Module List.
  TimeFun Stdlib.Lists.List.flat_map.
End List.

Module MiningCode (X : KEY_OPS) (L : LANG_OPS) (T : THRESHOLDS_OPS)
    <: MINING_OPS X L T.
  Fixpoint lits_acc (e : term L.op X.t) (acc : list Z) : list Z :=
    match e with
    | Leaf _ => acc
    | Node o es =>
      let rest := fold_right (fun e acc => lits_acc e acc) acc es in
      match L.literal o with Some z => z :: rest | None => rest end
    end.

  Definition lits (e : term L.op X.t) : list Z := lits_acc e nil.

  Definition mine (es : list (term L.op X.t)) (extra : list Z) : ttree :=
    let seeds := fold_right (fun e acc => lits_acc e acc) extra es in
    T.make (flat_map (fun z => (z - 1)%Z :: z :: (z + 1)%Z :: nil) seeds).
End MiningCode.

Module Mining (X : KEY) (L : LANG) (T : THRESHOLDS) <: MINING X L T.
  Include MiningCode X L T.

  Lemma lits_leaf : forall x, lits (Leaf x) = nil.
  Proof. reflexivity. Qed.

  Lemma lits_node : forall o es, lits (Node o es) =
    (match L.literal o with Some z => z :: nil | None => nil end) ++ flat_map lits es.
  Proof. Admitted.

  Lemma mine_vals : forall es extra z, In z (T.vals (mine es extra)) <->
    exists q, In q (flat_map lits es ++ extra) /\
      (z = (q - 1)%Z \/ z = q \/ z = (q + 1)%Z).
  Proof. Admitted.

  Lemma mine_ordered : forall es extra, T.ordered (mine es extra).
  Proof. Admitted.
End Mining.

Module MiningT (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T)
    <: MINING_ALL X L T.
  Include Mining X L T.

  TimeFun lits_acc.
  TimeFun lits.
  TimeFun mine.

  Definition c_mining : N := 1%N. (* STUB *)

  Definition seeds es extra := flat_map lits es ++ extra.
  Definition expanded es extra := flat_map (fun z => ((z - 1)%Z :: z :: (z + 1)%Z :: nil))
    (seeds es extra).

  Lemma T_lits_le : forall e,
    (T_lits e <= c_mining * N.of_nat (tsize e))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_mine_le : forall es extra,
    (T_mine es extra <= c_mining *
      (N.of_nat ((fold_right Nat.add 0 (map tsize es) +
        fold_right Nat.add 0 (map (fun z => Z.size_nat z + 1) (seeds es extra)))%nat) +
      T.T_make (expanded es extra) + 1))%N.
  Proof. Admitted. (* STUB *)

  Definition k_mining : N := 1%N. (* STUB *)

  Lemma F3_lits_acc : forall e acc, lits_acc e acc = lits e ++ acc.
  Proof. Admitted. (* STUB *)

  Lemma T1_lits_acc : forall e acc,
    (T_lits_acc e acc <= k_mining * N.of_nat (tsize e))%N.
  Proof. Admitted. (* STUB *)

  Lemma F1_mine : forall es extra, mine es extra = T.make (expanded es extra).
  Proof. Admitted. (* STUB *)

  Lemma F2_expanded_length : forall es extra,
    length (expanded es extra) = 3 * length (seeds es extra).
  Proof. Admitted. (* STUB *)
End MiningT.

