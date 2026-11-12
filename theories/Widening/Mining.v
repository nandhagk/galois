(** * Threshold mining code

    Mining traverses terms once to collect literals before expanding their neighbors.
    For example, the literal four contributes three, four and five to the threshold tree.
    Builds on: MiningSig and ThresholdsSig. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import KeySig.
From Galois.Domains Require Import LangSig ThresholdsSig.
From Galois.Widening Require Import MiningSig.

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
