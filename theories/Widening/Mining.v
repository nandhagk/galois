(** * Threshold mining code

    Mining traverses terms once to collect literals before expanding their neighbors.
    For example, the literal four contributes three, four and five to the threshold tree.

    Main results
    - [lits_complexity] Literal collection is linear in the term size.
    - [mine_complexity] Mining is linear in the terms and seeds plus the cost of building the
      thresholds.

    Builds on: MiningSig and ThresholdsSig. *)

From Stdlib Require Import List NArith ZArith Lia.
From Argent Require Import Time Tactics Std Complexity.
Import ComplexityNotations.
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

  (** Literal accumulation leaves an appended suffix untouched. *)
  Lemma lits_acc_app : forall e left right,
    lits_acc e (left ++ right) = lits_acc e left ++ right.
  Proof.
    intro e. induction e as [x|o es IH]; intros left right; [reflexivity|].
    assert (Hfold : forall left right,
      fold_right (fun e acc => lits_acc e acc) (left ++ right) es =
      fold_right (fun e acc => lits_acc e acc) left es ++ right).
    { clear left right. revert IH.
      induction es as [|e es IHes]; intros IH left right; [reflexivity|].
      inversion IH as [|e' IHe es' IHrest]; subst.
      cbn [fold_right]. rewrite (IHes IHrest left right), IHe. reflexivity. }
    cbn [lits_acc]. rewrite Hfold. destruct (L.literal o); reflexivity.
  Qed.

  (** An accumulator follows exactly the literals collected from the term. *)
  Lemma lits_acc_spec : forall e acc, lits_acc e acc = lits e ++ acc.
  Proof.
    intros e acc. unfold lits.
    change (lits_acc e (nil ++ acc) = lits_acc e nil ++ acc). apply lits_acc_app.
  Qed.

  (** Folding the accumulator preserves the ordered literals of all input terms. *)
  Lemma lits_fold_spec : forall es acc,
    fold_right (fun e acc => lits_acc e acc) acc es = flat_map lits es ++ acc.
  Proof.
    intro es. induction es as [|e es IH]; intro acc; cbn [fold_right flat_map];
      [reflexivity|].
    rewrite lits_acc_spec, IH, app_assoc. reflexivity.
  Qed.

  (** A variable leaf contributes no literal. *)
  Lemma lits_leaf : forall x, lits (Leaf x) = nil.
  Proof.
    reflexivity.
  Qed.

  (** A node places its own literal before the literals collected from its children. *)
  Lemma lits_node : forall o es, lits (Node o es) =
    (match L.literal o with Some z => z :: nil | None => nil end) ++ flat_map lits es.
  Proof.
    intros o es. unfold lits at 1. cbn [lits_acc].
    rewrite lits_fold_spec, app_nil_r. destruct (L.literal o); reflexivity.
  Qed.

  (** Mining retains precisely the literal seeds, the extra seeds, and their neighbors. *)
  Lemma mine_vals : forall es extra z, In z (T.vals (mine es extra)) <->
    exists q, In q (flat_map lits es ++ extra) /\
      (z = (q - 1)%Z \/ z = q \/ z = (q + 1)%Z).
  Proof.
    intros es extra z. unfold mine. rewrite T.make_vals, lits_fold_spec, in_flat_map.
    split; intros [q [Hq Hz]]; exists q; split; [exact Hq| |exact Hq|];
      cbn in *; intuition congruence.
  Qed.

  (** Threshold construction orders every mined collection. *)
  Lemma mine_ordered : forall es extra, T.ordered (mine es extra).
  Proof.
    intros es extra. unfold mine. apply T.make_ordered.
  Qed.
End Mining.

Module MiningT (X : KEY_T) (L : LANG_T) (T : THRESHOLDS_T)
    <: MINING_ALL X L T.
  Include Mining X L T.

  TimeFun lits_acc.
  TimeFun lits.
  TimeFun mine.

  (** Each syntax node also pays the two units charged by its parent's fold. *)
  Lemma lits_acc_time : forall e acc,
    (T_lits_acc e acc + 2 <= (L.c_lang + 4) * N.of_nat (tsize e))%N.
  Proof.
    intro e. induction e as [x|o es IH]; intro acc.
    - time_unfold T_lits_acc. cbn [tsize]. nia.
    - assert (Hfold : forall acc,
        (Std.List.T_fold_right
          (fun e acc => lits_acc e acc) (fun e acc => 1 + T_lits_acc e acc)%N acc es <=
         (L.c_lang + 4) * N.of_nat (fold_right Nat.add 0%nat (map tsize es)) + 1)%N).
      { clear acc. revert IH. induction es as [|e es IHes]; intros IH acc.
        - time_unfold Std.List.T_fold_right. cbn [map fold_right]. nia.
        - inversion IH as [|e' IHe es' IHrest]; subst.
          pose proof (IHes IHrest acc) as Hrest.
          pose proof (IHe (fold_right (fun e acc => lits_acc e acc) acc es)) as Hhead.
          time_unfold Std.List.T_fold_right. cbn [map fold_right].
          rewrite Nat2N.inj_add. nia. }
      time_unfold T_lits_acc.
      pose proof (Hfold acc) as Hchildren. pose proof (L.T_literal_le o) as Hliteral.
      cbn [tsize]. rewrite Nat2N.inj_succ. nia.
  Qed.

  (** Folding a term list charges the sum of its syntax sizes. *)
  Lemma lits_fold_time : forall es acc,
    (Std.List.T_fold_right
      (fun e acc => lits_acc e acc) (fun e acc => 1 + T_lits_acc e acc)%N acc es <=
     (L.c_lang + 4) * N.of_nat (fold_right Nat.add 0%nat (map tsize es)) + 1)%N.
  Proof.
    intro es. induction es as [|e es IH]; intro acc.
    - time_unfold Std.List.T_fold_right. cbn [map fold_right]. nia.
    - pose proof (IH acc) as Hrest.
      pose proof (lits_acc_time e
        (fold_right (fun e acc => lits_acc e acc) acc es)) as Hhead.
      time_unfold Std.List.T_fold_right. cbn [map fold_right].
      rewrite Nat2N.inj_add. nia.
  Qed.

  (** Expansion pays for two arithmetic operations and three output entries per seed. *)
  Lemma neighbors_time : forall zs,
    (List.T_flat_map (fun z => (z - 1)%Z :: z :: (z + 1)%Z :: nil)
      (fun z => 1 + (Std.Z.T_sub z 1 + Std.Z.T_add z 1))%N zs <=
     16 * N.of_nat
       (fold_right Nat.add 0%nat (map (fun z => (Z.size_nat z + 1)%nat) zs)) + 1)%N.
  Proof.
    intro zs. induction zs as [|z zs IH].
    - time_unfold List.T_flat_map. cbn [map fold_right]. nia.
    - time_unfold List.T_flat_map. cbn [map fold_right].
      pose proof (Std.Z.T_sub_le z 1) as Hsub.
      pose proof (Std.Z.T_add_le z 1) as Hadd.
      pose proof (Std.Datatypes.T_app_le ((z - 1)%Z :: z :: (z + 1)%Z :: nil)
        (flat_map (fun z => (z - 1)%Z :: z :: (z + 1)%Z :: nil) zs)) as Happ.
      cbn [length] in Happ.
      change (Std.Z.T_sub z 1 <= 3 * N.of_nat (Z.size_nat z + 1) + 3)%N in Hsub.
      change (Std.Z.T_add z 1 <= 3 * N.of_nat (Z.size_nat z + 1) + 1)%N in Hadd.
      rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** This coefficient covers syntax traversal and neighbor expansion together. *)
  Definition c_mining : N := (L.c_lang + 32)%N.

  Definition seeds es extra := flat_map lits es ++ extra.
  Definition expanded es extra := flat_map (fun z => ((z - 1)%Z :: z :: (z + 1)%Z :: nil))
    (seeds es extra).

  (** Literal collection pays for one traversal of the input syntax. *)
  Lemma T_lits_le : forall e,
    (T_lits e <= c_mining * N.of_nat (tsize e))%N.
  Proof.
    intro e. time_unfold T_lits. unfold c_mining.
    pose proof (lits_acc_time e nil). nia.
  Qed.

  (** Mining combines syntax traversal, seed arithmetic and threshold construction. *)
  Lemma T_mine_le : forall es extra,
    (T_mine es extra <= c_mining *
      (N.of_nat ((fold_right Nat.add 0%nat (map tsize es) +
        fold_right Nat.add 0 (map (fun z => Z.size_nat z + 1) (seeds es extra)))%nat) +
      T.T_make (expanded es extra) + 1))%N.
  Proof.
    intros es extra. time_unfold T_mine. rewrite lits_fold_spec.
    pose proof (lits_fold_time es extra) as Hterms.
    pose proof (neighbors_time (seeds es extra)) as Hneighbors.
    unfold c_mining, expanded, seeds in *. rewrite Nat2N.inj_add. nia.
  Qed.

  (** Literal collection is linear in the term size. *)
  Lemma lits_complexity :
    T_lits e ∈ 𝑂(N.of_nat (tsize e)) for e.
  Proof.
    eapply bigO_intro with (c := c_mining). intros e _.
    pose proof (T_lits_le e) as Hbound. nia.
  Qed.

  (** Mining is linear in the terms and seeds plus the cost of building the thresholds. *)
  Lemma mine_complexity :
    T_mine es extra ∈ 𝑂(N.of_nat (fold_right Nat.add 0%nat (map tsize es) +
        fold_right Nat.add 0%nat (map (fun z => (Z.size_nat z + 1)%nat) (seeds es extra)) +
        ((length (expanded es extra) * (Nat.log2 (length (expanded es extra)) + 1) + 1) *
          (T.zb (expanded es extra) + 1))))
    for (es, extra).
  Proof.
    eapply bigO_intro with (c := (c_mining * (T.c_thresholds + 1))%N).
    intros [es extra] _. cbn beta iota zeta.
    pose proof (T_mine_le es extra) as Hmine.
    pose proof (T.T_make_le (expanded es extra)) as Hmake.
    rewrite Nat2N.inj_add, Nat2N.inj_mul. nia.
  Qed.

  (** A syntax node pays for literal recognition and the surrounding fold. *)
  Definition k_mining : N := (L.c_lang + 4)%N.

  (** Accumulator collection preserves the public literal order. *)
  Lemma lits_acc_def : forall e acc, lits_acc e acc = lits e ++ acc.
  Proof.
    apply lits_acc_spec.
  Qed.

  (** Accumulator collection charges only the syntax nodes it visits. *)
  Lemma T_lits_acc_le : forall e acc,
    (T_lits_acc e acc <= k_mining * N.of_nat (tsize e))%N.
  Proof.
    intros e acc. unfold k_mining. pose proof (lits_acc_time e acc). nia.
  Qed.

  (** The accumulator implementation constructs exactly the specified expansion. *)
  Lemma mine_def : forall es extra, mine es extra = T.make (expanded es extra).
  Proof.
    intros es extra. unfold mine, expanded, seeds. rewrite lits_fold_spec. reflexivity.
  Qed.

  (** Expansion contributes three list entries even when seeds repeat. *)
  Lemma expanded_length : forall es extra,
    length (expanded es extra) = 3 * length (seeds es extra).
  Proof.
    intros es extra. unfold expanded. generalize (seeds es extra). intro zs.
    induction zs as [|z zs IH]; cbn [flat_map app length]; lia.
  Qed.
End MiningT.

