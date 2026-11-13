(** * Threshold mining code

    Mining traverses terms once to collect literals before expanding their neighbors.
    For example, the literal four contributes three, four and five to the threshold tree.
    Builds on: MiningSig and ThresholdsSig. *)

From Stdlib Require Import List NArith ZArith Lia.
From Argent Require Import Time Tactics Std.
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

  Definition k_mining : N := (L.c_lang + 4)%N.

  (** Accumulator collection preserves the public literal order. *)
  Lemma F3_lits_acc : forall e acc, lits_acc e acc = lits e ++ acc.
  Proof.
    apply lits_acc_spec.
  Qed.

  (** Accumulator collection charges only the syntax nodes it visits. *)
  Lemma T1_lits_acc : forall e acc,
    (T_lits_acc e acc <= k_mining * N.of_nat (tsize e))%N.
  Proof.
    intros e acc. unfold k_mining. pose proof (lits_acc_time e acc). nia.
  Qed.

  Lemma F1_mine : forall es extra, mine es extra = T.make (expanded es extra).
  Proof. Admitted. (* STUB *)

  Lemma F2_expanded_length : forall es extra,
    length (expanded es extra) = 3 * length (seeds es extra).
  Proof. Admitted. (* STUB *)
End MiningT.

