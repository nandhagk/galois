(** * Interning bounds and dense code widths

    Bounds retain key-encoder charges and the allocation frontier's actual bit width.
    For example, a table with two keys assigns IDs whose widths are at most that of three.
    Builds on: BaseIntern and public BaseMap cost contracts. *)

From Stdlib Require Import List NArith PArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseIntern.
Import List.ListNotations.

Module InternCost.

(** The constant covers three map invocation ticks and the scalar ID encoding. *)
Definition intern_k : N := 4.

Local Lemma positive_code p : encode positive_encoding p = p.
Proof.
  apply of_pure_equation.
Qed.

Local Lemma positive_charge p : Cost.ticks (encode_c positive_encoding p) = 1%N.
Proof.
  apply of_pure_cost.
Qed.

Local Lemma size_nat_agrees p :
  Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof.
  induction p; cbn [Pos.size Pos.size_nat]; rewrite ?Pos2Nat.inj_succ, ?IHp; reflexivity.
Qed.

(** Positive-code width is monotone in the represented ID. *)
Theorem bits_monotone p q :
  (p <= q)%positive -> (N.pos (Pos.size p) <= N.pos (Pos.size q))%N.
Proof.
  intro Hle. change (Pos.size p <= Pos.size q)%positive.
  apply Pos2Nat.inj_le. rewrite !size_nat_agrees.
  apply Pos.lt_eq_cases in Hle. destruct Hle as [Hlt|Heq].
  - now apply Pos.size_nat_monotone.
  - subst q. lia.
Qed.

(** Forward lookup's numeric domain includes the actual encoding charge and queried width. *)
Theorem find_cost {K} (HC : Map.cost_laws) (E : encoding K) k (s : Intern.t K) :
  (Cost.ticks (Intern.find_c E k s) <=
    1 + Cost.ticks (encode_c E k) + key_bits E k)%N.
Proof.
  rewrite Intern.find_cost, Map.get_cost. reflexivity.
Qed.

(** Inverse lookup pays a scalar encoding and the allocated ID's width. *)
Theorem key_of_cost {K} (HC : Map.cost_laws) i (s : Intern.t K) :
  (Cost.ticks (Intern.key_of_c i s) <= 2 + N.pos (Pos.size i))%N.
Proof.
  rewrite Intern.key_of_cost, Map.get_cost, positive_charge, positive_code. reflexivity.
Qed.

(** Numeric interning counts two original-key encodings and one frontier-ID encoding. *)
Theorem intern_cost {K} (HC : Map.cost_laws) (E : encoding K) k (s : Intern.t K) :
  (Cost.ticks (Intern.intern_c E k s) <= intern_k +
    2 * (Cost.ticks (encode_c E k) + key_bits E k) +
    N.pos (Pos.size (Intern.next s)))%N.
Proof.
  pose proof (Intern.intern_cost E k s) as Hcost.
  rewrite Map.get_cost, !Map.set_cost, positive_charge, positive_code in Hcost.
  unfold intern_k, key_bits. lia.
Qed.

(** One interning call advances the frontier by at most one, even for raw tables. *)
Theorem next_growth {K} (E : encoding K) k (s : Intern.t K) :
  (Pos.to_nat (Intern.next (snd (Intern.intern E k s))) <=
    S (Pos.to_nat (Intern.next s)))%nat.
Proof.
  destruct (Intern.find E k s) as [i|] eqn:Hfind.
  - rewrite (Intern.intern_found E k i s Hfind). cbn [snd]. lia.
  - destruct (Intern.intern_new E k s Hfind) as [_ Hnext].
    rewrite Hnext, Pos2Nat.inj_succ. lia.
Qed.

(** A finite frontier and actual visited-key budgets bound list interning numerically. *)
Theorem intern_list_cost {K} (HC : Map.cost_laws) (E : encoding K) xs
    (s : Intern.t K) e b p :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N) ->
  (Pos.to_nat (Intern.next s) + length xs <= Pos.to_nat p)%nat ->
  (Cost.ticks (Intern.intern_list_c E xs s) <=
    N.of_nat (length xs) * (1 + intern_k + 2 * (e + b) + N.pos (Pos.size p)))%N.
Proof.
  revert s. induction xs as [|k rest IH]; intros s Hkeys Hfrontier.
  - rewrite Intern.intern_list_cost_equation. cbn [length]. lia.
  - destruct (Hkeys k (or_introl eq_refl)) as [He Hb].
    assert (Htail : forall a, In a rest ->
      (Cost.ticks (encode_c E a) <= e)%N /\ (key_bits E a <= b)%N).
    { intros a Ha. apply Hkeys. now right. }
    pose proof (next_growth E k s) as Hgrowth.
    assert (Hnext : (Pos.to_nat (Intern.next (snd (Intern.intern E k s))) +
      length rest <= Pos.to_nat p)%nat) by (cbn [length] in Hfrontier; lia).
    specialize (IH _ Htail Hnext).
    assert (Hid : (Intern.next s <= p)%positive).
    { apply Pos2Nat.inj_le. cbn [length] in Hfrontier. lia. }
    pose proof (bits_monotone _ _ Hid) as Hbits.
    pose proof (intern_cost HC E k s) as Hcost.
    rewrite Intern.intern_list_cost_equation. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Empty construction needs widths only for its input keys and at most length-plus-one IDs. *)
Theorem of_list_cost {K} (HC : Map.cost_laws) (E : encoding K) xs e b :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N) ->
  (Cost.ticks (Intern.of_list_c E xs) <=
    N.of_nat (length xs) *
      (1 + intern_k + 2 * (e + b) + N.pos (Pos.size (Pos.of_succ_nat (length xs)))))%N.
Proof.
  intro Hkeys. rewrite Intern.of_list_cost_equation.
  apply intern_list_cost; [exact HC|exact Hkeys|].
  rewrite SuccNat2Pos.id_succ.
  change (1 + length xs <= S (length xs))%nat. lia.
Qed.

(** Every allocated dense ID fits within the bits of the table size plus one. *)
Theorem dense_id_bits {K} (E : encoding K) (HE : encoding_laws E)
    k i (s : Intern.t K) :
  Intern.wf E s -> Intern.find E k s = Some i ->
  (key_bits positive_encoding i <=
    N.pos (Pos.size (Pos.of_succ_nat (Intern.size s))))%N.
Proof.
  intros Hwf Hfind.
  pose proof (proj2 (Intern.ids_dense E i s Hwf) (ex_intro _ k Hfind)) as Hbound.
  assert (Hnext : Intern.next s = Pos.of_succ_nat (Intern.size s)).
  { apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. now apply (Intern.next_size E HE). }
  unfold key_bits. rewrite positive_code. apply bits_monotone. rewrite <- Hnext. lia.
Qed.

End InternCost.
