(** * Memo-table cost bounds

    Lookup and insertion budgets retain encoder and callback charges.
    For example, a repeated key pays no reference callback charge.
    Builds on: BaseMemo and the public BaseMap cost contracts. *)

From Stdlib Require Import List NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMemo.
Import List.ListNotations.

Module MemoCost.

(** A miss adds exactly one callback invocation and one insertion to lookup work. *)
Theorem get_or_cost {K V} (E : encoding K) (f_c : K -> Cost.t V) k (m : Memo.t K V) :
  (Cost.ticks (Memo.get_or_c E f_c k m) <=
    Cost.ticks (Map.get_c E k m) + 1 + Cost.ticks (f_c k) +
    Cost.ticks (Map.set_c E k (Cost.value (f_c k)) m))%N.
Proof.
  apply Memo.get_or_cost.
Qed.

(** A hit's cost is exactly its lookup cost, independently of the reference callback. *)
Theorem get_or_hit_cost {K V} (E : encoding K) (f_c : K -> Cost.t V)
    k v (m : Memo.t K V) :
  Map.get E k m = Some v ->
  Cost.ticks (Memo.get_or_c E f_c k m) = Cost.ticks (Map.get_c E k m).
Proof.
  intro Hhit. rewrite Memo.get_or_cost_equation, Hhit. lia.
Qed.

(** Numeric memo bounds include both encoder invocations on a miss. *)
Theorem get_or_numeric_cost {K V} (HC : Map.cost_laws) (E : encoding K)
    (f_c : K -> Cost.t V) k (m : Memo.t K V) :
  (Cost.ticks (Memo.get_or_c E f_c k m) <=
    3 + 2 * (Cost.ticks (encode_c E k) + key_bits E k) + Cost.ticks (f_c k))%N.
Proof.
  pose proof (get_or_cost E f_c k m) as Hcost.
  rewrite Map.get_cost, Map.set_cost in Hcost. unfold key_bits. lia.
Qed.

(** Primitive budgets on actual input keys bound memoized traversal for any initial cache. *)
Theorem map_memo_cost {K V} (E : encoding K) (f_c : K -> Cost.t V) xs m g s c :
  (forall k (q : Memo.t K V), In k xs -> (Cost.ticks (Map.get_c E k q) <= g)%N) ->
  (forall k q, In k xs ->
    (Cost.ticks (Map.set_c E k (Cost.value (f_c k)) q) <= s)%N) ->
  (forall k, In k xs -> (Cost.ticks (f_c k) <= c)%N) ->
  (Cost.ticks (Memo.map_memo_c E f_c xs m) <=
    N.of_nat (length xs) * (2 + g + s + c))%N.
Proof.
  revert m. induction xs as [|k rest IH]; intros m Hget Hset Hcallback.
  - rewrite Memo.map_memo_cost_equation. cbn [length]. lia.
  - assert (Htailget : forall a (q : Memo.t K V), In a rest ->
      (Cost.ticks (Map.get_c E a q) <= g)%N).
    { intros a q Ha. apply Hget. now right. }
    assert (Htailset : forall a q, In a rest ->
      (Cost.ticks (Map.set_c E a (Cost.value (f_c a)) q) <= s)%N).
    { intros a q Ha. apply Hset. now right. }
    assert (Htailcallback : forall a, In a rest -> (Cost.ticks (f_c a) <= c)%N).
    { intros a Ha. apply Hcallback. now right. }
    specialize (IH (snd (Memo.get_or E (fun a => Cost.value (f_c a)) k m))
      Htailget Htailset Htailcallback).
    pose proof (get_or_cost E f_c k m) as Hcost.
    specialize (Hget k m (or_introl eq_refl)).
    specialize (Hset k m (or_introl eq_refl)).
    specialize (Hcallback k (or_introl eq_refl)).
    rewrite Memo.map_memo_cost_equation. cbn [length]. rewrite Nat2N.inj_succ. nia.
Qed.

(** Finite visited-key bounds give a numeric linear traversal bound without global key budgets. *)
Theorem map_memo_numeric_cost {K V} (HC : Map.cost_laws) (E : encoding K)
    (f_c : K -> Cost.t V) xs m e b c :
  (forall k, In k xs ->
    (Cost.ticks (encode_c E k) <= e)%N /\ (key_bits E k <= b)%N /\
    (Cost.ticks (f_c k) <= c)%N) ->
  (Cost.ticks (Memo.map_memo_c E f_c xs m) <=
    N.of_nat (length xs) * (4 + 2 * (e + b) + c))%N.
Proof.
  intro Hkeys.
  eapply N.le_trans; [apply (map_memo_cost E f_c xs m (1 + e + b) (1 + e + b) c)|].
  - intros k q Hin. destruct (Hkeys k Hin) as [He [Hb Hc]].
    rewrite Map.get_cost. fold (key_bits E k). lia.
  - intros k q Hin. destruct (Hkeys k Hin) as [He [Hb Hc]].
    rewrite Map.set_cost. fold (key_bits E k). lia.
  - intros k Hin. exact (proj2 (proj2 (Hkeys k Hin))).
  - nia.
Qed.

End MemoCost.
