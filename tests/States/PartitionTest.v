(** * Labelled partition clients

    These clients distinguish label routing, bottom parts and capped joins over integer states.
    For example, a stray skips a bottom part and widens the first live part.
    Builds on: Partition, Env, Interval and ZLang. *)

From Stdlib Require Import List ZArith Lia.
From Galois.Base Require Import Key Map.
From Galois.Domains Require Import LangSig ValueSig IntervalSig Interval ThresholdsSig Thresholds ZLang.
From Galois.States Require Import EnvSig Env Partition.
Import List.ListNotations.

Module Vars := TrieMap BoolKey.
Module Values := Interval ZLang Thresholds.
Module State := Env BoolKey Vars ZLang Values.
Module Cap.
  Definition k := 2%nat.
  Lemma k_pos : (0 < k)%nat.
  Proof.
    unfold k; lia.
  Qed.
End Cap.
Module Parts := Partition BoolKey NatKey ZLang Values State Cap.

Definition point (z : Z) : State.t :=
  Reached (Vars.set false (I (Fin z) (Fin z)) Vars.empty).

Definition observe (a : Parts.t) :=
  map (fun q => (fst q, State.eval (Leaf false) (snd q))) (proj1_sig a).

Definition two_live := Parts.fit [(Some 1%nat, point 0); (Some 2%nat, point 10)].
Definition bottom_then_live := Parts.fit [(Some 1%nat, State.bot); (Some 2%nat, point 0)].

(** Coverage does not depend on labels. *)
Example labels_do_not_restrict_coverage :
  Parts.leb (Parts.inject 1%nat (point 0)) (Parts.inject 2%nat (point 0)) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Joining equal labels keeps one part and joins its component states. *)
Example equal_labels_join_values :
  observe (Parts.join (Parts.inject 1%nat (point 0)) (Parts.inject 1%nat (point 5))) =
    [(Some 1%nat, I (Fin 0) (Fin 5))].
Proof.
  vm_compute; reflexivity.
Qed.

(** Overflow keeps the first label and collapses the remaining parts under no label. *)
Example overflow_preserves_prefix :
  observe (Parts.join two_live (Parts.inject 3%nat (point 20))) =
    [(Some 1%nat, I (Fin 0) (Fin 0)); (None, I (Fin 10) (Fin 20))].
Proof.
  vm_compute; reflexivity.
Qed.

(** A matching label routes the fresh state to its own receiver. *)
Example labelled_widening_updates_second_part :
  observe (Parts.widen TLeaf two_live (Parts.inject 2%nat (point 20))) =
    [(Some 1%nat, I (Fin 0) (Fin 0)); (Some 2%nat, I (Fin 10) PosInf)].
Proof.
  vm_compute; reflexivity.
Qed.

(** Stray routing skips parts below bottom. *)
Example stray_widening_skips_bottom :
  observe (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))) =
    [(Some 1%nat, IBot); (Some 2%nat, I (Fin 0) PosInf)].
Proof.
  vm_compute; reflexivity.
Qed.

(** A partition with only bottom parts starts from the candidate. *)
Example all_bottom_widening_keeps_candidate :
  observe (Parts.widen TLeaf (Parts.inject 1%nat State.bot) (Parts.inject 3%nat (point 5))) =
    [(Some 3%nat, I (Fin 5) (Fin 5))].
Proof.
  vm_compute; reflexivity.
Qed.

(** A strict routed update decreases the computed sum of live ranks. *)
Example routed_rank_decreases :
  Nat.ltb (Parts.wrank TLeaf
    (Parts.widen TLeaf bottom_then_live (Parts.inject 3%nat (point 5))))
    (Parts.wrank TLeaf bottom_then_live) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The concrete state instance supplies the universal widening coverage theorem. *)
Example widening_coverage_client : forall p a b, Parts.leb b (Parts.widen p a b) = true.
Proof.
  exact Parts.widen_ub_r.
Qed.
