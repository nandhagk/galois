(** * Pending-set coherence for changed-key worklists

    A pending set and its duplicate-free worklist describe the same scheduled keys.
    For example, popping a key removes its membership because it has no second worklist occurrence.
    Builds on: the public encoded equality and finite-set contracts. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
Import List.ListNotations.

Module TabQueue.

(** Coherence retains set well-formedness, list uniqueness and exact pending membership. *)
Definition coherent {K} (E : encoding K) (work : list K) (pending : FinSet.t K) :=
  FinSet.wf E pending /\ NoDup work /\
    forall k, FinSet.mem E k pending = true <-> In k work.

(** The empty worklist and empty pending set are coherent for every raw encoding. *)
Theorem empty_coherent {K} (E : encoding K) : coherent E [] FinSet.empty.
Proof.
  split; [apply FinSet.wf_empty|]; split; [constructor|].
  intro k; rewrite FinSet.mem_empty; split; intro H; inversion H.
Qed.

(** Inserting an absent key preserves exact queue membership and uniqueness. *)
Theorem insert_coherent {K} (E : encoding K) (HE : encoding_laws E) k work pending :
  coherent E work pending -> FinSet.mem E k pending = false ->
  coherent E (k :: work) (FinSet.add E k pending).
Proof.
  intros [Hwf [Hnodup Hmembers]] Habsent; split; [apply FinSet.wf_add; exact Hwf|].
  split.
  - constructor; [|exact Hnodup].
    intro Hin; apply Hmembers in Hin; rewrite Habsent in Hin; discriminate.
  - intro q; rewrite FinSet.mem_add by exact Hwf.
    rewrite orb_true_iff, (eqb_true_iff E HE), Hmembers.
    cbn [In]; intuition congruence.
Qed.

(** Popping the head preserves coherence because duplicate scheduling has been suppressed. *)
Theorem pop_coherent {K} (E : encoding K) (HE : encoding_laws E) k work pending :
  coherent E (k :: work) pending ->
  coherent E work (FinSet.remove E k pending).
Proof.
  intros [Hwf [Hnodup Hmembers]]; inversion Hnodup as [|key rest Hnot Htail]; subst key rest.
  split; [apply FinSet.wf_remove; exact Hwf|]; split; [exact Htail|].
  intro q; rewrite FinSet.mem_remove, andb_true_iff, negb_true_iff.
  rewrite (eqb_false_iff E HE), Hmembers.
  cbn [In]; intuition congruence.
Qed.

(** Existing membership is an actual worklist occurrence rather than a stale set bit. *)
Theorem queued_in_work {K} (E : encoding K) k work pending :
  coherent E work pending -> FinSet.mem E k pending = true -> In k work.
Proof.
  intros [Hwf [Hnodup Hmembers]] Hmem; apply Hmembers; exact Hmem.
Qed.

End TabQueue.
