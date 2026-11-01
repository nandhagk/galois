(** * Dense batch cost adequacy

    Counted slot reads preserve the results and charge each present index.
    For example, a missing slot adds no trie read.
    Builds on: CollectionsAuditHistorical. *)

From Stdlib Require Import List NArith.
From Galois.Collections Require Import CollectionsAuditState CollectionsAuditHistorical.
Import List.ListNotations.

(** * Checked observations and proofs *)

(** Counted batch reads preserve results and length and count present slots and their code bits. *)
Theorem slot_batch_cost : slot_batch_cost_statement.
Proof.
  intros V m slots; induction slots as [|slot rest IH]; [repeat split; reflexivity|].
  destruct slot as [i|].
  - cbn [read_slots_counted read_slots].
    destruct (read_slots_counted m rest) as [out work] eqn:Htail.
    cbn in IH.
    destruct IH as [Hout [Hlength [Hreads Hbits]]].
    cbn; rewrite Hlength, Hreads, Hbits, Hout; repeat split; reflexivity.
  - cbn [read_slots_counted read_slots].
    destruct (read_slots_counted m rest) as [out work] eqn:Htail.
    cbn in IH.
    destruct IH as [Hout [Hlength [Hreads Hbits]]].
    cbn; rewrite Hlength, Hreads, Hbits, Hout; repeat split; reflexivity.
Qed.
