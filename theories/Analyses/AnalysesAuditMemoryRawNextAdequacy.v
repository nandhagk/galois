(** * Raw memory successor adequacy

    Raw successors preserve missing operands, repeated edges and strict callback observations.
    For example, two equal incoming edges still cause two operand calls.
    Builds on: raw memory successors and indexed-walk adequacy. *)

From Stdlib Require Import List Lia.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryRawNext
  AnalysesAuditMemoryEffects AnalysesAuditMemoryDisjoint AnalysesAuditMemoryWalkIndexAdequacy.

(** * Raw successor observations *)

(** The counted successor mirror returns exactly the original raw successor list. *)
Theorem audit_memory_raw_next_erases : audit_memory_raw_next_erases_statement.
Proof.
  exact audit_walk_raw_next_erases.
Qed.

(** Every operand occurrence contributes one event, including missing and duplicate keys. *)
Theorem audit_memory_operands_count : audit_memory_operands_count_statement.
Proof.
  intros N E T CE SE IE OE BE operand node keys.
  induction keys as [|key rest IH]; cbn [audit_memory_operands]; [reflexivity|].
  destruct (operand node key) as [entry calls].
  destruct (@audit_memory_operands N E T CE SE IE OE BE operand node rest) as [tail events].
  cbn in IH |- *; lia.
Qed.

(** Branch overhead is bounded by the actual incoming occurrences and retained primitive work. *)
Theorem audit_raw_next_source_bound : audit_raw_next_source_bound_statement.
Proof.
  intros N E T CE SE IE OE BE edge_enc site_enc table incoming operand before q v
    edge_work site_work incoming_work operand_work before_work.
  unfold audit_raw_next_source_work.
  destruct v as [|node|edge index]; cbn [audit_memory_raw_next].
  - cbn; lia.
  - destruct (incoming node) as [edges incoming_events].
    pose proof (audit_memory_operands_count N E T CE SE IE OE BE operand node
      (None :: map Some edges)) as Hlength.
    destruct (@audit_memory_operands N E T CE SE IE OE BE operand node
      (None :: map Some edges)) as [versions events].
    cbn [snd] in Hlength |- *.
    rewrite length_app; cbn; cbn [length] in Hlength;
      rewrite List.length_map in Hlength; lia.
  - destruct (audit_memory_effect_get edge_enc table edge index) as [[effect|] calls].
    + destruct (before edge index) as [[previous|] before_events].
      * destruct (audit_memory_scopes_disjoint site_enc
          (effect_writes effect) q) as [disjoint disjoint_events].
        cbn; lia.
      * cbn; lia.
    + cbn; lia.
Qed.
