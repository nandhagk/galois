(** * Concrete composite-key union-find adapters

    These instantiations connect the fixed pair and list encoders to the complete
    persistent union-find history and [of_unions] model. Child encoder traces are
    priced at their actual recursive call sites in each map access.
    For example, pair keys invoke both component encoders.
    Builds on: CollectionsAuditEncoding and CollectionsAuditUnionFind. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsUnionFind
  CollectionsAuditEncoding
  CollectionsAuditUnionFind.
Import List.ListNotations.

Definition audit_uf_pair_encode {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB)
    (key : A * B) := audit_pair_encode first second key.

Definition audit_uf_list_encode {A E}
    (element : A -> positive * list E) (key : list A) := audit_list_encode element key.

Definition audit_uf_pair_of_unions {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB)
    (inputs : list ((A * B) * (A * B))) :=
  audit_uf_of_unions (audit_uf_pair_encode first second) inputs.

Definition audit_uf_list_of_unions {A E}
    (element : A -> positive * list E) (inputs : list (list A * list A)) :=
  audit_uf_of_unions (audit_uf_list_encode element) inputs.

(** Discarding the uf pair of unions events recovers the corresponding original operation under
  its premises. *)
Definition audit_uf_pair_of_unions_erases_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
    (e1 : encoding A) (e2 : encoding B) inputs,
    (forall a, fst (first a) = encode e1 a) ->
    (forall b, fst (second b) = encode e2 b) ->
    fst (audit_uf_pair_of_unions first second inputs) =
      UnionFind.of_unions (pair_encoding e1 e2) inputs.

(** Discarding the uf list of unions events recovers the corresponding original operation under
  its premises. *)
Definition audit_uf_list_of_unions_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (e : encoding A) inputs,
    (forall a, fst (element a) = encode e a) ->
    fst (audit_uf_list_of_unions element inputs) =
      UnionFind.of_unions (list_encoding e) inputs.

Definition audit_uf_pair_encoder_work {A B EA EB}
    (first_work : list EA -> nat) (second_work : list EB -> nat)
    : list (audit_pair_event A B EA EB) -> nat :=
  audit_pair_events_work first_work second_work.

Definition audit_uf_list_encoder_work {A E} (element_work : list E -> nat)
    : list (audit_list_event A E) -> nat := audit_list_events_work element_work.

(** Pair-key union work is bounded by history frames and actual primitive work. *)
Definition audit_uf_pair_of_unions_source_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
    first_work second_work inputs,
    let enc_work := audit_uf_pair_encoder_work first_work second_work in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_pair_of_unions first second inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget (audit_uf_pair_encode first second) actions UnionFind.make +
      audit_uf_primitive_work enc_work events.

(** List-key union work is bounded by history frames and actual primitive work. *)
Definition audit_uf_list_of_unions_source_bound_statement : Prop :=
  forall A E (element : A -> positive * list E) element_work inputs,
    let enc_work := audit_uf_list_encoder_work element_work in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_list_of_unions element inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget (audit_uf_list_encode element) actions UnionFind.make +
      audit_uf_primitive_work enc_work events.
