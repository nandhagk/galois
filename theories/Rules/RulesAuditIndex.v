(** * Counted row and variable indexes

    The model retains tuple encoding, trie updates and the actual binding probe subruns.
    For example, a malformed row leaves the current index unchanged.
    Builds on: RulesAuditMaterializePrelude and RulesAuditNestedProbe. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsTable CollectionsAuditCost CollectionsAuditEncoding
  CollectionsAuditFinSet CollectionsAuditElements.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditNestedProbe
  RulesAuditMaterializePrelude.
Import List.ListNotations.

Definition mat_tuple_encoder (row : tuple) :=
  mat_lift 100 Pos.size_nat (audit_list_events_work audit_basic_encoding_work)
    (audit_list_encode audit_positive_encode row).

Definition mat_bound_term (bound : FinSet.t nat) (t : term) :=
  mat_mark 101 (match t with
    | TConst _ => mat_return true
    | TVar v => mat_lift 102 (fun _ => 1 + v + audit_trie_nodes bound)
        (audit_finset_source_work audit_nat_events_work) (audit_finset_mem audit_nat_encode v bound)
    end).

Fixpoint mat_tuple_key (bound : FinSet.t nat) (ts : list term) (row : tuple) :
    mat_run (option tuple) :=
  mat_mark 103 (match ts, row with
    | [], [] => mat_return (Some [])
    | t :: tail_terms, c :: tail_row =>
        tail <- mat_tuple_key bound tail_terms tail_row;;
        match tail with
        | None => mat_return None
        | Some key => kept <- mat_bound_term bound t;;
            mat_return (Some (if kept then c :: key else key))
        end
    | _, _ => mat_return None
    end).

Definition mat_index_add_full bound terms row before :=
  key <- mat_tuple_key bound terms row;;
  match key with
  | None => mat_return before
  | Some key =>
      raw <- mat_get_encoded mat_tuple_encoder key before;;
      let old := match raw with
      | Some rows => rows
      | None => []
      end in
      value <- mat_return (row :: old);;
      mat_set_encoded mat_tuple_encoder key value before
  end.

Definition mat_build_index_full bound terms rows :=
  mat_foldr (mat_index_add_full bound terms) rows Map.empty.

Definition mat_variable_add_full bound terms v row before :=
  key <- mat_tuple_key bound terms row;;
  match key with
  | None => mat_return before
  | Some key =>
      found <- mat_lift 104 (fun _ => 1 + length terms + mat_tuple_size row)
        rules_nested_probe_work (rules_bind_terms_counted terms row Map.empty);;
      match found with
      | None => mat_return before
      | Some binding =>
          value <- mat_lift 105 Pos.size_nat rules_nested_probe_work (rules_probe_value binding v);;
          raw <- mat_get_encoded mat_tuple_encoder key before;;
          let set := match raw with
          | Some s => s
          | None => FinSet.empty
          end in
          next <- mat_lift 106 (fun s => 1 + Pos.size_nat value + audit_trie_nodes s)
            (audit_finset_source_work audit_basic_encoding_work)
            (audit_finset_add audit_positive_encode value set);;
          mat_set_encoded mat_tuple_encoder key next before
      end
  end.

Definition mat_build_variable_full bound terms v rows :=
  mat_foldr (mat_variable_add_full bound terms v) rows Table.empty.

(** Each counted row and variable index erases to the corresponding source operation. *)
Definition mat_index_full_erases_statement : Prop :=
  (forall bound terms row before,
    fst (mat_index_add_full bound terms row before) = index_add bound terms row before) /\
  (forall bound terms rows,
    fst (mat_build_index_full bound terms rows) = build_index bound terms rows) /\
  (forall bound terms v row before,
    fst (mat_variable_add_full bound terms v row before) =
      variable_index_add bound terms v row before) /\
  (forall bound terms v rows,
    fst (mat_build_variable_full bound terms v rows) = build_variable_index bound terms v rows).

Definition mat_index_terms_input (terms : list term) : nat :=
  fold_right (fun t n => 1 + n + match t with
    | TVar v => v
    | TConst c => Pos.size_nat c
    end) 1 terms.

Definition mat_index_rows_input (rows : list tuple) : nat :=
  fold_right (fun row n => mat_tuple_size row + n) 1 rows.

Definition mat_index_input_budget {A} (bound : FinSet.t nat) terms rows (before : Trie.t A) :=
  (1000 * 1000) * Nat.pow
    (1 + audit_trie_nodes bound + mat_index_terms_input terms + mat_index_rows_input rows +
      audit_trie_nodes before) 6.

(** The row-index budget is derived from the input and current trie, not returned work. *)
Definition mat_index_full_input_bound_statement : Prop :=
  (forall bound terms row before,
    mat_work (snd (mat_index_add_full bound terms row before)) <=
      mat_index_input_budget bound terms [row] before) /\
  (forall bound terms rows,
    mat_work (snd (mat_build_index_full bound terms rows)) <=
      mat_index_input_budget bound terms rows (Map.empty : tuple_index)).

(** The variable-index budget additionally accounts for the queried variable. *)
Definition mat_variable_full_input_bound_statement : Prop :=
  (forall bound terms v row before,
    mat_work (snd (mat_variable_add_full bound terms v row before)) <=
      S v * mat_index_input_budget bound terms [row] before) /\
  (forall bound terms v rows,
    mat_work (snd (mat_build_variable_full bound terms v rows)) <=
      S v * mat_index_input_budget bound terms rows (Table.empty : variable_index)).

(** The combined claim retains both erasure and the separate phase bounds. *)
Definition mat_index_full_source_statement : Prop :=
  mat_index_full_erases_statement /\ mat_index_full_input_bound_statement /\
    mat_variable_full_input_bound_statement.
