(** * Prepared row-index examples

    These finite runs inspect successful and malformed rows and the actual fold trace.
    For example, two identical rows each emit a separate map update.
    Builds on: RulesAuditIndexCounts. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditIndex RulesAuditIndexCounts RulesAuditNestedProbe.
Import List.ListNotations.

(** * Successful and failed rows *)

Definition index_example_terms : list term := [TVar 0].

Definition index_example_rows : list tuple := [[1%positive]; []; [1%positive]].

Example index_example_row_outcomes :
  map (mat_index_success FinSet.empty index_example_terms) index_example_rows =
    [true; false; true].
Proof.
  reflexivity.
Qed.

Example index_example_row_calls :
  let events := snd (mat_build_index_full FinSet.empty index_example_terms index_example_rows) in
  (mat_block_count 5 events, mat_import_count 10 events, mat_import_count 11 events,
    mat_import_count 100 events) = (4, 2, 2, 4).
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_duplicate_rows :
  index_get (fst (mat_build_index_full FinSet.empty index_example_terms index_example_rows)) [] =
    [[1%positive]; [1%positive]].
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_empty_fold :
  snd (mat_build_index_full FinSet.empty index_example_terms []) = [MatBlock 5; MatBlock 0].
Proof.
  reflexivity.
Qed.

(** * Variable indexes and repeated bindings *)

Definition index_example_repeated_terms : list term := [TVar 0; TVar 0].

Definition index_example_repeated_rows : list tuple :=
  [[1%positive; 1%positive]; [1%positive; 2%positive];
   [2%positive; 2%positive]; [1%positive]].

Example index_example_variable_values :
  let index := fst (mat_build_variable_full FinSet.empty index_example_repeated_terms 0
    index_example_repeated_rows) in
  let values := variable_index_get index [] in
  (FinSet.mem positive_encoding 1%positive values, FinSet.mem positive_encoding 2%positive values,
    FinSet.mem positive_encoding 3%positive values) = (true, true, false).
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_repeated_binding :
  let '(result, events) := rules_bind_terms_counted index_example_repeated_terms
    [1%positive; 1%positive] Map.empty in
  (option_map (fun binding => Map.get nat_encoding 0 binding) result,
    length (filter (fun event => match event with
      | RprobeBindingSet _ _ _ _ _ _ _ => true
      | _ => false
      end) events),
    length (filter (fun event => match event with
      | RprobeEqual _ _ equal _ => equal
      | _ => false
      end) events)) = (Some (Some 1%positive), 1, 1).
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_repeated_mismatch :
  fst (rules_bind_terms_counted index_example_repeated_terms [1%positive; 2%positive] Map.empty) =
    None.
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_binding_call_operands :
  let events := snd (rules_bind_terms_counted index_example_repeated_terms
    [1%positive; 1%positive] Map.empty) in
  flat_map (fun event => match event with
    | RprobeBindingGet variable code _ raw _ _ => [(variable, code, raw)]
    | _ => []
    end) events = [(0, 1%positive, None); (0, 1%positive, Some 1%positive)].
Proof.
  vm_compute; reflexivity.
Qed.

Example index_example_binding_update_states :
  let events := snd (rules_bind_terms_counted index_example_repeated_terms
    [1%positive; 1%positive] Map.empty) in
  flat_map (fun event => match event with
    | RprobeBindingSet variable value _ before after _ _ =>
        [(variable, value, Map.get nat_encoding variable before,
          Map.get nat_encoding variable after)]
    | _ => []
    end) events = [(0, 1%positive, None, Some 1%positive)].
Proof.
  vm_compute; reflexivity.
Qed.
