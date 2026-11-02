# Public names

Each entry identifies a public name; the heading gives its owning file and card. Earlier entries
also summarize kind and meaning. The linked API document owns the full signature and statement.
Internal representations are not public names.

## Collections

Contract: [Collections](collections.md).

### `CollectionsAuditCost.v` — AUD-COST-BASE

- `audit_event`, `AuditCase`, `AuditCall`, `AuditConstruct`, `AuditKeyBit`,
  `AuditArithmetic`, `audit_trace` — shared event and trace vocabulary.
- `audit_work`, `audit_calls`, `audit_key_bits`, `audit_case_count`,
  `audit_construct_count`, `audit_arithmetic_count` — deterministic trace folds.
- `audit_work_app`, `audit_calls_app`, `audit_key_bits_app`, `audit_case_count_app`,
  `audit_construct_count_app`, `audit_arithmetic_count_app` — append equations to prove.
- `audit_z_bits`, `audit_key_bits_weight`, `audit_get_weight`, `audit_set_weight`,
  `audit_remove_weight`, `audit_encoding_weight`, `audit_binary_weight`,
  `audit_multiply_weight`, `audit_divide_weight`, `audit_shift_weight`,
  `audit_unary_conversion_weight` — fixed abstract primitive charges.
- `count_zencode`, `count_zdecode`, `scalar_z` — signed operands in arithmetic event payloads.


Declaration kinds in `Galois.Collections.CollectionsAuditCost`:

- `AuditArithmetic` (Constructor).
- `AuditCall` (Constructor).
- `AuditCase` (Constructor).
- `AuditConstruct` (Constructor).
- `AuditKeyBit` (Constructor).
- `audit_arithmetic_count` (Fixpoint).
- `audit_binary_weight` (Definition).
- `audit_calls` (Fixpoint).
- `audit_case_count` (Fixpoint).
- `audit_construct_count` (Fixpoint).
- `audit_divide_weight` (Definition).
- `audit_encoding_weight` (Definition).
- `audit_event` (Inductive).
- `audit_get_weight` (Definition).
- `audit_key_bits` (Fixpoint).
- `audit_key_bits_weight` (Definition).
- `audit_multiply_weight` (Definition).
- `audit_remove_weight` (Definition).
- `audit_set_weight` (Definition).
- `audit_shift_weight` (Definition).
- `audit_trace` (Definition).
- `audit_unary_conversion_weight` (Definition).
- `audit_work` (Definition).
- `audit_z_bits` (Definition).
- `count_zdecode` (Definition).
- `count_zencode` (Definition).
- `scalar_z` (Definition).

### `CollectionsEncoding.v` — COL-1a

- `encoding` — Record; injective conversion from keys to positive codes.
- `Encoding` — constructor; builds an encoding from a code function and injectivity proof.
- `encode`, `encode_injective` — fields; select the key code and its injectivity proof.
- `positive_encoding`, `N_encoding`, `nat_encoding`, `Z_encoding` — Definitions; number encodings.
- `bool_encoding`, `unit_encoding` — Definitions; Boolean and unit encodings.
- `option_encoding`, `sum_encoding` — Definitions; encodings of options and sums.
- `pair_encoding`, `list_encoding` — Definitions; linear bit-list encodings of pairs and lists.

### `CollectionsTrie.v` — COL-1b

- `Trie.t` — Type; canonical binary trie, with its representation internal to the module.
- `Trie.empty`, `Trie.is_empty` — Definitions; empty trie and emptiness test.
- `Trie.get`, `Trie.set`, `Trie.remove` — Definitions; lookup, update and removal by code.
- `Trie.map`, `Trie.combine` — Definitions; map values and combine tries position-wise.
- `Trie.fold`, `Trie.elements`, `Trie.size` — Definitions; ordered fold, bindings and count.
- `Trie.beq` — Definition; compares trie values at each position.
- `Trie.forall2` — Definition; short-circuit relation test over the first trie's bindings.
- `Trie.union_opt`, `Trie.union_with` — Definitions; combine overlaps and share one-sided subtrees.
- `Trie.key_lt` — Fixpoint; trie traversal order on positive codes.
- `Trie.extensionality` — Theorem; equal lookups imply equal canonical tries.
- `Trie.get_empty`, `Trie.is_empty_spec` — Theorems; characterise the empty trie and test.
- `Trie.get_set_same`, `Trie.get_set_other` — Theorems; lookup after setting a code.
- `Trie.get_remove_same`, `Trie.get_remove_other` — Theorems; lookup after removing a code.
- `Trie.get_map`, `Trie.get_combine` — Theorems; mapping and combining act at each position.
- `Trie.elements_sound`, `Trie.elements_complete` — Theorems; bindings and lookups agree.
- `Trie.elements_nodup`, `Trie.elements_sorted` — Theorems; bindings have distinct sorted codes.
- `Trie.fold_elements`, `Trie.size_elements` — Theorems; fold and size agree with bindings.
- `Trie.beq_pointwise`, `Trie.beq_correct` — Theorems; comparison is pointwise and decides equality.
- `Trie.forall2_spec` — Theorem; relates the traversal test to every first-trie binding.
- `Trie.get_union_with`, `Trie.union_with_combine` — Theorems; union agrees with pointwise combine.

### `CollectionsMap.v` — COL-1c

- `Map.t` — Definition; trie storing keys and values at encoded positions.
- `Map.empty`, `Map.wf` — Definitions; empty map and key-position invariant.
- `Map.code_get`, `Map.get` — Definitions; read a position or an encoded key.
- `Map.set`, `Map.remove`, `Map.map` — Definitions; update, remove or transform values.
- `Map.combine`, `Map.union_with` — Definitions; combine maps and share one-sided unions.
- `Map.fold`, `Map.elements`, `Map.size` — Definitions; ordered fold, bindings and count.
- `Map.is_empty`, `Map.mem` — Definitions; test emptiness and key membership.
- `Map.of_list` — Definition; build a map, keeping the last binding of each key.
- `Map.beq`, `Map.forall2` — Definitions; compare values and test first-map bindings.
- `Map.get_code`, `Map.code_get_empty` — Theorems; encoded lookup and empty position lookup.
- `Map.code_get_combine`, `Map.code_get_union_with` — Theorems; position-wise combination laws.
- `Map.forall2_spec` — Theorem; the relation test covers every first-map position.
- `Map.wf_union_with`, `Map.wf_empty`, `Map.wf_set` — Theorems; these operations preserve `wf`.
- `Map.wf_remove`, `Map.wf_map`, `Map.wf_combine` — Theorems; these operations preserve `wf`.
- `Map.wf_of_list` — Theorem; a map built from a list is well formed.
- `Map.mem_spec`, `Map.is_empty_spec` — Theorems; membership and emptiness tests reflect lookups.
- `Map.get_empty`, `Map.get_set_same`, `Map.get_set_other` — Theorems; empty and updated lookups.
- `Map.get_remove_same`, `Map.get_remove_other` — Theorems; lookup after removal.
- `Map.get_map`, `Map.get_combine` — Theorems; lookup after mapping and combining.
- `Map.get_of_list` — Theorem; lookup finds the last binding of a key in the input list.
- `Map.extensionality` — Theorem; well-formed maps with equal lookups are equal.
- `Map.elements_sound`, `Map.elements_complete` — Theorems; well-formed bindings and lookups agree.
- `Map.elements_nodup` — Theorem; a well-formed map's binding keys are distinct.
- `Map.fold_elements`, `Map.size_elements` — Theorems; fold and size agree with bindings.
- `Map.beq_correct` — Theorem; value comparison reflects lookup equality for well-formed maps.

### `CollectionsFinSet.v` — COL-1c

- `FinSet.t`, `FinSet.wf`, `FinSet.empty` — Definitions; finite sets, well-formedness and empty set.
- `FinSet.mem`, `FinSet.add`, `FinSet.remove` — Definitions; membership and single-key updates.
- `FinSet.union`, `FinSet.inter`, `FinSet.diff` — Definitions; union, intersection and difference.
- `FinSet.subset` — Definition; inclusion test using a short-circuit traversal.
- `FinSet.elements`, `FinSet.size`, `FinSet.is_empty` — Definitions; members, count and emptiness.
- `FinSet.of_list` — Definition; set of the keys in a list.
- `FinSet.mem_empty`, `FinSet.mem_add`, `FinSet.mem_remove` — Theorems; membership after updates.
- `FinSet.mem_union`, `FinSet.mem_inter`, `FinSet.mem_diff` — Theorems; membership in set algebra.
- `FinSet.of_list_spec` — Theorem; membership in a set built from a list is list membership.
- `FinSet.wf_ops` — Theorem; finite-set operations preserve well-formedness.
- `FinSet.extensionality`, `FinSet.subset_spec` — Theorems; extensionality and inclusion by members.
- `FinSet.elements_spec`, `FinSet.elements_nodup` — Theorems; members are listed exactly once.
- `FinSet.size_elements` — Theorem; size is the length of the elements list.
- `FinSet.mem_code`, `FinSet.union_code`, `FinSet.inter_code` — Theorems; position-level laws.
- `FinSet.diff_code`, `FinSet.subset_code` — Theorems; difference and inclusion at positions.
- `FinSet.is_empty_spec` — Theorem; emptiness is absence of members for a well-formed set.
- `FinSet.size_subset`, `FinSet.size_lt` — Theorems; inclusion bounds size, strictly if proper.
- `FinSet.size_le_length` — Theorem; a set inside a finite list is no larger than that list.
- `FinSet.union_comm`, `FinSet.union_assoc`, `FinSet.union_idem` — Theorems; union algebra.
- `FinSet.union_empty_r` — Theorem; empty set is a right identity for union.
- `FinSet.inter_comm`, `FinSet.inter_assoc`, `FinSet.inter_idem` — Theorems; intersection algebra.
- `FinSet.inter_empty_r` — Theorem; intersection with empty is empty.
- `FinSet.inter_union_distr` — Theorem; intersection distributes over union.
- `FinSet.union_inter_absorb` — Theorem; union absorbs intersection with itself.
- `FinSet.diff_self` — Theorem; a well-formed set minus itself is empty.

### `CollectionsHeap.v` — COL-2

- `PQueue.t`, `PQueue.wf`, `PQueue.empty` — Definitions; queue, invariant and empty queue.
- `PQueue.is_empty`, `PQueue.size` — Definitions; queue emptiness and live-key count.
- `PQueue.push`, `PQueue.pop` — Definitions; insert or lower a priority and remove a minimum.
- `PQueue.priority`, `PQueue.members` — Definitions; read live priorities and list held pairs.
- `PQueue.before` — Definition; lexicographic order on priority and key code.
- `PQueue.wf_empty`, `PQueue.priority_empty` — Theorems; empty queue is valid and has no priority.
- `PQueue.priority_push_same`, `PQueue.priority_push_other` — Theorems; priorities after push.
- `PQueue.size_push_new`, `PQueue.size_push_old` — Theorems; size after inserting or lowering.
- `PQueue.wf_push` — Theorem; push preserves queue well-formedness.
- `PQueue.pop_none`, `PQueue.pop_min` — Theorems; pop detects emptiness and returns a minimum.
- `PQueue.pop_rest`, `PQueue.wf_pop` — Theorems; pop removes exactly its key and preserves `wf`.
- `PQueue.members_spec`, `PQueue.members_nodup` — Theorems; members list live priorities once.
- `PQueue.size_members`, `PQueue.is_empty_spec` — Theorems; size and emptiness reflect live keys.

### `CollectionsUnionFind.v` — COL-2

- `UnionFind.t` — Record; parent and rank maps with an upper rank bound.
- `UnionFind.Forest` — constructor; builds a persistent union-find forest.
- `UnionFind.parents`, `UnionFind.ranks`, `UnionFind.max_rank` — fields; maps and rank bound.
- `UnionFind.make` — Definition; forest where every key is alone.
- `UnionFind.find` — Definition; representative and forest with compressed path.
- `UnionFind.union` — Definition; merge classes by rank.
- `UnionFind.equiv`, `UnionFind.equivb` — Definitions; class equivalence and threaded Boolean test.
- `UnionFind.keys` — Definition; distinct keys in parent or rank support.
- `UnionFind.wf` — Definition; map well-formedness and strictly increasing bounded parent ranks.
- `UnionFind.of_unions` — Definition; apply a list of unions to a fresh forest.
- `UnionFind.equiv_equivalence` — Theorem; class equivalence is an equivalence relation.
- `UnionFind.wf_make`, `UnionFind.wf_find`, `UnionFind.wf_union` — Theorems; forest invariants.
- `UnionFind.find_rep_stable` — Theorem; compression preserves representatives.
- `UnionFind.find_rep_canonical` — Theorem; a representative represents itself.
- `UnionFind.make_equiv`, `UnionFind.union_equiv` — Theorems; fresh classes and union semantics.
- `UnionFind.of_unions_equiv` — Theorem; classes are the equivalence closure of listed unions.
- `UnionFind.equivb_correct` — Theorem; the Boolean test and returned forest preserve equivalence.
- `UnionFind.keys_support` — Theorem; a key outside support has no distinct equivalent key.
- `UnionFind.keys_make`, `UnionFind.keys_union` — Theorems; support of fresh and merged forests.
- `UnionFind.keys_nodup` — Theorem; a well-formed forest's support has no duplicate keys.

### `CollectionsTable.v` — COL-2

- `Table.key`, `Table.t`, `Table.wf` — Definitions; list-key encoding, flat map and invariant.
- `Table.empty`, `Table.is_empty` — Definitions; empty table and emptiness test.
- `Table.get`, `Table.set`, `Table.remove` — Definitions; lookup, update and removal by list key.
- `Table.fold`, `Table.elements`, `Table.size` — Definitions; ordered fold, bindings and count.
- `Table.get_empty`, `Table.get_set_same`, `Table.get_set_other` — Theorems; empty and set lookups.
- `Table.get_remove_same`, `Table.get_remove_other` — Theorems; lookup after removal.
- `Table.wf_empty`, `Table.wf_set`, `Table.wf_remove` — Theorems; table invariants.
- `Table.extensionality` — Theorem; well-formed tables with equal lookups are equal.
- `Table.elements_sound`, `Table.elements_complete` — Theorems; table bindings and lookups agree.
- `Table.elements_nodup` — Theorem; well-formed table binding keys are distinct.
- `Table.fold_elements`, `Table.size_elements` — Theorems; fold and size agree with bindings.
- `Table.is_empty_spec` — Theorem; well-formed table emptiness is absence of lookups.

## Order

Contract: [Order](order.md).

### `OrderLattice.v` — ORD-1

- `lattice` — Record; comparison, bottom, join, widening and narrowing operations.
- `Lattice` — constructor; builds the operations of a lattice.
- `leb`, `bot`, `join`, `widen`, `narrow` — fields; select lattice operations.
- `lattice_laws` — Record; preorder, bottom, upper-bound and narrowing laws.
- `leb_refl`, `leb_trans`, `bot_least` — fields; preorder and least-bottom laws.
- `join_upper_l`, `join_upper_r`, `widen_upper_l`, `widen_upper_r` — fields; upper-bound laws.
- `narrow_lower`, `narrow_upper` — fields; narrowing bounds.
- `lub_laws`, `join_least` — Record and field; join is the least upper bound.
- `top`, `Top` — Record and constructor; greatest lattice element with proof.
- `top_value`, `top_greatest` — fields; select the top element and its greatest-element proof.
- `height`, `Height` — Record and constructor; bounded rank growing on strict joins.
- `rank`, `bound`, `rank_bounded`, `join_rank_grows` — fields; height rank and growth laws.
- `widening_rank`, `WideningRank` — Record and constructor; rank controlling widening steps.
- `wrank`, `widen_rank_stable`, `widen_rank_progress` — fields; rank and widening laws.
- `eqb_spec` — Definition; Boolean equality reflects equality.
- `equivalent` — Definition; two elements are below each other.
- `meet_laws` — Record; meet is a greatest lower bound.
- `meet_lower_l`, `meet_lower_r`, `meet_greatest` — fields; meet bounds and greatestness.
- `monotone_height`, `MonotoneHeight` — Record and constructor; height monotone in the order.
- `base_height`, `rank_monotone` — fields; height and its rank monotonicity proof.
- `bounded_widening_rank`, `BoundedWideningRank` — Record and constructor; bounded widening rank.
- `base_wrank`, `wbound`, `wrank_bounded` — fields; widening rank and its uniform bound.
- `height_wrank` — Definition; derives a bounded widening rank when widening is join.
- `join_monotone` — Theorem; least-upper-bound joins are monotone in both arguments.
- `join_bot_equivalent` — Theorem; joining bottom leaves an equivalent element.

### `OrderConcrete.v` — ORD-1

- `concretisation`, `Concretisation`, `gamma` — Record, constructor and field; forward meaning.
- `concretisation_laws`, `gamma_monotone` — Record and field; forward meaning is monotone.
- `agreement`, `Agreement`, `agree` — Record, constructor and field; backward agreement relation.
- `agreement_laws`, `agree_refl`, `agree_antitone` — Record and fields; agreement laws.
- `bottom_empty`, `gamma_bot_empty` — Record and field; bottom denotes no concrete value.
- `top_full`, `gamma_top_full` — Record and field; top denotes every concrete value.
- `agreement_equivalence`, `agree_sym`, `agree_trans` — Record and fields; agreement equivalence.
- `agreement_bot`, `agree_bot` — Record and field; bottom agrees on all pairs.
- `agreement_join_law`, `agree_join` — Record and field; agreement at both operands holds at join.
- `order_embedding` — Definition; a function preserves and reflects the Boolean order.
- `comap_gamma`, `comap_agree` — Definitions; pull meanings back along a carrier function.
- `gamma_join_l`, `gamma_join_r` — Theorems; each operand's meaning is contained in the join.
- `gamma_widen_l`, `gamma_widen_r` — Theorems; widening contains each operand's meaning.
- `gamma_narrow` — Theorem; narrowing contains the lower operand's meaning under its premise.
- `agree_join_l`, `agree_join_r` — Theorems; join agreement implies each operand's agreement.
- `agree_widen_l`, `agree_widen_r` — Theorems; widening agreement implies operand agreement.
- `comap_gamma_laws`, `comap_gamma_bot_empty` — Theorems; pulled-back concretisation laws.
- `comap_gamma_top_full` — Theorem; the pullback preserves full top under its premises.
- `comap_agree_laws`, `comap_agree_bot`, `comap_agree_join` — Theorems; pulled-back agreement laws.

### `OrderMonotone.v` — ORD-1

- `fun_leb` — Definition; pointwise order on assignments.
- `monotone_fun`, `monotone_fun2` — Definitions; monotonicity in one or two inputs.
- `monotone_on_assignments` — Definition; monotonicity from pointwise-ordered assignments.
- `monotone_id`, `monotone_const`, `monotone_compose` — Theorems; monotonicity closure rules.
- `monotone_join` — Theorem; join is monotone in both inputs with least-upper-bound laws.
- `monotone_on_const`, `monotone_on_lookup` — Theorems; constant and assignment lookup monotonicity.
- `monotone_on_join`, `monotone_on_compose` — Theorems; assignment monotonicity closure rules.
- `fun_leb_preorder` — Theorem; pointwise assignment order is reflexive and transitive.

### `OrderFlat.v` — ORD-1

- `flat` — Inductive; bottom, a value or top.
- `FBot`, `FVal`, `FTop` — constructors; form the three flat-domain cases.
- `flat_lattice`, `flat_top`, `flat_height` — Definitions; flat lattice, top and height.
- `flat_gamma`, `flat_agree` — Definitions; forward and backward meanings of flat values.
- `flat_laws`, `flat_lub` — Theorems; flat lattice satisfies lattice and least-upper-bound laws.
- `flat_gamma_laws`, `flat_gamma_bot_empty` — Theorems; flat concretisation laws and empty bottom.
- `flat_gamma_top_full` — Theorem; flat top denotes every concrete value.
- `flat_agree_laws`, `flat_agree_bot` — Theorems; flat agreement laws and bottom agreement.

### `OrderLift.v` — ORD-1

- `option_lattice`, `lift_bot` — Definitions; lattice and carrier with an added bottom.
- `Unreached`, `Reached`, `lift_bot_lattice` — notations; option constructors and lattice alias.
- `option_top`, `option_height`, `option_wrank` — Definitions; lifted top and termination evidence.
- `option_gamma`, `option_agree` — Definitions; meanings for the added-bottom carrier.
- `lift_bot_gamma`, `lift_bot_agree` — notations; aliases for option meanings.
- `lift_top` — Inductive; carrier with an added top.
- `Elem`, `Unknown` — constructors; original value and added top.
- `lift_top_lattice`, `lift_top_top`, `lift_top_height` — Definitions; lifted lattice and evidence.
- `lift_top_gamma`, `lift_top_agree` — Definitions; meanings for the added-top carrier.
- `option_laws`, `option_lub` — Theorems; added-bottom lattice and least-upper-bound laws.
- `option_gamma_laws`, `option_gamma_bot_empty` — Theorems; lifted concretisation and empty bottom.
- `option_agree_laws`, `option_agree_bot`, `option_agree_join` — Theorems; lifted agreement laws.
- `lift_top_laws`, `lift_top_lub` — Theorems; added-top lattice and least-upper-bound laws.
- `lift_top_gamma_laws`, `lift_top_gamma_top_full` — Theorems; added-top concretisation laws.
- `lift_top_agree_laws`, `lift_top_agree_bot`, `lift_top_agree_join` — Theorems; agreement laws.

### `OrderProduct.v` — ORD-1

- `product_lattice` — Definition; componentwise product lattice.
- `product_top`, `product_height`, `product_wrank` — Definitions; product top and termination.
- `product_gamma`, `product_agree` — Definitions; meanings requiring both components.
- `product_laws`, `product_lub` — Theorems; product lattice and least-upper-bound laws.
- `product_gamma_laws`, `product_gamma_bot_empty` — Theorems; product concretisation laws.
- `product_agree_laws`, `product_agree_join` — Theorems; product agreement laws.
- `monotone_fst`, `monotone_snd`, `monotone_pair` — Theorems; product monotonicity closure.

### `OrderReduced.v` — ORD-1

- `reduction_laws` — Record; reduction is decreasing, monotone and idempotent up to order.
- `reduce_lower`, `reduce_monotone`, `reduce_idempotent` — fields; the reduction laws.
- `reduction_sound`, `reduce_gamma` — Record and field; reduction preserves concrete meanings.
- `reduced_lattice` — Definition; product lattice with reduction in comparison, join and narrowing.
- `reduced_top`, `reduced_wrank` — Definitions; reduced-product top and widening-rank evidence.
- `reduced_laws`, `reduced_gamma_laws` — Theorems; reduced lattice and concretisation laws.
- `reduce_gamma_exact` — Theorem; sound reduction preserves the product meaning exactly.
- `reduced_top_full` — Theorem; reduced-product top denotes all values under its premises.

### `OrderDual.v` — ORD-1

- `dual_lattice` — Definition; reverses order and uses meet as join.
- `dual_top`, `dual_height` — Definitions; top and height evidence for the dual lattice.
- `dual_laws`, `dual_lub` — Theorems; dual lattice and least-upper-bound laws.

### `OrderBasic.v` — ORD-1

- `bool_lattice`, `bool_top`, `bool_height` — Definitions; Boolean lattice and its evidence.
- `bool_agree` — Definition; Boolean demand requires equality when true.
- `unit_lattice`, `unit_top`, `unit_height` — Definitions; one-element lattice and its evidence.
- `bool_laws`, `bool_lub` — Theorems; Boolean lattice and least-upper-bound laws.
- `bool_agree_laws`, `bool_agree_bot`, `bool_agree_join` — Theorems; Boolean agreement laws.
- `bool_agree_equivalence` — Theorem; Boolean agreement is an equivalence.
- `unit_laws`, `unit_lub` — Theorems; unit lattice and least-upper-bound laws.

### `OrderPowerset.v` — ORD-2

- `powerset_lattice` — Definition; finite sets ordered by inclusion.
- `powerset_gamma`, `powerset_agree` — Definitions; membership meaning and agreement on members.
- `must` — Inductive; all facts or a finite set of facts.
- `All`, `Only` — constructors; unrestricted and finite must-fact cases.
- `must_lattice`, `must_top`, `must_gamma` — Definitions; reverse-inclusion lattice and meaning.
- `within_set`, `finite_set` — Definitions; well-formed sets restricted to a finite universe.
- `finite_powerset_lattice`, `finite_powerset_top` — Definitions; finite powerset lattice and top.
- `finite_powerset_height` — Definition; size-based height for a duplicate-free universe.
- `finite_set_inter` — Definition; intersection of finite-universe sets.
- `finite_must_lattice`, `finite_must_top`, `finite_must_height` — Definitions; finite must lattice.
- `finite_clamp` — Definition; restricts a set to members of the universe.
- `finite_powerset_gamma`, `finite_powerset_agree` — Definitions; finite powerset meanings.
- `finite_must_embed`, `finite_must_gamma` — Definitions; finite must embedding and concretisation.
- `powerset_laws`, `powerset_lub` — Theorems; powerset lattice and least-upper-bound laws.
- `powerset_gamma_laws`, `powerset_gamma_bot_empty` — Theorems; powerset concretisation laws.
- `powerset_agree_laws`, `powerset_agree_bot` — Theorems; powerset agreement laws and bottom.
- `powerset_agree_join`, `powerset_agree_equivalence` — Theorems; agreement join and equivalence.
- `must_laws`, `must_lub` — Theorems; must lattice and least-upper-bound laws.
- `must_gamma_laws`, `must_gamma_bot_empty`, `must_gamma_top_full` — Theorems; must meanings.
- `finite_powerset_laws`, `finite_powerset_lub` — Theorems; finite powerset lattice laws.
- `finite_set_inter_meet` — Theorem; finite set intersection is a greatest lower bound.
- `finite_must_laws`, `finite_must_lub` — Theorems; finite must lattice laws.
- `finite_powerset_embedding`, `finite_must_embedding` — Theorems; finite-to-raw order embeddings.
- `finite_powerset_gamma_laws`, `finite_powerset_gamma_bot_empty` — Theorems; finite meanings.
- `finite_powerset_agree_laws` — Theorem; finite powerset agreement satisfies its laws.
- `finite_must_gamma_laws`, `finite_must_gamma_top_full` — Theorems; finite must meaning laws.
- `finite_clamp_mem`, `finite_clamp_in` — Theorems; clamp keeps exactly members in the universe.

### `OrderPointwise.v` — ORD-2

- `pointwise_lookup` — Definition; map lookup with a default for absent keys.
- `pointwise_lattice` — Definition; pointwise map lattice with bottom default.
- `pointwise_gamma`, `pointwise_agree` — Definitions; meanings for bottom-default maps.
- `pointwise_top_lattice`, `pointwise_top_gamma` — Definitions; maps with top default and meaning.
- `within_map`, `finite_map` — Definitions; well-formed maps restricted to a finite universe.
- `finite_pointwise_lattice`, `finite_pointwise_top` — Definitions; finite map lattice and top.
- `finite_pointwise_height`, `finite_pointwise_wrank` — Definitions; finite map termination proofs.
- `finite_pointwise_gamma`, `finite_pointwise_agree` — Definitions; finite map meanings.
- `finite_pointwise_top_lattice` — Definition; finite maps with top default and added bottom.
- `finite_pointwise_top_top`, `finite_pointwise_top_height` — Definitions; top and height evidence.
- `finite_map_clamp` — Definition; restricts a map to keys in the finite universe.
- `pointwise_laws`, `pointwise_lub` — Theorems; bottom-default pointwise lattice laws.
- `pointwise_gamma_laws`, `pointwise_agree_laws` — Theorems; pointwise meaning laws.
- `pointwise_agree_bot`, `pointwise_agree_join` — Theorems; pointwise agreement bottom and join.
- `pointwise_top_laws`, `pointwise_top_lub` — Theorems; top-default pointwise lattice laws.
- `pointwise_top_gamma_laws`, `pointwise_top_gamma_bot_empty` — Theorems; top-default meanings.
- `finite_pointwise_laws`, `finite_pointwise_lub` — Theorems; finite pointwise lattice laws.
- `monotone_pointwise_lookup`, `monotone_finite_pointwise_lookup` — Theorems; lookup monotonicity.
- `finite_pointwise_top_laws`, `finite_pointwise_top_lub` — Theorems; finite top-default laws.
- `finite_pointwise_top_embedding`, `finite_pointwise_embedding` — Theorems; finite map embeddings.
- `finite_pointwise_gamma_laws`, `finite_pointwise_agree_laws` — Theorems; finite map meaning laws.
- `finite_map_clamp_get` — Theorem; clamp keeps each lookup at a universe key.

### `OrderDisjunction.v` — ORD-2

- `join_all` — Definition; joins a list of lattice elements.
- `disjunction_leb` — Definition; tests whether each disjunct lies below an opposing disjunct.
- `compact` — Definition; collapses excess disjuncts by joining them.
- `disjunction_lattice`, `disjunction_wrank` — Definitions; capped disjunction lattice and rank.
- `disjunction_gamma` — Definition; union of the meanings of disjuncts.
- `disjunction_laws`, `disjunction_join_size` — Theorems; disjunction laws and join size bound.
- `disjunction_gamma_laws`, `disjunction_gamma_bot_empty` — Theorems; disjunction meaning laws.
- `monotone_join_all` — Theorem; elementwise ordered lists have ordered joins.

## Rules

Contract: [Rules](rules.md).

### `RulesSyntax.v` — RUL-1a

- `tuple` — Definition; a list of encoded constants.
- `term` — Inductive; a variable or an encoded constant.
- `TVar`, `TConst` — constructors; form variable and constant terms.
- `atom` — Record; a predicate and its argument terms.
- `Atom` — constructor; forms an atom from a predicate and argument terms.
- `pred`, `args` — fields; select an atom's predicate and arguments.
- `literal` — Inductive; a positive or negative atom.
- `LPos`, `LNeg` — constructors; form positive and negative literals.
- `rule` — Record; a head atom and body literals.
- `Rule` — constructor; forms a rule from its head and body.
- `head`, `body` — fields; select the head and body of a rule.
- `program` — Record; predicate encoding, arities and rules.
- `Program` — constructor; forms a program from its encoding, arities and rules.
- `penc`, `arity`, `rules` — fields; select the encoding, arities and rules of a program.
- `ground_atom` — Definition; a predicate paired with a tuple of constants.
- `lit_atom` — Definition; extracts the atom of a literal.
- `atom_vars` — Definition; lists variables occurring in an atom.
- `inst` — Definition; instantiates a term under a variable valuation.
- `ground` — Definition; instantiates an atom into a ground fact.
- `safe_rule` — Definition; requires head and negative variables in a positive literal.
- `program_wf` — Definition; requires safe rules and correct atom and fact arities.

### `RulesStratify.v` — RUL-1a

- `stratification` — Record; assigns predicate levels and a level count.
- `Stratification` — constructor; forms a stratification from levels and their bound.
- `level`, `count` — fields; select the predicate levels and their bound.
- `stratified` — Definition; checks level bounds and positive and negative dependencies.
- `stratify` — Definition; computes a stratification or reports failure.
- `stratify_sound` — Theorem; a computed stratification satisfies `stratified`.
- `stratify_complete` — Theorem; a stratifiable program receives a stratification.

### `RulesCompile.v` — RUL-1a

- `tuple_encoding` — Definition; encodes tuples as positive keys.
- `preds` — Definition; collects predicates occurring in rules and facts.
- `constants` — Definition; collects constants occurring in rules and facts.
- `in_universe` — Definition; tests a predicate and tuple against the finite universe.
- `herbrand` — Definition; proof-only list of tuples in the program universe.
- `relation` — Definition; finite tuple set inside the proof-only universe.
- `relation_lattice` — Definition; finite powerset lattice of relations.
- `restrict` — Definition; keeps a set's tuples inside a predicate's universe.
- `env_wf` — Definition; requires well-formed relations of the correct predicate arities.
- `fire_rule` — Definition; computes in-universe head tuples satisfying a rule body.
- `rconstraint` — Inductive; identifies a rule or fact constraint.
- `FromRule`, `FromFact` — constructors; identify rule and fact contributions.
- `rconstraint_encoding` — Definition; encodes rule and fact constraints.
- `stratum_system` — Definition; compiles one level into a constraint system.
- `stratum_static` — Definition; supplies static dependency evidence for that system.
- `herbrand_spec` — Theorem; characterises the tuples in the proof-only universe.
- `herbrand_nodup` — Theorem; the proof-only universe has no duplicate tuples.
- `restrict_spec` — Theorem; restriction keeps exactly the input's in-universe tuples.
- `fire_rule_exact` — Theorem; firing matches valuations satisfying a rule's body.
- `fire_rule_wf` — Theorem; firing produces a well-formed finite set.
- `fire_rule_complete` — Theorem; each satisfying in-universe valuation is fired.
- `stratum_system_monotone` — Theorem; a well-formed stratum system is monotone.

### `RulesModel.v` — RUL-1b

- `derives` — Inductive; derives facts and rule heads in one stratum.
- `derive_fact`, `derive_rule` — constructors; derive a fact or a satisfied rule head.
- `model_below` — Fixpoint; combines derivations below a given level.
- `perfect_model` — Definition; combines all strata of a stratification.
- `least_model` — Definition; selects the perfect model or the empty model on failure.
- `holds` — Definition; tests model membership of a predicate and tuple.
- `least_model_closed` — Theorem; the model contains facts and is closed under rules.
- `model_constants` — Theorem; derived atoms lie in their predicates' universes.

### `RulesSolve.v` — RUL-1b

- `database` — Definition; maps predicates to finite tuple sets.
- `rel_of` — Definition; reads a database relation, defaulting to the empty set.
- `db_holds` — Definition; tests a tuple's membership in a database relation.
- `solve_program` — Definition; solves each stratum and returns a database or failure.
- `represents` — Definition; relates well-formed database relations to a model.
- `stratum_post_solution_contains` — Theorem; a stratum post-solution contains its derivations.
- `stratum_reached_derives` — Theorem; every reached tuple has a stratum derivation.
- `stratum_least_is_derives` — Theorem; a least stratum solution contains exactly its derivations.
- `solve_program_exact` — Theorem; a well-formed stratifiable program yields its least model.
- `solve_program_none` — Theorem; an unstratifiable program yields no database.

## Float

Contract: [Float](float.md).

### `FloatInterval.v` — FLT-1

- `fle` — Definition; compares floats using the Flocq comparison.
- `subnormal` — Definition; identifies finite nonzero floats below the normal threshold.
- `fl_nn` — Definition; subtype of floats that are not NaNs.
- `fl_interval` — Record; bounds nonzero values and tracks NaN, zero and subnormal cases.
- `FlInterval` — constructor; builds an interval from bounds and flags.
- `flo`, `fhi` — fields; select lower and upper interval bounds.
- `may_nan`, `may_neg_zero`, `may_pos_zero`, `may_subnormal` — fields; track special cases.
- `fl_gamma` — Definition; states that a float belongs to an interval.
- `fl_lattice` — Definition; interval lattice with widening and narrowing.
- `fl_concretisation` — Definition; interval concretisation built from `fl_gamma`.
- `fl_top` — Definition; interval containing every float.
- `fl_top_lattice` — Definition; top evidence for the interval lattice.
- `fl_widening_rank` — Definition; bounded rank for interval widening.
- `fl_lattice_laws` — Theorem; interval lattice and concretisation satisfy their laws.
- `fl_top_sound` — Theorem; every float belongs to `fl_top`.
- `fl_bot_empty` — Theorem; the bottom interval contains no float.
- `subnormal_proper` — Theorem; a subnormal and a non-subnormal float exist.

### `FloatOps.v` — FLT-1

- `farith` — Inductive; arithmetic operators returning floats.
- `FAdd`, `FSub`, `FMul`, `FDiv` — constructors; select arithmetic operations.
- `fbop` — Inductive; arithmetic or less-than binary operation.
- `FArith`, `FLt` — constructors; select arithmetic and comparison operations.
- `nan_model` — Record; supplies NaN choices and their locality laws.
- `NanModel` — constructor; builds a NaN model from choices and proofs.
- `nan_choice`, `nan_neg`, `nan_abs` — fields; choose NaN results for the operations.
- `nan_choice_nan`, `nan_choice_local` — fields; require NaN results and local binary choice.
- `nan_neg_nan`, `nan_abs_nan` — fields; require NaN results for unary choices.
- `default_nan_model` — Definition; chooses one fixed quiet NaN for every operation.
- `fl_eval_bin` — Definition; evaluates float arithmetic with a NaN model.
- `fl_eval_neg`, `fl_eval_abs` — Definitions; evaluate negation and absolute value.
- `fl_lt` — Definition; tests float less-than, returning false for unordered values.
- `fl_bin` — Definition; computes an outward-rounded binary interval result.
- `fl_neg`, `fl_abs` — Definitions; compute interval negation and absolute value.
- `fl_assume_lt` — Definition; refines two intervals under a less-than assumption.
- `fl_bin_sound` — Theorem; binary interval evaluation contains the concrete result.
- `fl_neg_sound`, `fl_abs_sound` — Theorems; unary interval results contain concrete results.
- `fl_assume_lt_sound` — Theorem; comparison refinement retains satisfying operands.

### `FloatNan.v` — FLT-1

- `nan_demand` — Inductive; records whether a value and NaN sign or payload are demanded.
- `NotDemanded`, `Demanded` — constructors; select no demand or NaN observability flags.
- `ff_agree` — Definition; compares full floats under NaN sign and payload demands.
- `nan_agree` — Definition; compares floats under a `nan_demand`.
- `nan_domain` — Definition; demand lattice and agreement for float values.
- `nan_back` — Definition; computes operand demands from a binary operation and result demand.
- `nan_lattice_laws` — Theorem; the NaN demand lattice satisfies its lattice laws.
- `nan_domain_laws` — Theorem; NaN agreement satisfies its laws and is trivial at bottom.
- `nan_back_sound` — Theorem; computed operand demands preserve arithmetic result agreement.
- `fl_lt_agrees` — Theorem; NaN-identity agreement preserves comparison results.

### `FloatSsa.v` — FLT-1

- `fw` — Inductive; identifies the two float widths.
- `F32`, `F64` — constructors; select binary32 and binary64.
- `float_ext_tag` — Definition; assigns an extension tag to a width and operation.
- `float_ext_decode` — Definition; decodes valid float extension tags.
- `float_ext` — Definition; evaluates float extension tags on Ssa values.
- `float_ext_sigs` — Definition; lists the float extension operator signatures.
- `fl_any` — Inductive; represents unreachable, width-specific and arbitrary Ssa facts.
- `FlBot`, `FlA32`, `FlA64`, `FlOther` — constructors; form the four value-fact cases.
- `fl_any_lattice` — Definition; lattice of float and arbitrary Ssa facts.
- `fl_any_concretisation` — Definition; relates float facts to Ssa values.
- `fl_any_top` — Definition; top evidence for the Ssa float lattice.
- `fl_any_widening_rank` — Definition; bounded widening rank for the Ssa float lattice.
- `float_ssa_domain` — Definition; sparse value domain for float extension operations.
- `float_problem` — Definition; sparse float analysis problem for an Ssa function.
- `nan_domain_ssa` — Definition; NaN demand and agreement lifted to optional Ssa values.
- `ssa_nan_demand_view` — Definition; Ssa operand and exit demands and backwards transfers.
- `float_ext_respects` — Theorem; extension evaluation respects the declared signatures.
- `float_ext_tag_decode` — Theorem; decoding a generated tag recovers its width and operation.
- `float_ext_decode_tag` — Theorem; a decoded tag is the tag of its decoded operation.
- `nan_domain_ssa_laws` — Theorem; the Ssa NaN demand domain satisfies its laws.
- `float_ssa_domain_laws` — Theorem; the sparse float value domain satisfies its laws.
- `ssa_float_value_sound` — Theorem; reachable Ssa values satisfy their computed float facts.
- `ssa_nan_demand_view_laws` — Theorem; the Ssa NaN demand view satisfies demand laws.
- `ssa_nan_demand_sound` — Theorem; agreeing initial states have the same behaviour.

## Graph

### `GraphCore.v` — GRA-1a

- `Graph.t`, `Graph.Make` — Record and constructor; graph with entries, nodes and labelled edges.
- `Graph.entries`, `Graph.nodes`, `Graph.out` — fields; entry nodes, all nodes and outgoing edges.
- `Graph.source`, `Graph.target` — fields; endpoints of an edge.
- `reachable`, `reachable_entry`, `reachable_step` — Inductive and constructors; entry
  reachability.
- `graph_wf` — Record; graph nodes and edge endpoints obey the graph invariants.
- `Build_graph_wf` — constructor; packages the graph well-formedness laws.
- `nodes_nodup`, `entries_in`, `out_source`, `out_target_in` — fields; graph well-formedness laws.
- `path`, `path_nil`, `path_cons` — Inductive and constructors; edge lists forming paths.
- `reaches`, `mutual` — Definitions; path reachability and mutual reachability.
- `acyclic`, `before` — Definitions; absence of nonempty cycles and strict list order.
- `set_entries`, `without`, `induced` — Definitions; change roots or restrict a graph by nodes.
- `edge_count` — Definition; sum of outgoing-list lengths over nodes.
- `reachable_iff_path`, `reachable_in_nodes` — Theorems; paths characterise reachability
  within nodes.

### `GraphPrepare.v` — GRA-1a

- `prepared`, `Prepared` — Record and constructor; indexed adjacency and binary traversal fuel.
- `out_index`, `in_index`, `fuel` — fields; successor and predecessor indexes and traversal bound.
- `prepare` — Definition; builds the indexes and fuel from a graph.
- `succ_edges`, `pred_edges` — Definitions; retrieve the indexed outgoing and incoming edges.
- `prepared_laws` — Record; the indexes agree with the graph and carry adequate fuel.
- `Build_prepared_laws` — constructor; packages prepared-index agreement and fuel laws.
- `succ_agrees`, `succ_domain` — fields; successor lists agree at nodes and are empty elsewhere.
- `pred_agrees`, `pred_domain`, `pred_nodup` — fields; predecessor membership, domain and
  uniqueness.
- `fuel_value` — field; fuel equals twice the node count plus the edge count and two.
- `ready` — Definition; graph well-formedness, unique outgoing edges and prepared-index laws.
- `reverse_graph`, `prepared_reverse` — Definitions; reverse edges and swap the prepared indexes.
- `prepare_ready`, `pred_edges_nodup` — Theorems; preparation is ready and predecessors are
  unique.
- `reverse_graph_ready`, `reverse_path` — Theorems; reversal preserves readiness and reverses
  paths.

### `GraphDfs.v` — GRA-1b

- `dfs_result`, `DfsResult` — Record and constructor; depth-first forest and traversal orders.
- `preorder`, `postorder`, `tree_edge` — fields; traversal orders and discovery edges.
- `pre_num`, `post_num`, `visited` — fields; traversal positions and reached nodes.
- `dfs`, `rpo` — Definitions; blocked iterative search and reverse postorder.
- `tree_parent`, `dfs_ancestor`, `ancestor_b` — Definitions; tree parent, ancestry and
  interval test.
- `retreating` — Definition; edge whose target is an ancestor of its source in the DFS forest.
- `dfs_exact`, `reachable_dfs`, `dfs_tree` — Theorems; exact search reachability and forest edges.
- `rpo_order`, `rpo_single_entry`, `rpo_parent_of_non_entry` — Theorems; reverse-postorder
  properties.
- `rpo_edge_classes`, `cycle_has_retreating_edge` — Theorems; edge classes and cycles in DFS.
- `ancestor_b_agrees` — Theorem; interval ancestry test agrees with DFS-tree ancestry.

### `GraphCertificate.v` — GRA-1b

- `check_path`, `tree_path` — Definitions; check an edge-list path and recover a DFS tree path.
- `check_path_correct`, `tree_path_valid` — Theorems; path checking and recovered paths are
  correct.

### `GraphDominance.v` — GRA-2a

- `dominates`, `strictly_dominates`, `immediately_dominates` — Definitions; semantic dominators.
- `idom_ancestor`, `forest_on` — Definitions; parent-map ancestry and forest well-formedness.
- `virtual_entries`, `virtual_graph`, `virtual_encoding`, `virtual_prepared` — virtual-root model.
- `dominates_refl`, `dominates_trans`, `dominates_iff_unreachable_without` — dominance laws.
- `virtual_entries_exact`, `virtual_graph_ready`, `virtual_path_iff`, `virtual_dominates_iff` —
  virtual-root reduction laws.

### `GraphSemiDominators.v` — GRA-2c

- `semidom_path`, `semidominator`, `virtual_dfs`, `semidominators` — shared DFS and semidominators.
- `semidominators_wf`, `semidominators_exact` — well-formedness and semantic characterization.

### `GraphLengauerTarjan.v` — GRA-2d

- `simple_lt_idom`, `simple_lt_idom_exact` — Lengauer–Tarjan producer and exactness.

### `GraphSemiNca.v` — GRA-2e

- `semi_nca_idom`, `semi_nca_idom_exact` — Semi-NCA producer and exactness.

### `GraphDominators.v` — GRA-2f

- `dom_tree`, `DomTree` — Record and constructor; dominator forest with ancestry intervals.
- `idom`, `tin`, `tout` — fields; immediate dominators and forest traversal intervals.
- `dom_algorithm`, `SimpleLT`, `SemiNCA`, `dominator_tree_with` — selectable direct backends.
- `chk_idom`, `check_idom` — Definitions; candidate immediate dominators and exactness checker.
- `dom_tree_of`, `dominates_b` — Definitions; number a parent forest and test ancestry by
  intervals.
- `flat_idom`, `flat_tree` — Definitions; conservative fallback parent map and tree.
- `dominator_exact`, `dominator_tree` — Definitions; checker acceptance and total checked tree.
- `chk_idom_wf`, `check_idom_sound`, `check_idom_complete` — Theorems; candidate and checker laws.
- `dom_tree_of_agrees`, `flat_idom_shape` — Theorems; forest intervals and fallback shape.
- `dominator_tree_sound`, `dominator_tree_exact` — Theorems; total-tree soundness and checked
  exactness.
- `dominator_tree_with_exact`, `dominator_exact_true` — selectable-tree and producer exactness.

### `GraphEdgeDominance.v` — GRA-2b

- `edge_dominates` — Definition; every entry path to a node traverses the edge.
- `edge_dom_index`, `dominating_edges` — Definitions; indexed edge dominators and their node
  query.
- `edge_dominates_iff` — Theorem; characterises edge dominance through incoming edges and
  dominance.
- `dominating_edges_sound`, `dominating_edges_exact` — Theorems; sound and exact indexed queries.
- `self_loop_not_edge_dominating` — Theorem; a self-loop does not dominate first arrival at
  its node.

### `GraphPostDominators.v` — GRA-2b

- `post_dominates`, `post_dominator_tree` — Definitions; exit-path dominance and reversed tree.
- `post_dominates_iff_reverse` — Theorem; post-dominance is dominance in the reversed graph.
- `post_dominator_tree_sound`, `post_dominator_tree_exact` — Theorems; soundness and exactness.

### `GraphScc.v` — GRA-3a

- `scc_result`, `SccResult` — Record and constructor; components and their positive indexes.
- `components`, `component_ids`, `component_at`, `comp_of` — fields; component lists and indexes.
- `scc_within`, `scc` — Definitions; Tarjan components within a node list and the entire graph.
- `tarjan_frame`, `TarjanFrame` — Record and constructor; open node and remaining successor edges.
- `frame_node`, `frame_edges` — fields; node and remaining edges of a Tarjan frame.
- `tarjan_state`, `TarjanState` — Record and constructor; iterative Tarjan machine state.
- `frames`, `disc`, `low`, `pending`, `clock`, `emitted` — fields; stacks, numbers and output.
- `condensation` — Definition; component graph with original cross-component edges.
- `topological_order` — Definition; topological ordering of graph nodes.
- `scc_within_exact`, `scc_exact` — Theorems; component partitions and mutual reachability.
- `scc_reverse_topological` — Theorem; components are emitted after those they reach.
- `condensation_correct` — Theorem; condensation is a well-formed DAG with the specified edges.

### `GraphDag.v` — GRA-3b

- `topological_sort` — Definition; computation of a topological ordering.
- `path_weight` — Definition; sum of edge weights along a path.
- `dag_paths`, `DagPaths` — Record and constructor; maximum entry-path weights and witnesses.
- `best`, `via` — fields; maximum weights and selected final edges.
- `max_paths`, `max_path_to` — Definitions; compute maximum paths and recover a witness.
- `topological_sort_correct`, `max_paths_exact`, `max_paths_cycle` — Theorems; sorting and paths.

### `GraphChain.v` — GRA-3b

- `forward_step` — Definition; unique outgoing edge of a forwarding node, when present.
- `chain`, `chain_stop`, `chain_move` — Inductive and constructors; finite forwarding chains.
- `resolution`, `Landing`, `Cyclic` — Inductive and constructors; a landing node or a cycle.
- `resolve`, `resolve_all` — Definitions; resolve one or all forwarding chains.
- `resolve_correct` — Theorem; resolution agrees with finite chains and cycle detection.

### `GraphReducible.v` — GRA-4a

- `back_edge`, `reducible`, `reducible_b` — Definitions; dominance back edge and reducibility
  test.
- `back_edge_retreating`, `reducible_iff_retreating_back` — Theorems; DFS characterisation.
- `reducible_b_sound`, `reducible_b_correct` — Theorems; test soundness and exact-tree
  correctness.

### `GraphNaturalLoops.v` — GRA-4a

- `natural_loop`, `natural_loop_nodes` — Definitions; natural-loop membership and reverse search.
- `natural_loop_nodes_exact` — Theorem; computed nodes match natural-loop membership.

### `GraphLoops.v` — GRA-4b

- `loop_forest`, `LoopForest` — Record and constructor; recursively nested loop components.
- `loop_headers`, `loop_nodes`, `loop_parent`, `loop_of` — fields; headers, members and nesting.
- `loop_forest_of`, `in_loop`, `outer_nodes` — Definitions; construct and inspect loop nesting.
- `strong_component` — Definition; maximal nonempty mutual-reachability class.
- `loop_forest_nested`, `loop_forest_exact`, `loop_forest_covers` — Theorems; nesting and
  cycle coverage.

### `GraphWto.v` — GRA-4c

- `wto_of_valid` — Theorem; the direct WTO producer returns a valid order.

- `wto_token`, `WVertex`, `WOpen`, `WClose` — Inductive and constructors; weak-order tokens.
- `wto` — Definition; flat list of weak-order tokens.
- `balanced_from`, `annotate` — Fixpoints; check nesting and attach enclosing-head stacks.
- `wto_order`, `wto_valid` — Definitions; textual vertex order and Bourdoncle validity.
- `check_wto`, `wto_of` — Definitions; weak-order checker and candidate producer.
- `wto_all_heads`, `wto_total` — Definitions; nested all-heads fallback and checked total
  producer.
- `check_wto_correct`, `wto_valid_cycles` — Theorems; checker correctness and cycle coverage.
- `wto_all_heads_valid`, `wto_total_valid` — Theorems; fallback and total producer are valid.

### `GraphFrontier.v` — GRA-5

- `in_df`, `in_idf`, `idf_step` — Definition, Inductive and constructor; frontier and closure.
- `dominance_frontier`, `iterated_frontier` — Definitions; compute frontiers and their closure.
- `dominance_chain` — Theorem; a runner chain identifies an edge's frontier witnesses.
- `dominance_frontier_exact`, `iterated_frontier_exact` — Theorems; computed frontiers are exact.

### `GraphIdf.v` — GRA-7

- `in_pruned_idf`, `pruned_idf_step`, `direct_idf`, `direct_pruned_idf` — iterated frontiers.
- `direct_idf_exact`, `direct_pruned_idf_exact` — exactness of both queries.

### `GraphControlDependence.v` — GRA-5

- `control_dependent`, `cdep` — Definitions; edge and node control dependence by post-dominance.
- `exits_reachable` — Definition; every graph node has a path to an exit.
- `control_deps` — Definition; index control-dependence edges by dependent node.
- `control_deps_exact` — Theorem; computed control-dependence edges match the semantic definition.

### `GraphInterference.v` — GRA-6a

- `interference`, `Interference` — Record and constructor; symmetric loop-free interference graph.
- `vertices`, `adjacent` — fields; graph vertices and neighbour sets.
- `empty_interference`, `neighbours`, `interferes` — Definitions; empty graph and adjacency
  queries.
- `interference_wf` — Record; graph symmetry, absence of self-loops and index well-formedness.
- `Build_interference_wf` — constructor; packages interference graph laws.
- `interferes_sym`, `interferes_irrefl`, `interferes_vertex` — fields; interference graph laws.
- `vertices_wf`, `adjacent_wf`, `neighbours_wf` — fields; set and map well-formedness.
- `add_point` — Definition; add interference from definitions and live values at a point.
- `add_point_exact`, `add_point_vertices`, `add_point_wf` — Theorems; observer-step properties.

### `GraphColour.v` — GRA-6a

- `colour_result`, `ColourResult` — Record and constructor; assigned colours and spilled vertices.
- `colours`, `spilled` — fields; colour assignments and spill list.
- `proper_colouring` — Record; range, coverage, adjacency and precolouring properties.
- `Build_proper_colouring` — constructor; packages proper-colouring laws.
- `colour_below_k`, `vertex_decided`, `spilled_uncoloured` — fields; colour and spill validity.
- `adjacent_differ`, `precoloured_kept` — fields; distinct neighbours and preserved precolouring.
- `check_colouring`, `precolour_ok` — Definitions; check a colouring and valid precolouring.
- `greedy_colour`, `all_spilled` — Definitions; greedy colouring and conservative spill fallback.
- `check_colouring_correct`, `greedy_colour_proper`, `greedy_no_spill` — Theorems; colouring laws.

### `GraphBriggs.v` — GRA-6b

- `briggs_colour`, `colour_checked` — Definitions; optimistic colouring and checked fallback.
- `degenerate` — Definition; graph admits complete simplification below the colour bound.
- `briggs_colour_proper`, `colour_checked_proper`, `briggs_no_spill` — Theorems; colouring
  guarantees.

## Fixpoint

### `FixpointQuery.v` — FIX-1

- `Query.t`, `Query.Ret`, `Query.Ask`, `Query.Side` — Inductive and constructors; query trees.
- `Query.eval`, `Query.reads`, `Query.sides` — Fixpoints; result, reads and contributions of a
  query.
- `Query.run` — Fixpoint; obtain result, reads and contributions in one traversal.
- `ask_all`, `side_all` — Fixpoints; sequence reads and contributions.
- `query_determined`, `run_spec` — Theorems; read agreement determines a query and `run` agrees.
- `ask_all_spec`, `side_all_spec` — Theorems; sequence helpers have the stated read and side
  effects.

### `FixpointSystem.v` — FIX-1

- `System.t`, `System.Make` — Record and constructor; a system of targeted query constraints.
- `System.constraints`, `System.target`, `System.rhs` — fields; constraints, targets and queries.
- `System.static`, `System.Static` — Record and constructor; declared reads and side targets.
- `System.deps`, `System.side_targets` — fields; declared reads and contributions for each
  constraint.
- `System.reads_within`, `System.sides_within` — fields; declarations cover actual reads and
  effects.
- `deps`, `side_targets` — Notations; aliases for static-system projections.
- `post_solution` — Definition; every result and contribution lies below its assigned unknown.
- `assignment`, `lookup` — Definitions; finite assignment and lookup with bottom default.
- `monotone_query`, `monotone_system` — Definitions; monotonicity of results and contributions.
- `top_post_solution` — Theorem; the constant top assignment satisfies every constraint.

### `FixpointIndex.v` — FIX-1

- `sys_index`, `SysIndex` — Record and constructor; indexes of contributors and readers.
- `contributors`, `readers` — fields; maps from unknowns to contributing and reading constraints.
- `index_system`, `contributors_of`, `readers_of` — Definitions; build and query static indexes.
- `sys_index_laws` — Record; membership agreement and uniqueness of index lists.
- `Build_sys_index_laws` — constructor; packages system-index agreement laws.
- `contributors_agree`, `readers_agree`, `index_nodup` — fields; index agreement and uniqueness.
- `index_system_laws` — Theorem; the constructed system index satisfies its laws.

### `FixpointCheck.v` — FIX-1

- `check_post` — Definition; check all constraint results and contributions against an assignment.
- `check_post_iff` — Theorem; the full checker decides the post-solution property.

### `FixpointCut.v` — FIX-1

- `cut_certificate`, `CutCertificate` — Record and constructor; cut values and recomputation plan.
- `cuts`, `stored`, `plan` — fields; cut points, stored values and non-cut evaluation order.
- `plan_valid` — Definition; plan coverage, uniqueness and dependency order.
- `expand` — Definition; check a cut certificate and recompute the remaining assignment.
- `replay` — Definition; fold an observer over unknowns and their assignment values.
- `expand_sound`, `expand_complete` — Theorems; accepted certificates and completeness conditions.
- `plan_valid_cuts` — Theorem; a valid plan's cut points intersect every flow cycle.
- `replay_invariant`, `replay_covers` — Theorems; observer invariants and certificate coverage.

### `FixpointLeast.v` — FIX-1

- `join_update`, `run_updates`, `apply_updates` — Definitions; collect and apply constraint
  updates.
- `raise`, `reached` — Definitions; one constraint run and assignments reachable from bottom.
- `least_solution` — Definition; post-solution below all post-solutions.
- `reached_below`, `reached_least`, `least_solution_unique` — Theorems; least-solution properties.

### `FixpointCycles.v` — FIX-1

- `flows`, `cuts_every_cycle` — Definitions; static unknown dependencies and cycle-cutting sets.

### `FixpointWorklist.v` — FIX-2a

- `scheduler`, `Scheduler` — Record and constructor; priorities and widening points.
- `priority`, `widening_point` — fields; queue priority and widening-site predicate.
- `strategy`, `Joining`, `Widening` — Inductive and constructors; update strategies.
- `dependencies`, `Declared`, `Recorded` — Inductive and constructors; static or observed reads.
- `dependencies_ok` — Definition; declared index laws or trivial recorded-dependency condition.
- `Engine.t`, `Engine.State` — Record and constructor; worklist engine state.
- `Engine.current`, `Engine.queue`, `Engine.recorded` — fields; values, pending constraints
  and reads.
- `initial_state`, `engine_step` — Definitions; initialize and advance the worklist engine.
- `engine_rel`, `engine_reachable` — Definitions; successor relation and reachable engine states.
- `engine_steps`, `steps_zero`, `steps_succ` — Inductive and constructors; finite engine runs.
- `outcome`, `Done`, `Pending` — Inductive and constructors; finished assignment or pending state.
- `then_run`, `loop` — Definition and Fixpoint; compose outcomes and run binary fuel.
- `run_worklist`, `solve_fuel` — Definitions; fuel-bounded run and sound top-fallback solver.
- `engine_finished_sound` — Theorem; a finished reachable engine state is a post-solution.
- `run_worklist_spec`, `run_worklist_sound`, `run_worklist_acc` — Theorems; run semantics and
  adequacy.

### `FixpointTotal.v` — FIX-2b

- `terminates` — Definition; height or widening-rank evidence and cycle-cutting widening points.
- `solve_total` — Definition; accessibility-based solver returning a proved post-solution.
- `engine_acc`, `run_worklist_adequate` — Theorems; evidence yields accessibility and enough fuel.
- `solve_fuel_exact`, `solve_total_run` — Theorems; sufficient fuel agrees with the solver run.
- `solve_total_reached`, `solve_total_least` — Theorems; joining reaches a least solution.

### `FixpointSchedule.v` — FIX-3

- `unknowns`, `dependency_graph` — Definitions; static unknowns and their flow graph.
- `rpo_scheduler`, `wto_scheduler`, `scc_scheduler` — Definitions; graph-based worklist
  schedulers.
- `plan_of` — Definition; derive a non-cut plan from cycle-cutting points.
- `unknowns_spec`, `dependency_graph_flows`, `dependency_graph_ready` — Theorems; graph
  construction.
- `rpo_scheduler_cuts`, `wto_scheduler_cuts`, `scc_scheduler_cuts` — Theorems; widening points
  cut cycles.
- `plan_of_valid` — Theorem; plan construction succeeds exactly for cycle-cutting points.

### `FixpointNarrow.v` — FIX-3

- `narrow_pass`, `narrow_checked` — Definitions; narrow assignments and check the resulting
  solution.
- `narrow_checked_post`, `narrow_checked_below` — Theorems; narrowing preserves soundness and
  decreases.

### `FixpointPartial.v` — FIX-4

- `closed_partial`, `dependency_closed` — Definitions; sound partial assignments and closed sets.
- `check_partial` — Definition; check constraints touching the explored set.
- `check_partial_correct` — Theorem; partial checker decides the closed-partial property.
- `closed_partial_extends`, `closed_partial_above_least` — Theorems; extension and
  least-solution bound.
- `post_solution_closed` — Theorem; a post-solution restricts to a dependency-closed partial
  solution.

### `FixpointLocal.v` — FIX-4

- `local_result`, `LocalResult` — Record and constructor; explored unknowns and their assignment.
- `explored`, `values` — fields; explored set and computed assignment.
- `local_solve`, `local_checked` — Definitions; local producer and checked partial solution.
- `local_checked_sound` — Theorem; accepted results cover roots and form a closed partial
  solution.

## Examples

Contract: [Examples](examples.md).

### `ExamplesWhileSyntax.v` — EX-1

- `var` — Definition; While variable identifier.
- `unop`, `binop` — Inductives; unary and binary word operators.
- `Neg`, `BNot`, `LNot`, `Add`, `Sub`, `Mul`, `And`, `Or`, `Xor`, `Shl`, `ShrU`, `ShrS`,
  `Eq`, `Ne`, `LtU`, `LeU`, `LtS`, `LeS` — constructors; While operators.
- `expr` — Inductive; While expression syntax.
- `EConst`, `EVar`, `EUn`, `EBin` — constructors; constants, variables and applications.
- `stmt` — Inductive; While statement syntax.
- `SSkip`, `SAssign`, `SSeq`, `SIf`, `SLoop`, `SBreak`, `SContinue`, `SOutput` — constructors;
  While statements.

### `ExamplesWhileSemantics.v` — EX-1

- `wrap32`, `signed32`, `eval_un`, `eval_bin` — Definitions; concrete 32-bit operator semantics.
- `store`, `update`, `eval_expr` — Definitions and Fixpoint; stores, updates and expression
  evaluation.
- `wframe`, `config`, `target_cont` — Inductives; control frames, configurations and jump targets.
- `KSeq`, `KJoin`, `KLoop`, `KExit`, `Run`, `Enter`, `WhileFin`, `JRun`, `JFin` — constructors;
  While control states.
- `jump_cont` — Definition; resolves a relative jump against control frames.
- `step_w` — Inductive; small-step execution with output events.
- `w_skip`, `w_assign`, `w_output`, `w_seq`, `w_if`, `w_loop`, `w_enter`, `w_break`, `w_continue`,
  `w_fin_seq`, `w_fin_join`, `w_fin_exit`, `w_fin_loop` — constructors; the While step rules.
- `while_semantics`, `while_endings`, `store_of_config`, `word_stores`, `var_encoding` —
  Definitions;
  semantics, endings, store projection, initial-store predicate and variable encoding.

### `ExamplesWhileBridge.v` — EX-4

- `un_bits`, `bin_bits`, `env2` — Definitions; translate word operators and construct operand
  environments.
- `un_bridge`, `bin_bridge`, `eval_expr_word` — Theorems; operator bridges and word preservation.

### `ExamplesWhileSkeleton.v` — EX-4

- `atom` — Inductive; atomic actions of the skeleton translation.
- `ANop`, `AAssign`, `AOutput` — constructors; While skeleton atoms.
- `loops_ok`, `to_skeleton` — Fixpoints; check loop depths and translate statements.
- `while_client` — Definition; While operations for the skeleton machine.
- `match_state` — Inductive; relates While configurations to skeleton states.
- `while_skeleton_bisimulation`, `match_state_initial`, `while_behaviour_transport` — Theorems;
  bisimulation, matching initial states and preservation of behaviour.

### `ExamplesWhileViews.v` — EX-4

- `while_skel_vars`, `while_var_view`, `while_region_alg` — Definitions; variable and region
  adapters.
- `while_region_alg_agrees` — Theorem; the region summary agrees with completion and escaping
  labels for every skeleton.
- `while_effects`, `while_effects_view`, `while_demand_view`, `while_genkill_view`,
  `while_copy_view` —
  Definitions; While effects, demand, expression and copy adapters.
- `erase_dead`, `while_dce`, `while_erasure` — Fixpoint and Definitions; dead-assignment erasure.
- `while_client_laws`, `while_skel_vars_laws`, `to_skeleton_labels_ok`, `while_var_view_laws`,
  `while_effects_laws`, `while_demand_laws`, `while_genkill_laws`, `while_copy_sound`,
  `while_never_traps`, `while_erasure_laws`, `while_dce_sound` — Theorems; adapter laws and
  behaviour preservation of dead-code erasure.

### `ExamplesSsaSyntax.v` — EX-2

- `func`, `label`, `vid` — Definitions; function, block and value identifiers.
- `iw`, `msize`, `ty`, `cval`, `bop`, `sop`, `instr`, `callee`, `terminator` — Inductives;
  widths, types, values, operators and instructions.
- `W32`, `W64`, `M1`, `M2`, `M4`, `M8`, `TyI32`, `TyI64`, `TyPtr`, `TyFun`, `TyF32`, `TyF64`,
  `VInt`, `VPtr`, `VFun`, `VF32`, `VF64` — constructors; widths, types and concrete values.
- `BAdd`, `BSub`, `BMul`, `BDivU`, `BAnd`, `BOr`, `BXor`, `BShl`, `BShrU`, `BEq`, `BLtU`,
  `BLtS`, `OConst`, `OBin`, `OZext`, `OTrunc`, `OPtrAdd`, `OExt` — constructors; Ssa operators.
- `IOp`, `IAlloc`, `IFree`, `ILoad`, `IStore`, `IOutput`, `CDirect`, `CIndirect`, `TJump`, `TBr`,
  `TSwitch`, `TCall`, `TRet` — constructors; instructions, callees and terminators.
- `ty_of`, `valid_cval` — Definitions; concrete value type and integer word-range validity.
- `ssa_block`, `fdef`, `program` — Records; blocks, functions and programs.
- `SBlock`, `FDef`, `Program` — constructors; build blocks, functions and programs.
- `bparams`, `bbody`, `bterm`, `fentry`, `blocks`, `fresult`, `funcs`, `main`, `ext_sigs` — fields;
  select program structure and extension signatures.
- `find_func`, `find_block` — Definitions; look up functions and blocks.

### `ExamplesSsaTyping.v` — EX-2

- `iw_ty`, `op_sig`, `load_ok`, `static_ty`, `ext_respects`, `wf_program`, `wf_check`, `typed_env` —
  Definitions; typing, extension signatures, well-formedness and its checker.

### `ExamplesSsaTypingProofs.v` — EX-2

- `op_eval_typed`, `op_eval_valid`, `typed_state_reachable`, `typed_operands` — Theorems; operator
  and reachable-environment typing and integer ranges.
- `allocation_size_in_range`, `wf_check_sound`, `ext_respects_nil` — Theorems; allocation bounds,
  checker soundness and empty extension signatures.

### `ExamplesSsaSemantics.v` — EX-2

- `mval`, `event` — Inductives; memory fragments and observable events.
- `MInt`, `MFrag`, `EvOut`, `EvRet` — constructors; bytes and events.
- `mblock`, `sframe`, `state`, `limits` — Records; blocks, frames, machine states and limits.
- `MBlock`, `SFrame`, `State`, `Limits` — constructors; build machine state components.
- `msz`, `mbytes`, `mlive`, `msite`, `ffunc`, `flabel`, `fpc`, `fenv`, `fret`, `stack`, `mem`,
  `next_block`, `max_frames`, `max_blocks` — fields; select memory and machine state components.
- `op_eval`, `ssa_semantics`, `ssa_endings` — Definitions; operator evaluation and machine
  behaviour.
- `step_s` — Inductive; Ssa small-step semantics.

### `ExamplesSsaActivation.v` — EX-5a

- `astate` — Record; state of one function activation.
- `AState` — constructor; builds an activation state.
- `alabel`, `apc`, `aenv` — fields; select activation location and values.
- `activation`, `activation_endings` — Definitions; activation semantics and endings.
- `ssa_refined_value`, `SsaSourceValue`, `SsaCallResult`, `ssa_refined_point`,
  `SsaBeforeParams`, `SsaExecPoint`, `SsaCallReady`, `SsaAfterReturn`, `SsaDeadPoint`,
  `ssa_refined_edge`, `SsaBindParams`, `SsaInstruction`, `SsaMakeCallResult`, `SsaTransfer`,
  `SsaReturn` — Types and constructors; refined instruction-point graph.
- `ssa_refined_value_encoding`, `ssa_refined_point_encoding`, `ssa_refined_edge_encoding`,
  `ssa_refined_semantic_var_encoding` — Definitions; finite encodings.
- `ssa_refined_state`, `SsaRefinedState`, `srs_point`, `srs_env`, `srs_call_results`,
  `srs_pending`, `ssa_refined_semantic_var`, `SsaSourceVar`, `SsaCallVar`, `SsaPendingVar` —
  Types, constructors and fields; refined state and semantic variables.
- `ssa_refined_activation`, `ssa_refined_endings`, `ssa_refined_stable`, `ssa_refined_rel`,
  `ssa_refined_macro`, `SsaMacroLast`, `SsaMacroMore` — Definitions and constructors.
- `ssa_refined_initial`, `ssa_refined_step_correspondence`, `ssa_refined_behaviour` — Theorems;
  execution correspondence.

### `ExamplesSsaBridge.v` — EX-5a

- `ssa_truth`, `ssa_bridge` — Definitions; truth test and bridge to word expressions.
- `ssa_bridge_laws` — Theorem; the integer operator bridge is sound.

### `ExamplesSsaViews.v` — EX-5a

- `ssa_edge` — Record; slot-indexed Ssa graph edge.
- `SsaEdge` — constructor; builds an Ssa edge.
- `esrc`, `edst`, `eslot` — fields; select edge source, target and slot.
- `values_of`, `ssa_block_view`, `ssa_point_view` — Definitions; values and graph adapters.
- `ssa_refined_var_view`, `ssa_refined_points`, `ssa_refine_point`,
  `ssa_refined_semantic_var_view` — Definitions; refined models and analysis carriers (EX-5a).
- `ssa_refined_point_model`, `ssa_refined_point_laws`, `ssa_refined_liveness` — Theorems;
  model agreement, point laws and source-variable liveness correspondence (EX-5a).
- `ssa_refined_graph_agrees`, `ssa_refined_semantic_var_laws` — Theorems; semantic view laws and
  graph agreement (EX-5a).
- `instr_or_term` — Inductive; instruction or terminator.
- `AnInstr`, `ATerm` — constructors; embed an instruction or terminator.
- `call_site`, `ssa_effects`, `ssa_var_view`, `ssa_demand_view` — Definitions; call sites and
  adapters.
- `ssa_truth_nonzero`, `ssa_block_view_laws`, `ssa_var_view_laws`, `ssa_demand_view_laws` —
  Theorems;
  truth and Ssa adapter laws.

### `ExamplesSsaStrict.v` — EX-5c

- `frame_activation` — Definition; extracts an activation from a full state frame.
- `subtrace` — Inductive; subsequence relation on traces.
- `sub_nil`, `sub_keep`, `sub_skip` — constructors; empty, retained and skipped trace events.
- `ssa_strict_laws`, `activation_lifting` — Theorems; strict SSA and activation trace lifting.
- `ssa_refined_reachable_strict` — Theorem; reachable strict SSA for the refined model.

### `ExamplesSsaEffects.v` — EX-5b

- `ssa_effects_view`, `ssa_calls`, `ssa_resolver` — Definitions; effects and call adapters.
- `ssa_effects_laws`, `ssa_calls_laws` — Theorems; the effects and calls views satisfy their laws.

### `ExamplesSsaMemory.v` — EX-6

- `full_node`, `ssa_full_view`, `ssa_mem_view` — Definitions; full-program graph and memory
  adapters.
- `full_edge` — Record; edge of the full-program graph.
- `FullEdge` — constructor; builds a full-program edge.
- `fsrc`, `fdst`, `fslot` — fields; select full-edge source, target and slot.
- `ssa_full_view_laws`, `ssa_mem_laws` — Theorems; graph and memory adapter laws.

### `ExamplesSsaPointers.v` — ANA-9

- `ssa_ptr_ops`, `ssa_ptr_view`, `ssa_footprints` — Definitions; pointer effects, view and
  footprints.
- `ssa_raw_site`, `ssa_rel_ptr_view` — Definitions; speculative sites and relational observations.
- `ssa_rel_ptr_laws`, `ssa_rel_value_covers`, `ssa_rel_heap_covers` — Theorems; relational laws
  and concrete observation coverage.
- `ssa_ptr_pop_listed`, `ssa_zero_laws` — Theorems; effect inventory and zero-fact adapter laws.

### `ExamplesSsaBytes.v` — ANA-10a

- `ssa_bytes_view` — Definition; byte view and coarse write ranges.
- `ssa_bytes_laws` — Theorem; byte view laws.

### `ExamplesWhileAnalyses.v` — EX-4, ANA-2

- `expr_encoding`, `while_live_at`, `while_needed`, `while_dead_var`, `loop_head`,
  `lcm_extended_view`, `lcm_avail`, `lcm_busy`, `lcm_avail2` — Definitions; EX-4 encodings,
  executable analysis wrappers and loop and code-motion fixtures.
- `while_liveness_sound`, `while_reaching_sound`, `while_zero_since_entry_sound`,
  `while_equality_sound`, `while_available_sound`, `while_busy_sound` — Theorems; EX-4
  specializations of dense analysis soundness.
- `while_structured_liveness_sound`, `while_certificate_sound`, `while_certificate_complete`,
  `while_region_table_agrees` — Theorems; ANA-2 structured analysis and certificate claims.
- `factorial_while`, `factorial_while_dce`, `z_var`, `lcm_prog`, `lcm_result_ex` — Definitions;
  EX-4 factorial and lazy-code-motion fixtures.

### `ExamplesSsaAnalyses.v` — EX-5a, ANA-3, ANA-6, ANA-9, EX-7 facade

C62 routes the ANA-5, ANA-7, ANA-8, ANA-10a and ANA-10e declarations in this inventory to
`ExamplesSsaNumbering.v`, `ExamplesSsaScev.v`, `ExamplesSsaCalls.v`,
`ExamplesSsaMemoryBase.v` and `ExamplesSsaMemoryLegacy.v`, respectively. EX-7 provides their
original qualified facade paths and preserves the other paths after all six prerequisite cards
land; until then those legacy paths are pending. EX-7 moves the existing facade body to
`ExamplesSsaAnalysisBase.v` and retargets the five client modules before adding explicit aliases.
The entries below retain the full compatibility inventory and their original declaration owners.

- `label_encoding`, `sop_encoding`, `const_numeric`, `const_conc`, `liveness_at` — Definitions;
  EX-5a encodings, constant domain and executable liveness wrapper.
- `ok_i32`, `mul_one_rules`, `mul_one_term`, `unit_cost` — Definitions; ANA-6 e-graph fixtures.
- `mul_one_rules_sound` — Theorem; ANA-6 validates the multiplication rewrite.
- `ssa_sccp_sound`, `ssa_guard_chain_sound` — Theorems; ANA-3 value and guard soundness.
- `ssa_dead_value_removable` — Theorem; EX-5a specializes neededness to an Ssa activation.
- `ssa_summary_sound`, `ssa_recursion_sound`, `ssa_unreachable_sound`, `ssa_stack_demand_sound`,
  `ssa_callee_leaf_sound` — Theorems; ANA-8 call and summary claims.
- `ssa_andersen_sound`, `ssa_steensgaard_sound`, `ssa_escape_sound` — Theorems; ANA-9 pointer
  and escape claims.
- `ssa_immutable_sound` — Theorem; ANA-10a preservation of unwritten bytes.
- `factorial_ssa`, `z_value`, `p_value`, `loop_header_point` — Definitions; EX-5a factorial fixture.
- `gvn_prog`, `gvn_first`, `gvn_second`, `gvn_problem` — Definitions; ANA-5 numbering fixture.
- `gvn_binding_state`, `gvn_binding_observation`, `gvn_binding_observation_laws`,
  `gvn_binding_witness`, `gvn_binding_home_dominates`, `gvn_binding_equal` — ANA-5 binding client.
- `gvn_use_prog`, `gvn_use_problem`, `gvn_use_state`, `gvn_use_observation`,
  `gvn_use_observation_laws`, `gvn_use_witness`, `gvn_use_equal` — ANA-5 dominated-use client.
- `gvn_phi_prog`, `gvn_phi_problem`, `gvn_phi_left`, `gvn_phi_right`, `gvn_phi_observation`,
  `gvn_phi_observation_laws`, `gvn_phi_checked`, `gvn_phi_witness`, `gvn_phi_equal` — ANA-5
  cyclic parameter client and finite history.
- `gvn_loop_prog`, `gvn_loop_problem`, `gvn_loop_info`, `gvn_loop_value` — ANA-5 loop client.
- `gvn_loop_laws`, `gvn_loop_wf`, `gvn_loop_invariant`, `gvn_loop_stability`, `gvn_loop_run`,
  `gvn_loop_recomputed`, `gvn_loop_sound` — ANA-5 loop evidence and application.
- `count_up`, `count_up_n`, `count_up_chrec`, `count_up_inv` — Definitions; ANA-7 recurrence
  fixture.
- `count_up_inventory`, `count_up_ops`, `count_up_loop` — Definitions; ANA-7 recognition inputs
  and actual activation adapter.
- `count_up_ops_laws`, `count_up_loop_laws`, `count_up_recognise`, `count_up_recurrence`,
  `count_up_trip_bound` — Theorems; ANA-7 client laws and generic recurrence and trip applications.
- `chain_graph`, `chain_writes`, `chain_writes_clobber`, `chain_reads`, `chain_ssa` — Definitions;
  ANA-10e MemorySSA fixtures.

### Computed Examples in `tests/Examples`

- `ExamplesWhileViewsTest.v` — EX-4: `while_z_live`, `while_z_dead`, `while_dce_factorial`,
  `while_lcm_accepts`.
- `ExamplesSsaViewsTest.v` — EX-5a: `factorial_wf`, `factorial_z_live`, `factorial_z_dead`,
  `factorial_p_needed`.
- `ExamplesSsaANA5Test.v` — ANA-5: `gvn_merges`.
- `ExamplesSsaANA6Test.v` — ANA-6: `egraph_optimise_accepts`.
- `ExamplesSsaANA7Test.v` — ANA-7: `scev_count_up_trip`.
- `ExamplesSsaANA10eTest.v` — ANA-10e: `memoryssa_accepts`, `memoryssa_rejects`.

## Views

### `ViewsSemantics.v` — VIEW-1

- `semantics`, `Semantics` — Record, constructor; initial states and labeled steps from the anchors.
- `initial`, `step` — Fields; select initial states and labeled transitions.
- `endings`, `Endings` — Record, constructor; classify final, trapped, and stopped states.
- `final`, `trapped`, `stopped` — Fields; identify the three ending classes.
- `running`, `stuck` — Definitions; identify states with a step and states with no step
  or ending.
- `endings_wf` — Record; ending classes halt and are pairwise disjoint.
- `final_halts`, `trapped_halts`, `stopped_halts` — Fields; each ending class cannot step.
- `final_not_trapped`, `final_not_stopped`, `trapped_not_stopped` — Fields; endings are
  disjoint.
- `exec`, `exec_refl`, `exec_step` — Inductive, constructors; finite traced execution.
- `exec_in`, `exec_in_refl`, `exec_in_step` — Inductive, constructors; execution within
  a predicate.
- `diverges`, `diverges_step` — CoInductive, constructor; infinite execution.
- `reachable_state` — Definition; a state reached by a finite run from an initial state.
- `ending`, `EndFinal`, `EndTrap`, `EndStop`, `EndStuck` — Inductive, constructors;
  ending kinds.
- `ends_as` — Definition; a state has the given ending kind.
- `diverges_after` — Definition; divergence follows a finite trace.
- `same_behaviour` — Record; two states have equal finish, prefix, and divergence observations.
- `same_finish`, `same_prefix`, `same_diverging_prefix` — Fields; equal observable run sets.
- `bisimulation` — Record; lock-step matching of endings and steps in both directions.
- `bisim_ends`, `bisim_forth`, `bisim_back` — Fields; ending and step matching obligations.
- `stuttering` — Record; two-way matching with decreasing measures for unmatched silent steps.
- `st_ends_forth`, `st_ends_back` — Fields; match all endings, including stuck, after silent runs.
- `st_forth`, `st_back` — Fields; match steps or take a decreasing silent step.
- `bisimilar_same_behaviour` — Theorem; bisimilar states have equal observable behaviour.
- `stuttering_same_behaviour` — Theorem; stuttering-related states have equal behaviour.
- `same_behaviour_sym`, `same_behaviour_trans` — Theorems; behaviour equality is symmetric
  and transitive.
- `exec_in_exec`, `exec_in_app` — Theorems; restricted runs are runs and compose by trace
  append.

### `ViewsGraph.v` — VIEW-1

- `graph_view`, `GraphView` — Record, constructor; connect semantic states and steps to a graph.
- `cfg`, `point`, `taken`, `stays` — Fields; graph, state point, edge step, and point-preserving
  step.
- `graph_view_laws` — Record; graph and reachable semantic steps satisfy the view contract.
- `cfg_wf`, `entry_points`, `edge_covers` — Fields; graph validity, entries, and step coverage.
- `taken_edge`, `stays_point` — Fields; taken edges and stay steps agree with state points.
- `edges_of` — Definition; enumerate all graph out-edges.
- `dense_constraint`, `Seed`, `Flow` — Inductive, constructors; seed and edge-transfer
  constraints.
- `dense_constraint_encoding` — Definition; encode dense constraints using node and edge codes.
- `forward_system`, `forward_static` — Definitions; forward edge system and static dependencies.
- `backward_system`, `backward_static` — Definitions; backward edge system and static
  dependencies.
- `meets_every_cycle` — Definition; a node predicate visits each graph cycle.
- `run_edges`, `run_nil`, `run_cons`, `run_stay` — Inductive, constructors; edge history
  of a run.
- `last_writer` — Definition; last history edge writing a given value.
- `arrivals_since` — Definition; count back edges since the most recent entry edge.
- `forward_post_solution_iff`, `backward_post_solution_iff` — Theorems; characterize dense
  solutions.
- `forward_cuts_every_cycle`, `backward_cuts_every_cycle` — Theorems; graph cycle cuts
  cut flows.
- `run_edges_exec`, `exec_run_edges`, `run_edges_path` — Theorems; relate histories, runs,
  and paths.
- `run_edges_app`, `run_edges_snoc_inv` — Theorems; compose histories and decompose the
  last edge.
- `last_writer_snoc`, `arrivals_since_snoc` — Theorems; update history summaries for one edge.

### `ViewsForward.v` — VIEW-1

- `forward_inv` — Definition; reachable state satisfying the fact at its point.
- `forward_invariant_sound` — Theorem; forward post-solutions contain every reachable state.
- `forward_inv_invariant` — Theorem; the solution-relative forward predicate is an invariant.
- `forward_history_sound` — Theorem; forward facts contain the corresponding run histories.

### `ViewsAgreement.v` — VIEW-1

- `agreement_symmetric`, `agreement_swap` — Definitions; symmetry predicate and reversed
  agreement.
- `invariant_of` — Record; initial, preserved states are reachable.
- `inv_initial`, `inv_step`, `inv_reachable` — Fields; initiality, preservation, and
  reachability.
- `step_agrees`, `ends_agree`, `agreeing` — Definitions; step, ending, and state agreement
  obligations.
- `forth_agrees`, `ends_forth` — Definitions; one-direction step and all-ending matching
  obligations, including stuck.
- `step_agrees2`, `ends_agree2`, `agreeing2` — Definitions; two-program matching and
  related states.
- `reachable_invariant` — Theorem; reachability satisfies `invariant_of`.
- `agreement_bisimulation` — Theorem; backward agreement obligations give a bisimulation.
- `agreement_same_behaviour` — Theorem; agreeing states have the same behaviour.
- `agreement_simulation2` — Theorem; two-program agreement gives a stuttering simulation.

### `ViewsSkeleton.v` — VIEW-2

- `Skeleton.stmt` — Inductive; structured statements with relative-depth jumps.
- `Skeleton.Atom`, `Skeleton.Seq`, `Skeleton.If` — Constructors; atom, sequence, and branch.
- `Skeleton.Block`, `Skeleton.Loop` — Constructors; enclosing exit and repetition labels.
- `Skeleton.Jump`, `Skeleton.JumpIf`, `Skeleton.JumpTable` — Constructors; relative-depth jumps.
- `dir`, `DFirst`, `DSecond`, `DBody` — Inductive, constructors; child directions in
  a statement.
- `position`, `dir_encoding`, `position_encoding` — Definitions; position paths and their
  encodings.
- `child`, `sub`, `positions` — Definition, fixpoints; select children, select subtrees,
  list positions.
- `labels_ok` — Fixpoint; check relative jump depths against enclosing labels.
- `skeleton_client`, `SkeletonClient` — Record, constructor; client store, atoms, guards,
  and jumps.
- `init_store`, `atom_step`, `atom_trap`, `atom_stop` — Fields; initial stores and atom
  outcomes.
- `guard_bool`, `guard_index`, `jump_effect` — Fields; guard evaluation and jump store effect.
- `skeleton_client_laws` — Record; jump totality and atom progress and ending laws.
- `jump_total`, `atom_progress` — Fields; jumps have an effect and atoms step, trap, or stop.
- `atom_trap_halts`, `atom_stop_halts`, `atom_trap_not_stop` — Fields; atom endings are
  exclusive.
- `frame`, `FSeq`, `FJoin`, `FBlock`, `FLoop` — Inductive, constructors; continuation
  stack frames.
- `mstate`, `Go`, `Ret` — Inductive, constructors; running and completed skeleton positions.
- `resume` — Fixpoint; unwind frames to a relative jump label.
- `skel_step` — Inductive; one skeleton-machine transition.
- `step_atom`, `step_seq`, `step_if`, `step_block`, `step_loop` — Constructors; enter or
  run nodes.
- `step_jump`, `step_jump_if_taken`, `step_jump_if_skipped`, `step_jump_table` — Constructors;
  jumps.
- `step_ret_seq`, `step_ret_join`, `step_ret_block`, `step_ret_loop` — Constructors;
  resume frames.
- `skeleton_semantics`, `skeleton_endings` — Definitions; machine semantics and ending
  predicates.
- `store_of`, `stack_of` — Definitions; extract store and continuation stack from a machine
  state.
- `positions_exact` — Theorem; listed positions are exactly valid subtree positions.
- `skeleton_endings_wf`, `skeleton_not_stuck` — Theorems; machine endings are valid and
  progress holds.

### `ViewsStructured.v` — VIEW-2

- `skel_point`, `PEntry`, `PExit` — Inductive, constructors; entry and exit points of
  a position.
- `skel_point_encoding` — Definition; encode a skeleton point.
- `action`, `AAtom`, `AGuard`, `AIndexIs`, `AIndexAtLeast`, `AJump` — Inductive, constructors;
  edge actions.
- `skel_edge`, `SkelEdge`, `from`, `slot` — Record, constructor, fields; edge source and slot.
- `skel_edge_encoding` — Definition; encode a skeleton edge by source and slot.
- `act_hold` — Definition; one action's relation on stores and traces.
- `acts_hold`, `holds_nil`, `holds_cons` — Inductive, constructors; sequential action execution.
- `label_point` — Definition; resolve a relative label to its skeleton point.
- `skel_out`, `skel_nodes`, `skel_to`, `skel_acts` — Definitions; graph edges, nodes,
  targets, actions.
- `skeleton_graph`, `skeleton_view` — Definitions; graph and semantic view of a skeleton.
- `loop_heads`, `is_loop_head` — Definitions; enumerate and test skeleton loop heads.
- `traps_at`, `stops_at` — Definitions; trap and stop conditions at skeleton points.
- `store_agreement` — Definition; lift store agreement to skeleton-machine states.
- `skel_root`, `edge_fwd`, `edge_bwd` — Definitions; root test and action-folded edge transfers.
- `skeleton_forward`, `skeleton_forward_static` — Definitions; forward system and static
  dependencies.
- `skeleton_backward`, `skeleton_backward_static` — Definitions; backward system and
  dependencies.
- `skeleton_view_laws_hold` — Theorem; the skeleton view satisfies the graph-view laws.
- `skeleton_forward_sound` — Theorem; skeleton forward facts contain reachable stores.
- `skeleton_agreement_bisimulation` — Theorem; backward skeleton agreement gives bisimulation.
- `skeleton_cut_points` — Theorem; loop heads meet every skeleton graph cycle.
- `skeleton_forward_cuts`, `skeleton_backward_cuts` — Theorems; loop heads cut both systems'
  flows.
- `is_loop_head_iff` — Theorem; loop-head test agrees with the list of loop heads.

### `ViewsRegion.v` — VIEW-3

- `summary_algebra`, `SummaryAlgebra` — Record, constructor; fold operations for skeleton
  statements.
- `on_atom`, `on_seq`, `on_if`, `on_block`, `on_loop` — Fields; summaries of ordinary
  constructors.
- `on_jump`, `on_jump_if`, `on_jump_table` — Fields; summaries of jump constructors.
- `summarise` — Fixpoint; fold a summary algebra over a skeleton.
- `algebra_sound` — Record; each algebra operation preserves a stated meaning.
- `sound_atom`, `sound_seq`, `sound_if`, `sound_block`, `sound_loop` — Fields; ordinary cases.
- `sound_jump`, `sound_jump_if`, `sound_jump_table` — Fields; jump cases preserve meaning.
- `escapes` — Definition; external relative label depths reached by a region's jumps.
- `falls`, `falls_at` — Definitions; possible normal completion of a region or position.
- `nesting`, `skel_depth` — Fixpoints; maximum enclosing-label and statement depths.
- `seq_flat`, `seq_of_list` — Fixpoint, definition; flatten sequences and build balanced
  sequences.
- `summarise_sound` — Theorem; a sound algebra's fold satisfies its meaning.
- `escapes_labels_ok` — Theorem; escaping labels characterize valid enclosing depths.
- `nesting_le_skel_depth`, `position_length_le_depth` — Theorems; skeleton depth bounds
  both measures.
- `seq_of_list_flat`, `seq_of_list_depth` — Theorems; balanced construction preserves order
  and depth.
- `falls_sound`, `frames_bounded` — Theorems; reachable completion and stack depth are bounded.

### `ViewsSsa.v` — VIEW-4

- `definition`, `Op`, `Param`, `Arbitrary` — Inductive, constructors; value definition forms.
- `guard_kind`, `GTrue`, `GFalse`, `GConst`, `GNotConst` — Inductive, constructors; guard tests.
- `condition`, `Condition`, `subject`, `kind` — Record, constructor, fields; value and
  guard test.
- `ssa_view`, `SsaView` — Record, constructor; SSA definitions, graph, values, and operations.
- `base`, `def`, `home`, `params` — Fields; graph and block definitions of values.
- `edge_args`, `edge_guard`, `val`, `op_eval`, `truth` — Fields; edges and concrete value
  semantics.
- `holds_guard`, `cond_holds`, `guard_ops_consistent` — Definitions; guard and operand
  consistency.
- `ssa_view_laws` — Record; SSA graph, guard, and value-origin properties.
- `base_laws`, `param_defs`, `guards_ok`, `guard_op_defined`, `value_origin` — Fields; SSA laws.
- `sparse_domain`, `SparseDomain` — Record, constructor; lattice and abstract SSA operations.
- `fact_lat`, `fact_conc`, `top_fact`, `op_abs` — Fields; sparse facts and abstract operation.
- `assume_value`, `assume_args` — Fields; refine a value or comparison arguments under a guard.
- `sparse_domain_laws` — Record; lattice, concretisation, transfer, and refinement soundness.
- `dom_lattice`, `dom_conc`, `fact_bot_empty`, `top_sound` — Fields; basic sparse domain laws.
- `op_sound`, `assume_value_sound`, `assume_args_sound` — Fields; operation and refinement laws.
- `executable` — Definition; test whether a lifted fact exceeds bottom.
- `sparse_unknown`, `UVal`, `UEdge`, `UBlock` — Inductive, constructors; sparse analysis
  unknowns.
- `sparse_unknown_encoding` — Definition; encode value, edge, and block unknowns.
- `sparse_constraint` — Inductive; sparse conditional constraint kinds.
- `CBlockEntry`, `CEntryFact`, `COp`, `CArbitrary` — Constructors; entry and value constraints.
- `CArg`, `CEdge`, `CBlock` — Constructors; edge argument, feasibility, and block constraints.
- `sparse_constraint_encoding` — Definition; encode sparse constraints.
- `sparse_problem`, `SparseProblem` — Record, constructor; view, domain, values, and
  entry facts.
- `view`, `domain`, `sparse_values`, `entry_fact` — Fields; sparse problem inputs.
- `sparse_system`, `sparse_static` — Definitions; sparse conditional system and dependencies.
- `sparse_sound` — Theorem; reachable blocks, taken edges, and defined values satisfy
  sparse facts.

### `ViewsRefine.v` — VIEW-4

- `refine_fact`, `refine_on_edge` — Definitions; refine a value fact by an edge's guards.
- `edge_feasible` — Definition; test whether edge guard refinements allow execution.
- `refine_fact_sound`, `refine_on_edge_sound` — Theorems; guard refinement retains concrete
  values.
- `edge_feasible_sound` — Theorem; a taken edge is feasible under sound facts.

### `ViewsDominated.v` — VIEW-5

- `strict_ssa_laws` — Record; redefinitions and operands obey SSA dominance restrictions.
- `redefine_in_stay`, `redefine_on_edge` — Fields; value changes occur at their defining blocks.
- `frame_in_stay`, `frame_on_edge` — Fields; values are unchanged away from their homes.
- `guard_home`, `op_args_dominate` — Fields; guard and operand definitions dominate their uses.
- `dom_context`, `DomContext` — Record, constructor; prepared graph and dominance indexes.
- `dc_graph`, `dc_encoding`, `dc_prepared`, `dc_tree`, `dc_index` — Fields; dominance
  context parts.
- `make_dom_context`, `dominating_edges_in` — Definitions; prepare dominance and list
  dominating edges.
- `refined_fact` — Definition; refine a value fact using the edges dominating a block.
- `dominated_guard_holds` — Theorem; guards and operand equations hold at dominated
  reachable uses.
- `dominating_edges_in_sound` — Theorem; each indexed edge semantically dominates the
  queried block.
- `refined_fact_sound` — Theorem; dominated-edge refinement retains the reachable concrete
  value.

### `ViewsEffects.v` — VIEW-6

- `effects`, `Effects` — Record, constructor; conservative instruction effect flags.
- `reads`, `writes`, `may_trap`, `may_diverge`, `may_stop` — Fields; memory and control effects.
- `allocates`, `frees`, `calls`, `observes` — Fields; allocation, frame, and event effects.
- `effects_view`, `EffectsView` — Record, constructor; instruction, heap, heap agreement,
  and depth.
- `instr_at`, `heap`, `heap_agree`, `depth` — Fields; retrieve the effects view components.
- `diverges_within`, `within_step` — CoInductive, constructor; divergence above a frame depth.
- `effects_laws` — Record; effects flags soundly describe reachable steps and endings.
- `silent`, `trap_covered`, `stop_covered` — Fields; observation, trap, and stop coverage.
- `heap_frame`, `reads_frame`, `trap_frame`, `stop_frame` — Fields; heap independence
  and framing.
- `frame_frame`, `call_returns` — Fields; frame depth and nondiverging call properties.
- `silent_exec_in` — Theorem; a run through non-observing instructions emits no event.

### `ViewsCalls.v` — VIEW-6

- `calls_view`, `CallsView` — Record, constructor; functions, call sites, and active frames.
- `functions`, `roots`, `sites_of`, `caller_of`, `here`, `frames` — Fields; call-view
  components.
- `active` — Definition; current and suspended active functions.
- `call_edge`, `CallEdge`, `edge_site`, `edge_callee` — Record, constructor, fields;
  call-graph edge.
- `call_graph` — Definition; graph of resolved call targets from function roots.
- `calls_view_laws` — Record; sites, roots, reachable frames, and call-step shape are sound.
- `sites_caller`, `initial_roots`, `frames_listed`, `step_shape` — Fields; call-view
  obligations.
- `call_graph_wf` — Theorem; a valid calls view and resolver produce a well-formed call graph.
- `active_reachable_in_call_graph` — Theorem; active functions are reachable in the call graph.

### `ViewsSummary.v` — VIEW-6

- `summary_spec`, `SummarySpec` — Record, constructor; summary lattice and local and call
  transfers.
- `slat`, `local`, `via_call` — Fields; summary lattice, local fact, and callee transfer.
- `step_cover`, `StepCover`, `step_covers` — Record, constructor, field; summary covers a step.
- `summary_constraint`, `SLocal`, `SCall` — Inductive, constructors; local and call constraints.
- `summary_constraint_encoding` — Definition; encode a function or call-site/callee constraint.
- `summary_system`, `summary_static` — Definitions; summary constraints and static dependencies.
- `summary_laws` — Record; summary coverage is monotone and covers local and callee steps.
- `covers_monotone`, `local_covers`, `call_covers` — Fields; summary coverage obligations.
- `summary_sound` — Theorem; every active function's post-solution covers the current step.

### `ViewsMemory.v` — VIEW-7

- `mem_op`, `MemLoad`, `MemStore`, `MemCopy`, `MemFill`, `MemAlloc`, `MemFree` — Inductive,
  constructors; memory operations and their operands.
- `mem_view`, `MemView` — Record, constructor; memory instruction and pointer interpretation.
- `mem_instr`, `loc_of`, `loc_site`, `loc_offset` — Fields; access operation and pointer
  location.
- `mem_view_laws`, `site_stable` — Record, field; allocation sites persist across steps.
- `pointer_domain`, `PointerDomain` — Record, constructor; abstract pointers and reachable
  ranges.
- `ptr_lat`, `ptr_conc`, `ptr_reach` — Fields; pointer lattice, concretisation, and start
  offsets.
- `access_footprint` — Definition; byte ranges touched by an offset and width from abstract
  starts.
- `pointer_domain_laws`, `ptr_reach_sound` — Record, field; pointer ranges cover concrete
  starts.
- `loc_site_preserved` — Theorem; allocation sites persist along runs.
- `access_footprint_sound` — Theorem; computed load or store footprints cover accessed bytes.

## Bits

### `BitsWord.v` — BIT-1

- `width` — Definition; Positive word width.
- `modulus` — Definition; Power-of-two modulus for a width.
- `wrap` — Definition; Reduce an integer modulo the word modulus.
- `is_word` — Definition; Recognise integers in the word range.
- `word` — Definition; Width and integer pair.
- `half` — Definition; Half of the width modulus.
- `msb` — Definition; Most significant wrapped bit.
- `signed` — Definition; Signed two’s-complement view.
- `wrap_is_word` — Theorem; States `is_word w (wrap w z)`.
- `wrap_id` — Theorem; States `is_word w z -> wrap w z = z`.
- `wrap_wrap` — Theorem; States `wrap w (wrap w z) = wrap w z`.
- `wrap_add` — Theorem; States `wrap w (x + y) = wrap w (wrap w x + wrap w y)`.
- `wrap_mul` — Theorem; States `wrap w (x * y) = wrap w (wrap w x * wrap w y)`.
- `wrap_narrow` — Theorem; States `(w <= w2)%positive -> wrap w (wrap w2 z) = wrap w z`.

### `BitsFun.v` — BIT-1

- `wnot` — Definition; Bitwise complement.
- `wneg` — Definition; Modular negation.
- `wadd` — Definition; Modular addition.
- `wsub` — Definition; Modular subtraction.
- `wmul` — Definition; Modular multiplication.
- `wand` — Definition; Bitwise conjunction.
- `wor` — Definition; Bitwise disjunction.
- `wxor` — Definition; Bitwise exclusive-or.
- `wudiv` — Definition; Total unsigned division.
- `wurem` — Definition; Total unsigned remainder.
- `wsdiv` — Definition; Total signed division.
- `wsrem` — Definition; Total signed remainder.
- `wsmod` — Definition; Total signed modulus.
- `wshl` — Definition; Logical left shift.
- `wlshr` — Definition; Logical right shift.
- `washr` — Definition; Arithmetic right shift.
- `wrotl` — Definition; Left rotation.
- `wrotr` — Definition; Right rotation.
- `wclz` — Definition; Leading zero count.
- `wctz` — Definition; Trailing zero count.
- `wpopcnt` — Definition; Population count.
- `wult` — Definition; Unsigned less-than.
- `wule` — Definition; Unsigned less-than-or-equal.
- `wslt` — Definition; Signed less-than.
- `wsle` — Definition; Signed less-than-or-equal.

### `BitsOp.v` — BIT-1

- `op` — Inductive; Bit-vector operator syntax.
- `arity` — Definition; Number of operator operands.
- `result_width` — Definition; Check operand widths and return result width.
- `eval_op` — Definition; Evaluate a bit-vector operator.
- `word_fun1` — Definition; Select the unary same-width word function.
- `word_fun2` — Definition; Select the binary same-width word function.
- `word_cmp` — Definition; Select the word comparison function.
- `op_encoding` — Definition; Injective encoding of operators.
- `commutative` — Definition; Recognise commutative operators.
- `eval_op_total` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_width` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_arity` — Theorem; States `eval_op o xs = Some r -> List.length xs = arity o`.
- `eval_op_is_word` — Theorem; States `eval_op o xs = Some r -> is_word (fst r) (snd r)`.
- `eval_op_normalised` — Theorem;
  The operator rules: None only on arity or width mismatch; results are words of the rule's width.
- `eval_op_fun1` — Theorem; The operator rules agree with the word functions.
- `eval_op_fun2` — Theorem; The operator rules agree with the word functions.
- `eval_op_cmp` — Theorem; The operator rules agree with the word functions.
- `eval_op_ite` — Theorem; The operator rules agree with the word functions.
- `commutative_sound` — Theorem; Commutative operators give the same result in either order.
- `bvnot` — Constructor; Bitwise complement operator.
- `bvneg` — Constructor; Modular negation operator.
- `bvclz` — Constructor; Count leading zero bits.
- `bvctz` — Constructor; Count trailing zero bits.
- `bvpopcnt` — Constructor; Count set bits.
- `bvadd` — Constructor; Modular addition operator.
- `bvsub` — Constructor; Modular subtraction operator.
- `bvmul` — Constructor; Modular multiplication operator.
- `bvudiv` — Constructor; Total unsigned division operator.
- `bvurem` — Constructor; Total unsigned remainder operator.
- `bvsdiv` — Constructor; Total signed division operator.
- `bvsrem` — Constructor; Total signed remainder operator.
- `bvsmod` — Constructor; Total signed modulus operator.
- `bvand` — Constructor; Bitwise conjunction operator.
- `bvor` — Constructor; Bitwise disjunction operator.
- `bvxor` — Constructor; Bitwise exclusive-or operator.
- `bvshl` — Constructor; Logical left shift operator.
- `bvlshr` — Constructor; Logical right shift operator.
- `bvashr` — Constructor; Arithmetic right shift operator.
- `bvrotl` — Constructor; Left rotation operator.
- `bvrotr` — Constructor; Right rotation operator.
- `bveq` — Constructor; Equality comparison operator.
- `bvne` — Constructor; Inequality comparison operator.
- `bvult` — Constructor; Unsigned less-than operator.
- `bvule` — Constructor; Unsigned less-than-or-equal operator.
- `bvslt` — Constructor; Signed less-than operator.
- `bvsle` — Constructor; Signed less-than-or-equal operator.
- `bvite` — Constructor; Conditional selection operator.
- `bvzext` — Constructor; Zero-extension operator.
- `bvsext` — Constructor; Sign-extension operator.
- `bvtrunc` — Constructor; Truncate to a target width.
- `bvextract` — Constructor; Extract a contiguous range of bits.
- `bvconcat` — Constructor; Concatenate high and low operands.

### `BitsExpr.v` — BIT-1

- `Bits.expr` — Inductive; Bit-vector expression syntax.
- `Bits.eval_args` — Definition; Evaluate an expression list.
- `Bits.eval` — Definition; Evaluate an expression.
- `Bits.env_of` — Definition; Build an environment from words.
- `Bits.vars` — Definition; Build a list of variables.
- `eval_var` — Theorem; The evaluator, by cases on the expression.
- `eval_const` — Theorem; States `eval env (Const w z) = Some (w, wrap w z)`.
- `eval_app` — Theorem; The evaluator, by cases on the expression.
- `eval_args_nil` — Theorem; States `eval_args env nil = Some nil`.
- `eval_args_cons` — Theorem; The evaluator, by cases on the expression.
- `eval_is_word` — Theorem; States `eval env e = Some r -> is_word (fst r) (snd r)`.
- `Bits.Var` — Constructor; Read a variable by index.
- `Bits.Const` — Constructor; Literal word with a width and integer value.
- `Bits.App` — Constructor; Apply an operator to argument expressions.

### `BitsBridge.v` — BIT-1

- `bridge_op` — Definition; Relate client operator results to word operators.
- `bridge_expr` — Definition; Relate client operator results to word expressions.
- `bridge_op_expr` — Theorem;
  An operator-level bridge is an expression-level bridge through the variables 0, 1, ...

### `BitsTestbit.v` — BIT-1

- `testbit_wrap` — Theorem; The bits of a wrapped value, and equality of words by bits.
- `word_ext` — Theorem; The bits of a wrapped value, and equality of words by bits.
- `testbit_wand` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wor` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wxor` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wnot` — Theorem; The bitwise operators act bit by bit on words.
- `testbit_wshl` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `testbit_wlshr` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `testbit_washr` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `wshl_big` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `washr_big` — Theorem;
  Shifts, including amounts of at least w: 0, or the sign bit for the arithmetic shift.
- `wand_comm` — Theorem; States `wand w x y = wand w y x`.
- `wand_assoc` — Theorem; States `wand w x (wand w y z) = wand w (wand w x y) z`.
- `wor_comm` — Theorem; States `wor w x y = wor w y x`.
- `wor_assoc` — Theorem; States `wor w x (wor w y z) = wor w (wor w x y) z`.
- `wxor_comm` — Theorem; States `wxor w x y = wxor w y x`.
- `wxor_assoc` — Theorem; States `wxor w x (wxor w y z) = wxor w (wxor w x y) z`.
- `wxor_self` — Theorem; States `wxor w x x = 0`.
- `wand_idem` — Theorem; States `is_word w x -> wand w x x = x`.
- `wnot_involutive` — Theorem; States `is_word w x -> wnot w (wnot w x) = x`.
- `wnot_wand` — Theorem; States `wnot w (wand w x y) = wor w (wnot w x) (wnot w y)`.
- `wnot_wor` — Theorem; States `wnot w (wor w x y) = wand w (wnot w x) (wnot w y)`.
- `wand_wnot` — Theorem; States `wand w x (wnot w x) = 0`.
- `wadd_comm` — Theorem; States `wadd w x y = wadd w y x`.
- `wadd_assoc` — Theorem; States `wadd w x (wadd w y z) = wadd w (wadd w x y) z`.
- `wadd_0_r` — Theorem; States `is_word w x -> wadd w x 0 = x`.
- `wneg_wnot` — Theorem; States `wneg w x = wadd w (wnot w x) 1`.
- `wadd_wneg` — Theorem; States `wadd w x (wneg w x) = 0`.
- `wsub_wneg` — Theorem; States `wsub w x y = wadd w x (wneg w y)`.
- `wmul_comm` — Theorem; States `wmul w x y = wmul w y x`.
- `wmul_assoc` — Theorem; States `wmul w x (wmul w y z) = wmul w (wmul w x y) z`.
- `wmul_1_r` — Theorem; States `is_word w x -> wmul w x 1 = x`.
- `wmul_wadd_distr` — Theorem; Modular arithmetic identities.
- `wshl_0` — Theorem; States `is_word w x -> wshl w x 0 = x`.

### `BitsSigned.v` — BIT-2

- `signed_range` — Theorem; States `- half w <= signed w x < half w`.
- `signed_id` — Theorem; States `- half w <= z < half w -> signed w z = z`.
- `wrap_signed` — Theorem; States `wrap w (signed w x) = wrap w x`.
- `signed_wrap` — Theorem; States `signed w (wrap w x) = signed w x`.
- `signed_inj` — Theorem; States `signed w x = signed w y -> wrap w x = wrap w y`.
- `signed_neg_iff_msb` — Theorem; States `signed w x < 0 <-> msb w x = true`.
- `wadd_signed` — Theorem; States `wadd w x y = wrap w (signed w x + signed w y)`.
- `wsub_signed` — Theorem; States `wsub w x y = wrap w (signed w x - signed w y)`.
- `wslt_bias` — Theorem; Addition and comparison through the signed view.
- `wslt_wult` — Theorem; States `msb w x = msb w y -> wslt w x y = wult w x y`.
- `wsdiv_signed` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsrem_signed` — Theorem; States `wsrem w x y = wrap w (Z.rem (signed w x) (signed w y))`.
- `wsmod_signed` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsdiv_zero` — Theorem; States `wsdiv w x 0 = if msb w x then 1 else modulus w - 1`.
- `wsdiv_wsrem_euclid` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.
- `wsmod_sign` — Theorem;
  Signed division and remainders equal the mathematical ones on the signed views, with SMT-LIB's
  totality: remainder and modulus by zero give the dividend.

### `BitsArith.v` — BIT-2

- `wudiv_zero` — Theorem; States `wudiv w x 0 = modulus w - 1`.
- `wurem_zero` — Theorem; States `wurem w x 0 = wrap w x`.
- `wudiv_spec` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wurem_spec` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wurem_lt` — Theorem; States `is_word w x -> is_word w y -> y <> 0 -> wurem w x y < y`.
- `wudiv_wurem_euclid` — Theorem; Unsigned division and remainder, and SMT-LIB's totality at zero.
- `wmul_signed` — Theorem; States `wmul w x y = wrap w (signed w x * signed w y)`.
- `wmul_wshl` — Theorem; Multiplication and powers of two.
- `wudiv_wlshr` — Theorem; Multiplication and powers of two.
- `wurem_mask` — Theorem; Multiplication and powers of two.
- `testbit_wrotl` — Theorem; Rotations move bits cyclically, by the amount modulo the width.
- `wrotl_mod` — Theorem; States `wrotl w x y = wrotl w x (wrap w y mod Zpos w)`.
- `wrotr_wrotl` — Theorem; States `wrotr w (wrotl w x y) y = wrap w x`.
- `wclz_zero` — Theorem; States `wclz w 0 = Zpos w`.
- `wctz_zero` — Theorem; States `wctz w 0 = Zpos w`.
- `wclz_spec` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.
- `wclz_range` — Theorem; States `0 <= wclz w x <= Zpos w`.
- `wctz_spec` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.
- `wpopcnt_range` — Theorem; States `0 <= wpopcnt w x <= Zpos w`.
- `wpopcnt_wnot` — Theorem;
  Leading zeros, trailing zeros and population count; all three give w or 0..w on zero.

### `BitsExtend.v` — BIT-2

- `zext_value` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `sext_value` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `sext_signed` — Theorem; Zero extension keeps the value; sign extension keeps the signed view.
- `trunc_zext` — Theorem; Truncation undoes extension and commutes with addition.
- `trunc_sext` — Theorem; Truncation undoes extension and commutes with addition.
- `trunc_wadd` — Theorem; Truncation undoes extension and commutes with addition.
- `extract_concat_hi` — Theorem;
  Concatenation puts the first operand high; extract and truncation recover the parts.
- `trunc_concat_lo` — Theorem;
  Concatenation puts the first operand high; extract and truncation recover the parts.

## Domains

### `DomainsNumeric.v` — DOM-1a

- `numeric_domain` — Record; Lattice and sound abstract word operations.
- `numeric_laws` — Record; Lattice, concretisation and numeric transfer laws.
- `abs_eval` — Definition; Evaluate an expression abstractly.
- `abs_assume` — Definition; Refine an environment from an expression result.
- `env_ok` — Definition; Require every environment word to be in range.
- `env_sound` — Definition; Relate abstract and concrete environments.
- `word_domain` — Record; Width-indexed payload lattice and operations.
- `payload_sound` — Definition; Relate a width-tagged payload to a concrete word.
- `word_laws` — Record; Soundness and refinement laws for payload operations.
- `tagged` — Inductive; Empty, width-tagged or unrestricted payload.
- `tagged_lattice` — Definition; Lattice for tagged.
- `tagged_val` — Definition; Build a tagged value, collapsing empty payloads.
- `tagged_domain` — Definition; Payload domain for tagged.
- `tagged_gamma` — Definition; Concretisation for tagged.
- `width_ok` — Definition; Limit a tagged value to a maximum width.
- `capped` — Definition; Tagged values bounded by a maximum width.
- `capped_lattice` — Definition; Lattice for capped.
- `capped_height` — Definition; Finite height for capped.
- `capped_wrank` — Definition; Widening rank for capped.
- `clamp` — Definition; Replace an out-of-cap tagged value by top.
- `capped_domain` — Definition; Payload domain for capped.
- `capped_gamma` — Definition; Concretisation for capped.
- `abs_eval_var` — Theorem; States `abs_eval D env (Var i) = env i`.
- `abs_eval_const` — Theorem; States `abs_eval D env (Const w z) = of_const D w z`.
- `abs_eval_app` — Theorem; The abstract evaluator follows the expression's structure.
- `abs_eval_sound` — Theorem;
  One generic soundness theorem: abstract evaluation over-approximates concrete evaluation.
- `abs_assume_sound` — Theorem;
  A guard keeps the environment sound, and refinement only goes down.
- `abs_assume_refines` — Theorem;
  A guard keeps the environment sound, and refinement only goes down.
- `tagged_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `capped_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `tagged_numeric_laws` — Theorem;
  The tagged lattice is a lattice, and a payload domain lifts to a numeric domain.
- `clamp_gamma` — Theorem;
  Clamping to the cap only widens, and the capped domain is a sound numeric domain.
- `capped_numeric_laws` — Theorem;
  Clamping to the cap only widens, and the capped domain is a sound numeric domain.
- `NumericDomain` — Constructor; Construct a numeric domain from its lattice and transfers.
- `WordDomain` — Constructor; Construct a width-indexed payload domain.
- `lat` — Field; Numeric lattice, constructors or transfers.
- `top_at` — Field; Numeric lattice, constructors or transfers.
- `of_const` — Field; Numeric lattice, constructors or transfers.
- `forward` — Field; Numeric lattice, constructors or transfers.
- `assume` — Field; Numeric lattice, constructors or transfers.
- `meet` — Field; Numeric lattice, constructors or transfers.
- `lat_laws` — Field; Numeric domain law.
- `gamma_laws` — Field; Numeric domain law.
- `bot_empty` — Field; Numeric domain law.
- `top_at_sound` — Field; Numeric domain law.
- `of_const_sound` — Field; Numeric domain law.
- `forward_sound` — Field; Numeric domain law.
- `assume_sound` — Field; Numeric domain law.
- `assume_length` — Field; Numeric domain law.
- `assume_refines` — Field; Numeric domain law.
- `meet_sound` — Field; Numeric domain law.
- `meet_lower_left` — Field; Numeric domain law.
- `plat` — Field; Width-indexed payload operation.
- `ptop` — Field; Width-indexed payload operation.
- `pconst` — Field; Width-indexed payload operation.
- `pforward` — Field; Width-indexed payload operation.
- `passume` — Field; Width-indexed payload operation.
- `pmeet` — Field; Width-indexed payload operation.
- `plat_laws` — Field; Payload domain law.
- `pgamma_monotone` — Field; Payload domain law.
- `pgamma_bot_empty` — Field; Payload domain law.
- `ptop_sound` — Field; Payload domain law.
- `pconst_sound` — Field; Payload domain law.
- `pforward_sound` — Field; Payload domain law.
- `passume_sound` — Field; Payload domain law.
- `passume_refines` — Field; Payload domain law.
- `pmeet_sound` — Field; Payload domain law.
- `pmeet_lower_left` — Field; Payload domain law.
- `TBot` — Constructor; Tagged empty value.
- `TVal` — Constructor; Payload tagged with its word width.
- `TAny` — Constructor; Unrestricted word value.

### `DomainsConst.v` — DOM-1a

- `const_domain` — Definition; Payload domain for const.
- `const_gamma` — Definition; Concretisation for const.
- `const_word_laws` — Theorem; States `word_laws const_domain const_gamma`.

### `DomainsInterval.v` — DOM-1b

- `bound` — Inductive; Infinite or finite interval endpoint.

- `interval` — Inductive; Empty interval or pair of bounds.
- `interval_lattice` — Definition; Lattice for interval.
- `interval_gamma` — Definition; Concretisation for interval.
- `interval_wrank` — Definition; Widening rank for interval.
- `interval_pgamma` — Definition; Payload meaning for interval.
- `interval_domain` — Definition; Payload domain for interval.
- `interval_laws` — Theorem; States `lattice_laws (interval_lattice thresholds)`.
- `interval_lub` — Theorem; States `lub_laws (interval_lattice thresholds)`.
- `interval_gamma_laws` — Theorem;
  Intervals: a lattice with least upper bounds, monotone meaning, sound transfers.
- `interval_gamma_bot_empty` — Theorem;
  Intervals: a lattice with least upper bounds, monotone meaning, sound transfers.
- `interval_word_laws` — Theorem; States `word_laws (interval_domain thresholds) interval_pgamma`.
- `NegInf` — Constructor; Negative infinity interval bound.
- `Fin` — Constructor; Finite integer interval bound.
- `PosInf` — Constructor; Positive infinity interval bound.
- `IBot` — Constructor; Empty integer interval.
- `Itv` — Constructor; Interval with lower and upper bounds.

### `DomainsSign.v` — DOM-1a

- `sign` — Record; Set of possible signed signs.

- `sign_lattice` — Definition; Lattice for sign.
- `sign_height` — Definition; Finite height for sign.
- `sign_gamma` — Definition; Concretisation for sign.
- `sign_domain` — Definition; Payload domain for sign.
- `sign_laws` — Theorem; States `lattice_laws sign_lattice`.
- `sign_lub` — Theorem; States `lub_laws sign_lattice`.
- `sign_word_laws` — Theorem; States `word_laws sign_domain sign_gamma`.
- `Sign` — Constructor; Sign record constructor.
- `neg` — Field; Sign membership flag.
- `zero` — Field; Sign membership flag.
- `pos` — Field; Sign membership flag.

### `DomainsKnownBits.v` — DOM-2

- `tnum` — Record; Known-zero and known-one bit masks.
- `tnum_lattice` — Definition; Lattice for tnum.
- `tnum_height` — Definition; Finite height for tnum.
- `tnum_gamma` — Definition; Concretisation for tnum.
- `known_bits_domain` — Definition; Payload domain for known bits.
- `tnum_laws` — Theorem; States `lattice_laws (tnum_lattice w)`.
- `tnum_lub` — Theorem; States `lub_laws (tnum_lattice w)`.
- `known_bits_word_laws` — Theorem; States `word_laws known_bits_domain tnum_gamma`.
- `Tnum` — Constructor; Known-bits record constructor.
- `zeros` — Field; Known zero or one bit mask.
- `ones` — Field; Known zero or one bit mask.

### `DomainsWrapped.v` — DOM-3

- `wrapped_laws` — Theorem; States `lattice_laws (wrapped_lattice w)`.

- `wrapped` — Inductive; Empty, full or circular word interval.
- `wrapped_size` — Definition; Count the words in a circular interval.
- `wrapped_lattice` — Definition; Lattice for wrapped.
- `wrapped_wrank` — Definition; Widening rank for wrapped.
- `wrapped_gamma` — Definition; Concretisation for wrapped.
- `wrapped_domain` — Definition; Payload domain for wrapped.
- `wrapped_join_minimal` — Theorem;
  Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
  arcs; there is no least upper bound in general, so there is no lub_laws theorem.
- `wrapped_gamma_laws` — Theorem;
  Wrapping intervals (DOM-3): the join above is an upper bound of minimal size among the covering
  arcs; there is no least upper bound in general, so there is no lub_laws theorem.
- `wrapped_word_laws` — Theorem; States `word_laws wrapped_domain wrapped_gamma`.
- `WBot` — Constructor; Empty circular interval.
- `WFull` — Constructor; Full circular interval.
- `WItv` — Constructor; Circular interval with two endpoints.

### `DomainsCongruence.v` — DOM-4

- `cong_laws` — Theorem; States `lattice_laws (cong_lattice w)`.

- `cong` — Inductive; Empty or modular congruence value.
- `cong_norm` — Definition; Normalise a congruence to the word width.
- `cong_lattice` — Definition; Lattice for cong.
- `cong_height` — Definition; Finite height for cong.
- `cong_gamma` — Definition; Concretisation for cong.
- `cong_domain` — Definition; Payload domain for cong.
- `cong_lub` — Theorem; States `lub_laws (cong_lattice w)`.
- `cong_word_laws` — Theorem; States `word_laws cong_domain cong_gamma`.
- `CBot` — Constructor; Empty congruence.
- `Cong` — Constructor; Congruence with modulus and residue.

### `DomainsProduct.v` — DOM-4

- `product_word_domain` — Definition; Build a reduced product of payload domains.
- `product_pgamma` — Definition; Intersect the meanings of two payloads on words.
- `payload_concretisation` — Definition; Expose a payload meaning as a concretisation.
- `word_payload_concretisation` — Definition; Restrict a payload meaning to words at its width.
- `product_tagged_gamma_equiv` — Theorem; Tagged product meaning is unchanged by the word restriction.
- `reduction_empty` — Definition; Require reduction to collapse empty components.
- `reduce_bits_wrapped` — Definition; Exchange known-bit and circular-interval information.
- `reduce_interval_cong` — Definition; Exchange interval and congruence information.
- `reduce_const_with` — Definition; Exchange constant information with a payload.
- `const_reduction_laws` — Record; Exact-query and meet obligations for constant reduction.
- `const_exact_sound`, `const_exact_monotone`, `const_meet_monotone`,
  `const_meet_idempotent`, `const_meet_exact_fixed`, `const_meet_mismatch` — Fields;
  Constructive obligations for the constant reduction.
- `bits_wrapped_domain` — Definition; Reduced product of known bits and circular intervals.
- `interval_cong_domain` — Definition; Reduced product of intervals and congruences.
- `const_product_domain` — Definition; Reduced product of constants with a payload.
- `product_word_laws` — Theorem;
  A product of two sound payload domains with a sound, monotone, idempotent reduction is sound.
- `reduce_bits_wrapped_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `reduce_interval_cong_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `reduce_const_with_laws` — Theorem;
  The three reductions only go down, are monotone and idempotent, keep the meaning, and send a pair
  with an empty component to the bottom pair.
- `bits_wrapped_numeric_laws` — Theorem; The three named products are sound numeric domains.
- `interval_cong_numeric_laws` — Theorem; The three named products are sound numeric domains.

### `DomainsDemanded.v` — DOM-5

- `mask_lattice` — Definition; Lattice for mask.
- `mask_height` — Definition; Finite height for mask.
- `mask_agreement` — Definition; Word agreement on selected bits.
- `demand` — Definition; Compute operand masks from a demanded result mask.
- `agree_masks` — Definition; Relate operand lists under their demanded masks.
- `consts_hold` — Definition; Check known constants against operand words.
- `masks_leb` — Definition; Pointwise inclusion of width-indexed masks.
- `mask_laws` — Theorem; States `lattice_laws (mask_lattice w)`.
- `mask_lub` — Theorem; States `lub_laws (mask_lattice w)`.
- `mask_agreement_laws` — Theorem; States `agreement_laws (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_bot` — Theorem; States `agreement_bot (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_join` — Theorem;
  States `agreement_join_law (mask_lattice w) (mask_agreement w)`.
- `mask_agreement_equivalence` — Theorem; States `agreement_equivalence (mask_agreement w)`.
- `demand_sound` — Theorem;
  Soundness: operands of equal widths that agree under the demanded masks, and whose known
  constants are right, give results that agree under the output mask.
- `demand_zero` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.
- `demand_length` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.
- `demand_monotone` — Theorem;
  Demanding nothing demands nothing, the masks have the arity's length, and demand is monotone.

### `DomainsAddress.v` — DOM-6

- `address` — Record; Site, offset and size of an abstract access.
- `access` — Definition; Concrete object, byte offset and size.
- `bytes_of` — Definition; Membership of a byte in a concrete access.
- `address_gamma` — Definition; Concretisation for address.
- `covers` — Definition; Prove one abstract access covers another.
- `disjoint` — Definition; Prove two abstract accesses disjoint.
- `may_overlap` — Definition; Conservative overlap query for abstract accesses.
- `covers_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `disjoint_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `may_overlap_sound` — Theorem;
  Each predicate is sound for every pair of concrete accesses the addresses describe.
- `covers_exact` — Theorem;
  The predicates are not trivially false: an exact address covers itself, and objects at different
  known sites are disjoint.
- `disjoint_sites` — Theorem;
  The predicates are not trivially false: an exact address covers itself, and objects at different
  known sites are disjoint.
- `Address` — Constructor; Address record constructor.
- `site` — Field; Address site, offset or size.
- `offset` — Field; Address site, offset or size.
- `size` — Field; Address site, offset or size.

### `DomainsPointsTo.v` — DOM-6

- `points_to` — Definition; Possible sites and an unknown-object flag.
- `points_to_laws` — Theorem; States `lattice_laws points_to_lattice`.

- `points_to_lattice` — Definition; Lattice for points to.
- `points_to_gamma` — Definition; Concretisation for points to.
- `pts_of_site` — Definition; Singleton points-to fact.
- `pts_unknown` — Definition; Points-to fact for an unknown object.
- `pts_may_alias` — Definition; Conservative alias query on points-to facts.
- `pts_must_alias` — Definition; Prove two points-to facts have one common object.
- `points_to_lub` — Theorem; States `lub_laws points_to_lattice`.
- `points_to_gamma_laws` — Theorem;
  States `concretisation_laws points_to_lattice points_to_gamma`.
- `pts_may_alias_sound` — Theorem;
  Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries.
- `pts_must_alias_sound` — Theorem;
  Points-to sets: a lattice with least upper bounds, a monotone meaning, sound alias queries.
- `pts_of_site_gamma` — Theorem; States `gamma points_to_gamma (pts_of_site s) p <-> p = s`.

### `DomainsByteRange.v` — DOM-6

- `range` — Definition; Half-open integer byte range.

- `ranges_wf` — Definition; Sorted, nonempty and nonadjacent range invariant.
- `byte_ranges` — Definition; Canonical list of byte ranges.
- `ranges_empty` — Definition; Empty canonical range set.
- `ranges_mem` — Definition; Test byte membership in a range set.
- `ranges_add` — Definition; Add a byte range to a range set.
- `ranges_remove` — Definition; Remove a byte range from a range set.
- `ranges_union` — Definition; Union two range sets.
- `ranges_inter` — Definition; Intersect two range sets.
- `ranges_diff` — Definition; Subtract one range set from another.
- `ranges_covers` — Definition; Test whether a range set covers a range.
- `ranges_intersects` — Definition; Test whether a range set intersects a range.
- `ranges_lattice` — Definition; Lattice for ranges.
- `ranges_gamma` — Definition; Concretisation for ranges.
- `ranges_mem_empty` — Theorem; States `ranges_mem ranges_empty b = false`.
- `ranges_mem_add` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_remove` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_union` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_inter` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_mem_diff` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_ext` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_covers_spec` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_intersects_spec` — Theorem;
  Membership laws; a byte-range set is determined by its bytes, so equality is extensional.
- `ranges_laws` — Theorem; States `lattice_laws ranges_lattice`.
- `ranges_lub` — Theorem; States `lub_laws ranges_lattice`.
- `ranges_gamma_laws` — Theorem; States `concretisation_laws ranges_lattice ranges_gamma`.

### `DomainsFootprint.v` — DOM-6

- `footprint` — Record; Site and half-open byte bounds.

- `covered` — Definition; Bytewise coverage of an access by footprints.
- `written` — Definition; Byte membership in a footprint list.
- `footprint_encoding` — Definition; Injectively encode a site and its byte bounds.
- `footprints_canonical` — Definition; Require sorted, nonempty and nonadjacent footprints.
- `site_ranges` — Definition; Extract one site's byte ranges.
- `footprints_normalise` — Definition; Canonicalise a footprint list.
- `footprints_inter` — Definition; Intersect footprint lists by site and byte.
- `footprints_diff` — Definition; Subtract footprint bytes by site.
- `canonical_footprints` — Definition; Footprint lists paired with their canonicality proof.
- `range_must` — Definition; Unreachable or canonical must-written footprints.
- `range_reached` — Definition; Normalise footprints into a reached must fact.
- `range_written` — Definition; Byte membership in a must fact.
- `range_must_lattice` — Definition; Lattice for range must.
- `range_must_top` — Definition; Must fact with no known written bytes.
- `range_add` — Definition; Add written bytes to a must fact.
- `range_remove` — Definition; Forget overwritten bytes from a must fact.
- `range_covers` — Definition; Bytewise must coverage of an access.
- `range_must_gamma` — Definition; Concretisation for range must.
- `footprints_normalise_canonical` — Theorem;
  States `footprints_canonical ET (footprints_normalise ET F)`.
- `footprints_normalise_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_inter_canonical` — Theorem;
  States `footprints_canonical ET (footprints_inter ET F G)`.
- `footprints_inter_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_diff_canonical` — Theorem;
  States `footprints_canonical ET (footprints_diff ET F G)`.
- `footprints_diff_written` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_ext` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `footprints_canonical_ranges` — Theorem;
  Normalising keeps the bytes and yields a canonical list; a canonical list is a function of its
  bytes; its per-site ranges are byte_ranges.
- `covered_written` — Theorem;
  covered is exactly bytewise coverage, including empty accesses and noncanonical lists.
- `covered_bytewise` — Theorem;
  covered is exactly bytewise coverage, including empty accesses and noncanonical lists.
- `range_must_laws` — Theorem; States `lattice_laws (range_must_lattice ET)`.
- `range_must_lub` — Theorem; States `lub_laws (range_must_lattice ET)`.
- `range_must_leb_spec` — Theorem;
  The must lattice of ranges: a lattice with least upper bounds, ordered by bytes.
- `range_reached_written` — Theorem;
  The must lattice of ranges: a lattice with least upper bounds, ordered by bytes.
- `range_must_gamma_laws` — Theorem;
  Meaning: Unreached has no concrete states; Reached F means every footprint byte is written.
- `range_must_gamma_bot_empty` — Theorem;
  States `bottom_empty (range_must_lattice ET) range_must_gamma`.
- `range_must_gamma_top_full` — Theorem; States `top_full (range_must_top ET) range_must_gamma`.
- `range_covers_sound` — Theorem;
  Meaning: Unreached has no concrete states; Reached F means every footprint byte is written.
- `range_covers_iff_written` — Theorem;
  range_covers is exactly bytewise coverage, including an access of zero bytes.
- `range_covers_add` — Theorem;
  Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
  overlapped bytes away and keeps the others.
- `range_covers_remove` — Theorem;
  Coverage lemmas: adding makes the added bytes covered and keeps the old ones; removing takes the
  overlapped bytes away and keeps the others.
- `range_add_gamma` — Theorem;
  The operations are sound for the meaning: added bytes that are written stay written, and bytes
  outside fs keep their status when fs may have been overwritten.
- `range_remove_gamma` — Theorem;
  The operations are sound for the meaning: added bytes that are written stay written, and bytes
  outside fs keep their status when fs may have been overwritten.
- `footprint_encoding_spec` — Theorem;
  footprint_encoding is the encoding of the triple of site code and bounds, by construction.
- `Footprint` — Constructor; Footprint record constructor.
- `fp_site` — Field; Footprint site or byte bound.
- `fp_lo` — Field; Footprint site or byte bound.
- `fp_hi` — Field; Footprint site or byte bound.

### `DomainsEquality.v` — DOM-7

- `partition` — Definition; Unreachable or a well-formed equality partition.
- `partition_equiv` — Definition; Equality relation represented by a partition.
- `partition_lattice` — Definition; Lattice for partition.
- `partition_top` — Definition; Partition that knows no nontrivial equalities.
- `partition_union` — Definition; Add an equality to a partition.
- `partition_forget` — Definition; Forget all nontrivial equalities of a key.
- `key_update` — Definition; Update a keyed valuation at one key.
- `partition_test` — Definition; Test equality and return the compressed partition.
- `partition_gamma` — Definition; Concretisation for partition.
- `partition_laws` — Theorem; States `lattice_laws (partition_lattice E)`.
- `partition_lub` — Theorem; States `lub_laws (partition_lattice E)`.
- `partition_join_spec` — Theorem;
  Partitions form a lattice with least upper bounds; the join is the intersection of equivalences.
- `partition_union_spec` — Theorem; Adding an equality merges exactly the two classes.
- `partition_forget_unreached` — Theorem; States `partition_forget E x Unreached = Unreached`.
- `partition_forget_spec` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_forget_leb` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_forget_gamma` — Theorem;
  Forgetting x: it leaves its class, the other equalities stay, and only equalities are lost. The
  specification needs p <> Unreached, whose equivalence relates every pair.
- `partition_test_correct` — Theorem;
  The test agrees with the relation and returns an equivalent partition.
- `partition_gamma_laws` — Theorem;
  Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything.
- `partition_gamma_bot_empty` — Theorem;
  Meaning: equal keys hold equal values; the bottom denotes nothing; the top everything.
- `partition_top_full` — Theorem; States `top_full (partition_top E) (@partition_gamma K V E)`.

### `DomainsSymbolic.v` — DOM-7

- `sym_key` — Definition; List of positive codes for a symbolic expression.

- `expr_key` — Definition; Encode an operator and its operand numbers.
- `numbering` — Record; Intern table and next available number.
- `numbering_empty` — Definition; Empty intern table with initial number.
- `intern` — Definition; Find or allocate a number for a symbolic key.
- `numbering_wf` — Definition; Bound and uniquely identify numbers in the table.
- `numbering_wf_empty` — Theorem; States `numbering_wf numbering_empty`.
- `numbering_wf_intern` — Theorem; States `numbering_wf n -> numbering_wf (snd (intern k n))`.
- `intern_get` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_found` — Theorem; States `Table.get k (ids n) = Some i -> intern k n = (i, n)`.
- `intern_fresh` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_stable` — Theorem;
  Interning: found keys keep their number, new keys get the next one, and the table only grows.
- `intern_injective` — Theorem;
  Numbers identify keys: two keys that get one number from a threaded numbering are equal.
- `expr_key_commutative` — Theorem;
  Keys respect commutativity, and equal keys denote equal values under any valuation.
- `expr_key_eval` — Theorem;
  Keys respect commutativity, and equal keys denote equal values under any valuation.
- `Numbering` — Constructor; Numbering record constructor.
- `ids` — Field; Interned IDs or next ID.
- `next` — Field; Interned IDs or next ID.

## Analyses

### `AnalysesLiveness.v` — ANA-1

- `fmem` — Definition; Tests membership in a finite set.
- `mentions` — Definition; Tests whether an encoded key occurs in a list.
- `var_view` — Record; Describes graph edges, variable uses and definitions.
- `VarView` — Constructor; Constructs the var view record.
- `gview` — Field; Graph view used by the variable analysis.
- `uses` — Field; Variables read by an edge.
- `defs` — Field; Variables written by an edge.
- `exit_uses` — Field; Variables observable at an exit.
- `vget` — Field; Reads a variable from a state.
- `var_view_laws` — Record; Relates variable uses and definitions to steps and exits.
- `view_laws` — Field; The underlying graph view satisfies its laws.
- `no_stays` — Field; The view has no point-preserving steps.
- `defs_frame` — Field; A step leaves variables outside its definitions unchanged.
- `uses_determine` — Field; Agreement on uses determines the edge step.
- `exits_determine` — Field; Agreement on exit uses determines the ending.
- `var_universe` — Definition; Finite universe of variables mentioned by the view.
- `live_set` — Definition; Finite live-variable fact.
- `live_lattice` — Definition; Lattice of finite live-variable facts.
- `live_agreement` — Definition; Agreement of states on all live variables.
- `liveness_transfer` — Definition; Adds edge uses and removes edge definitions.
- `liveness_system` — Definition; Backward constraints for liveness.
- `liveness_static` — Definition; Declared liveness dependencies.
- `solve_liveness` — Definition; Solves the liveness constraints.
- `reach_universe` — Definition; Finite universe of variable and defining-edge pairs.
- `reach_set` — Definition; Finite reaching-definition fact.
- `reach_lattice` — Definition; Lattice of reaching definitions.
- `reaching_transfer` — Definition; Indexed transfer equal to the reaching-definition reference.
- `reaching_system` — Definition; Indexed forward constraints equal to the reference observations.
- `zero_lattice` — Definition; Must lattice of variables zero since entry.
- `zero_since_entry_system` — Definition; Forward constraints for zero-since-entry facts.
- `copy_view` — Record; Describes variable copies along graph edges.
- `CopyView` — Constructor; Constructs the copy view record.
- `cvars` — Field; Variable view underlying the copy view.
- `copies` — Field; Copies performed by an edge.
- `equality_transfer` — Definition; Forgets written variables and joins copied variables.
- `equality_system` — Definition; Forward constraints for must equality.
- `live_agreement_laws` — Theorem; Live-variable agreement satisfies the agreement laws.
- `var_universe_covers` — Theorem; The variable universe covers view uses and definitions.
- `liveness_sound` — Theorem; Agreement on live variables preserves behaviour.
- `reaching_sound` — Theorem; The fact contains each last writer along a run prefix.
- `zero_since_entry_sound` — Theorem; Every variable in the fact still holds its entry zero.
- `equality_sound` — Theorem; Variables in the same partition class have equal values.

### `AnalysesAvailable.v` — ANA-1

- `genkill_view` — Record; Describes expressions generated and killed by each edge.
- `GenKillView` — Constructor; Constructs the gen kill view record.
- `gkview` — Field; Graph view underlying gen/kill information.
- `gen` — Field; Expressions generated by an edge.
- `kill` — Field; Expressions invalidated by an edge.
- `uval` — Field; Value of an expression in a state.
- `genkill_laws` — Record; Relates generated and killed expressions to execution.
- `gk_view` — Field; The underlying graph view satisfies its laws.
- `gk_no_stays` — Field; The graph view has no point-preserving steps.
- `gen_value` — Field; Generated expressions have their computed value.
- `kill_frame` — Field; Expressions outside the kill set retain their value.
- `final_exit` — Field; Final states occur at graph exits.
- `expr_universe` — Definition; Finite universe of expressions in the view.
- `avail_set` — Definition; Finite must-fact of expressions.
- `avail_lattice` — Definition; Reverse-inclusion lattice of expression facts.
- `avail_transfer` — Definition; Applies expression kills and generations to a fact.
- `available_system` — Definition; Forward constraints for available expressions.
- `busy_system` — Definition; Backward constraints for very busy expressions.
- `lcm_result` — Record; Insertion and deletion choices for lazy code motion.
- `LcmResult` — Constructor; Constructs the lcm result record.
- `insert` — Field; Expressions inserted on an edge.
- `delete` — Field; Expressions deleted at a node.
- `lcm_check` — Definition; Checks proposed code-motion insertions and deletions.
- `available_sound` — Theorem; An available expression has a current previously computed value.
- `busy_sound` — Theorem; A very busy expression is evaluated before invalidation.
- `lcm_insert_safe` — Theorem; An accepted insertion is anticipated.
- `lcm_delete_current` — Theorem; An accepted deletion has a current available value.

### `AnalysesStructured.v` — EX-4, ANA-2

EX-4 owns `skel_vars`, `skel_vars_laws`, their constructors and projections, and `act_vars`;
ANA-2 extends the file after EX-4 lands and owns the remaining declarations.

- `skel_vars` — Record; Variable uses and definitions of skeleton actions.
- `SkelVars` — Constructor; Constructs the skel vars record.
- `atom_uses` — Field; Variables read by a skeleton atom.
- `atom_defs` — Field; Variables written by a skeleton atom.
- `atom_trap_uses` — Field; Variables needed to determine an atom's trapping behaviour.
- `guard_uses` — Field; Variables read by a skeleton guard.
- `skel_vars_laws` — Record; Relates skeleton variable effects to client execution.
- `Build_skel_vars_laws` — Constructor; Constructs the skeleton variable laws record.
- `atom_frame` — Field; An atom changes only its declared definitions.
- `atom_agrees` — Field; Equal atom inputs yield matching steps.
- `guard_agrees` — Field; Equal guard inputs yield the same guard result.
- `trap_agrees` — Field; Equal trap inputs yield the same trap outcome.
- `jump_keeps` — Field; A jump preserves the relevant variable values.
- `act_vars` — Definition; Variables used or defined by a skeleton action.
- `skel_exit_uses` — Definition; Variables observable at a skeleton exit.
- `skel_universe` — Definition; Finite universe of variables in a skeleton.
- `skel_set` — Definition; Finite set of skeleton variables.
- `skel_lattice` — Definition; Lattice of skeleton variable sets.
- `skel_actb` — Definition; Backward transfer for a skeleton action.
- `structured_liveness_system` — Definition; Skeleton constraints for structured liveness.
- `certificate` — Definition; Facts stored at skeleton loop heads.
- `certificate_check` — Definition; Recomputes non-head facts and validates loop-head facts.
- `certificate_of` — Definition; Restricts a solution to its loop-head facts.
- `replay_live` — Definition; Replays live facts through an observer.
- `structured_liveness_sound` — Theorem; Structured live agreement preserves behaviour.
- `certificate_sound` — Theorem; An accepted loop certificate expands to a post-solution.
- `certificate_complete` — Theorem; A post-solution yields an accepted loop certificate.
- `replay_live_iff` — Theorem; Replay covers the expanded live facts.

### `AnalysesCensus.v` — ANA-2

- `region_table` — Definition; Computes a summary at every skeleton position.
- `region_table_agrees` — Theorem; Each table entry agrees with the recursive region summary.
- `census_atoms`, `occurrence_census` — static syntax traversal and encoded operand counts.
- `occurrence_census_exact` — Theorem; lookup agrees with the flattened static occurrence count.

### `AnalysesValues.v` — EX-5a and ANA-3

EX-5a owns the following bridge records, constructors and fields; ANA-3 uses these same
declarations after EX-5a lands.

- `op_bridge` — Record; Maps client operators and values to bit-vector expressions and words.
- `OpBridge` — Constructor; Constructs the op bridge record.
- `op_expr` — Field; Bit-vector expression for a client operator.
- `to_word` — Field; Maps a client value to a width and bit-vector word.
- `op_bridge_laws` — Record; The client operator bridge agrees with word evaluation and truth.
- `Build_op_bridge_laws` — Constructor; Constructs the operator bridge laws.
- `bridge_word` — Field; Mapped values satisfy the word-range condition.
- `bridge_eq` — Field; A defined client result matches the bit-vector evaluation.
- `bridge_truth` — Field; The client truth predicate agrees with the bit-vector result.

ANA-3 owns the remaining declarations in this file.

- `sparse_of_numeric` — Definition; Adapts a numeric domain to the sparse analysis interface.
- `numeric_problem` — Definition; Builds a sparse value problem from a numeric domain and bridge.
- `solve_values` — Definition; Solves a sparse value problem.
- `sparse_of_numeric_laws` — Theorem; The numeric adapter satisfies the sparse-domain laws.
- `numeric_value_sound` — Theorem; Reachable values belong to their computed numeric facts.

### `AnalysesPaths.v` — ANA-3

- `path_domain` — Definition; Bounded disjunction domain for path facts.
- `guard_chain` — Definition; Dominating guarded edges relevant to a use.
- `path_domain_laws` — Theorem; The bounded path domain satisfies the sparse-domain laws.
- `guard_chain_holds` — Theorem; Each dominating guard in the chain holds at the use.

### `AnalysesDemand.v` — ANA-4

- `demand_domain` — Record; Lattice and agreement for backward value demands.
- `DemandDomain` — Constructor; Constructs the demand domain record.
- `dlat` — Field; Lattice of demand facts.
- `dagree` — Field; Agreement relation associated with a demand.
- `demand_view` — Record; Uses, definitions and backward demand transfer for graph edges.
- `DemandView` — Constructor; Constructs the demand view record.
- `dgraph` — Field; Graph view underlying the demand analysis.
- `ddefs` — Field; Variables defined by each edge.
- `dnec` — Field; Demands required by an edge's observable effects.
- `dback` — Field; Backward operand demands for a demanded definition.
- `dexit` — Field; Demands observable at an exit.
- `dlookup` — Field; Reads the value of a variable from a state.
- `dvars` — Field; Finite variable universe of demand facts.
- `demand_lattice` — Definition; Pointwise lattice of per-variable demands.
- `dget` — Definition; Reads a variable demand with a bottom default.
- `demand_agreement` — Definition; State agreement induced by per-variable demands.
- `demand_transfer` — Definition; Propagates output demands backward across an edge.
- `exit_map` — Definition; Builds the map of demands observable at an exit.
- `demand_system` — Definition; Backward constraints for demanded values.
- `demand_vars_ok` — Definition; All demands refer to the declared finite variable universe.
- `demand_laws` — Record; Relates backward demand propagation to steps and endings.
- `d_view` — Field; The demand graph view satisfies its laws.
- `d_no_stays` — Field; The demand graph has no point-preserving steps.
- `d_frame` — Field; An edge leaves variables outside its definitions unchanged.
- `d_agreement` — Field; The demand relation satisfies agreement laws.
- `d_bot_agrees` — Field; Bottom demand relates any two values.
- `d_back_bot` — Field; Bottom output demand propagates no operand demands.
- `d_vars` — Field; Demanded variables lie in the finite universe.
- `d_step` — Field; Demand agreement is preserved across matching steps.
- `d_exits` — Field; Demand agreement preserves observable endings.
- `trap_policy` — Inductive; Choices for preserving or dropping unread traps.
- `KeepTraps` — Constructor; Preserves trap behaviour during dead-code erasure.
- `DropUnreadTraps` — Constructor; Allows unread traps under the refinement conclusion.
- `effectful` — Definition; Tests whether an instruction must be retained under the trap policy.
- `demand_closed` — Definition; A demand closed under the backward transfer and exit seeds.
- `closed_system` — Definition; Single-unknown constraint system for demand closure.
- `bool_demand` — Definition; Boolean demand domain for neededness.
- `needed_values` — Definition; Closed Boolean demand, least under its stated strictness premise.
- `dead_value` — Definition; Tests whether a value is absent from the needed demand.
- `observable_bits_view` — Definition; Specialises demand propagation to observable bit masks.
- `erasure` — Record; Relates an original graph to an erased program.
- `Erasure` — Constructor; Constructs the erasure record.
- `er_demand` — Field; Demand view used by the erasure.
- `er_graph` — Field; Graph view of the transformed program.
- `er_erased` — Field; Identifies edges whose instruction is erased.
- `er_instr` — Field; Instruction associated with each edge.
- `er_inv` — Definition; Original-state invariant under the selected trap policy.
- `er_agree` — Definition; Agreement relation between original and transformed states.
- `erasure_laws` — Record; Matching-step and ending laws for an erasure.
- `er_cfg` — Field; The two programs have the same control-flow graph.
- `er_view` — Field; The transformed graph view satisfies its laws.
- `er_no_stays` — Field; The transformed view has no point-preserving steps.
- `er_kept_forth` — Field; A retained instruction matches an original step forward.
- `er_kept_back` — Field; A retained instruction matches a transformed step backward.
- `er_nop_forth` — Field; An erased instruction matches a transformed no-op forward.
- `er_nop_back` — Field; An erased instruction matches an original step backward.
- `er_ends` — Field; Related states have compatible observable endings.
- `never_traps` — Definition; The original run from a state never traps.
- `dce_conclusion` — Definition; Behavioural claim selected by the trap policy.
- `demand_sound` — Theorem; Agreement on demanded parts preserves behaviour.
- `closed_demand_sound` — Theorem; A closed demand gives behavioural agreement at reachable states.
- `dead_value_removable` — Theorem; States differing only in a dead value have the same behaviour.
- `closed_system_iff` — Theorem; The single-unknown system encodes demand closure.
- `needed_values_closed` — Theorem; Computed needed values are closed under demand dependencies.
- `needed_values_least` — Theorem; Computed needed values are below every closed demand.
- `non_effectful_step_pure` — Theorem; A non-effectful step is silent and preserves state.
- `dce_sound` — Theorem; Erasure satisfies the conclusion of the selected trap policy.

### `AnalysesAdce.v` — ANA-4

- `adce_input` — Record; Graph and effect information for aggressive dead-code marking.
- `AdceInput` — Constructor; Constructs the adce input record.
- `agraph` — Field; Control-flow graph for aggressive dead-code marking.
- `aexits` — Field; Exit nodes used for control dependence.
- `effectful_node` — Field; Marks a node with an observable effect.
- `may_not_terminate` — Field; Marks a node whose loop may diverge.
- `adce_marked` — Definition; Node-supported marking, least and closed under its stated premises.
- `skips_to` — Definition; An unmarked path reaches a marked node without earlier marked nodes.
- `adce_closed` — Theorem; Marked nodes have node support and satisfy scoped closure rules.
- `adce_least` — Theorem; Marked nodes are least under the scoped marking rules.
- `adce_skip_unique` — Theorem; Unmarked paths have a unique first marked successor.

### `AnalysesNumbering.v` — ANA-5

- `numbering_problem` — Record; SSA data and purity information for value numbering.
- `NumberingProblem` — Constructor; Constructs the numbering problem record.
- `nsv` — Field; SSA view used by value numbering.
- `pure` — Field; Identifies pure operations eligible for numbering.
- `nvalues` — Field; Enumerates values considered by numbering.
- `dominator_numbering` — Definition; Computes scoped value numbers along the dominator tree.
- `optimistic_numbering` — Definition; Refines a partition to compute optimistic value numbers.
- `numbering_check` — Definition; Checks a proposed value numbering.
- `numbering_observation` — Record; States, ready values, ranks and shared predecessor contexts.
- `NumberingObservation` — Constructor; Constructs an observation dictionary.
- `observation_state`, `observation_ready`, `observation_rank`, `observation_previous` — Fields;
  Relate observations, readiness, ranks and shared predecessor contexts.
- `numbering_observation_laws` — Record; Local operation and historical parameter equations.
- `NumberingObservationLaws` — Constructor; Constructs the local observation laws.
- `observed_op`, `observed_param` — Fields; Operation and shared incoming-parameter evidence.
- `numbering_loop_laws` — Record; Pure-operation binding behavior for loop soundness.
- `NumberingLoopLaws` — Constructor; Constructs the loop binding laws.
- `loop_op_binding` — Field; A changed pure operation binds a computed result.
- `loop_info` — Record; Header and membership predicate for a loop.
- `LoopInfo` — Constructor; Constructs the loop info record.
- `header` — Field; Header of a loop.
- `body` — Field; Membership in a loop body.
- `loop_info_wf` — Record; Well-formedness conditions for loop membership and header.
- `header_in_body` — Field; The loop header belongs to its body.
- `header_dominates` — Field; The loop header dominates every body node.
- `single_entry` — Field; Every entry into the loop body passes through its header.
- `invariant_in` — Definition; Inductive loop-invariance predicate for a value.
- `loop_operands_stable` — Definition; Direct operands stay fixed during the selected loop run.
- `numbering_check_sound` — Theorem; Accepted value numbering relates equal values at valid uses.
- `numbering_use_sound` — Theorem; Equal numbers imply equal values at a dominated use.
- `dominator_numbering_checked` — Theorem; Dominator-scoped numbering passes the numbering checker.
- `optimistic_numbering_checked` — Theorem; Optimistic numbering passes the numbering checker.
- `loop_invariant_sound` — Theorem; An invariant value changes at most once per loop execution.

### `AnalysesEgraph.v` — ANA-6

- `term_vars`, `legacy_subst`, `legacy_subst_bound` — finite replay substitution helpers.
- `legacy_subst_present`, `legacy_subst_missing`, `legacy_subst_bound_spec` — helper laws.

- `term` — Inductive; Variables and operator applications in e-graph terms.
- `TVar` — Constructor; A variable in an e-graph term.
- `TApp` — Constructor; An operator application in an e-graph term.
- `denote` — Definition; Evaluates a term in an environment.
- `equiv_term` — Definition; Equivalence of terms over valid environments.
- `subst_term` — Definition; Substitutes terms for variables in a term.
- `rewrite_rule` — Record; Left side, right side and side condition of a rewrite.
- `RewriteRule` — Constructor; Constructs the rewrite rule record.
- `rule_lhs` — Field; Left-hand side of a rewrite rule.
- `rule_rhs` — Field; Right-hand side of a rewrite rule.
- `rule_side` — Field; Side condition on a rewrite instance.
- `rule_sound` — Definition; A rewrite preserves denotation in valid environments.
- `rewrite_step` — Record; Position, rule, direction and substitution of a rewrite.
- `RewriteStep` — Constructor; Constructs the rewrite step record.
- `step_pos` — Field; Position of the rewritten subterm.
- `step_rule` — Field; Index of the applied rewrite rule.
- `step_forward` — Field; Direction in which the rule is applied.
- `step_subst` — Field; Substitution used for the rule instance.
- `replay` — Definition; Replays an explanation as a sequence of rewrite steps.
- `check_explanation` — Definition; Checks a replayed rewrite explanation.
- `term_eqb` — Definition; Decidable equality test for terms.
- `term_cost` — Definition; Sum of operator costs over a term.
- `egraph` — Definition; Hash-consed nodes and union-find classes for equality saturation.
- `saturate` — Definition; Runs directly proved bounded Rewrite saturation.
- `extract` — Definition; Extracts a candidate term from an e-graph.
- `optimise` — Definition; Returns an extracted term only after explanation and cost checks.
- `term_eqb_spec` — Theorem; Term equality succeeds exactly for equal terms.
- `check_explanation_sound` — Theorem; An accepted explanation relates equivalent terms.
- `check_explanation_refl` — Theorem; The empty explanation accepts equal terms.
- `optimise_sound` — Theorem; An accepted optimisation returns an equivalent cheaper term.

### `AnalysesScev.v` — ANA-7

- `iexpr` — Inductive; Invariant expressions built from variables, constants, sums and products.
- `IVar` — Constructor; An invariant variable expression.
- `IConst` — Constructor; An invariant integer constant expression.
- `IWordConst` — Constructor; A client word literal with explicit signed interpretation.
- `IAdd` — Constructor; The sum of two invariant expressions.
- `IMul` — Constructor; The product of two invariant expressions.
- `eval_iexpr` — Fixpoint; Evaluates an invariant expression in an invariant environment.
- `chrec` — Inductive; Chains of recurrences over invariant expressions.
- `CInv` — Constructor; A loop-invariant recurrence expression.
- `CRec` — Constructor; An additive chain of recurrences.
- `CGeo` — Constructor; A geometric chain of recurrences.
- `CSum`, `CProduct` — Constructors; Pointwise sum and product fallback expressions.
- `eval_chrec` — Fixpoint; Evaluates a recurrence at an iteration count.
- `chrec_add` — Definition; Adds two chains of recurrences.
- `chrec_mul` — Definition; Multiplies two chains of recurrences.
- `chrec_scale` — Definition; Scales a chain of recurrences by an integer.
- `cmp_kind` — Inductive; Comparison kinds used in loop tests.
- `CmpLt` — Constructor; Strict less-than comparison.
- `CmpLe` — Constructor; Less-than-or-equal comparison.
- `CmpNe` — Constructor; Not-equal comparison.
- `signedness` — Inductive; Signed or unsigned interpretation of a word.
- `Unsigned` — Constructor; Unsigned interpretation of a word.
- `Signed` — Constructor; Signed interpretation of a word.
- `view_z` — Definition; Interprets a word as signed or unsigned integer.
- `test_holds` — Definition; Interpretation of an integer comparison at a word width.
- `in_range` — Definition; Whether an integer lies in the selected word range.
- `loop_test` — Record; Comparison, signedness, recurrence and bound of a loop test.
- `LoopTest` — Constructor; Constructs the loop test record.
- `t_cmp` — Field; Comparison used by a loop exit test.
- `t_sign` — Field; Signedness of a loop exit test.
- `t_lhs` — Field; Recurrence tested at the loop exit.
- `t_bound` — Field; Loop-invariant bound in the exit test.
- `loop_view` — Record; SSA and edge information for one loop.
- `LoopView` — Constructor; Constructs the loop view record.
- `lssa` — Field; SSA view underlying the loop view.
- `lheader` — Field; Header of the analysed loop.
- `lbody` — Field; Membership in the analysed loop body.
- `lentry` — Field; Edges that enter the loop.
- `lback` — Field; Back edges of the loop.
- `ltest` — Field; Exit test associated with the loop.
- `scev_ops` — Record; Client operators and integer interpretations used by SCEV.
- `ScevOps` — Constructor; Constructs the scev ops record.
- `width_of` — Field; Word width of a concrete value.
- `to_Z` — Field; Integer interpretation of a concrete value.
- `add_op` — Field; Operator identified as addition.
- `mul_op` — Field; Operator identified as multiplication.
- `const_op` — Field; Operator identified as a constant.
- `scev_ops_laws` — Record; Operator evaluation agrees with the integer arithmetic model.
- `add_laws` — Field; Addition agrees with the integer interpretation.
- `mul_laws` — Field; Multiplication agrees with the integer interpretation.
- `const_laws` — Field; Constants agree with the integer interpretation.
- `to_Z_canonical` — Field; Concrete observations are canonical word representatives.
- `inv_env` — Definition; Values of loop invariants in an entry state.
- `signed_iexpr`, `signed_chrec`, `signed_inv_env` — Definitions; Sign-aware normalization and
  environment for loop trip evidence.
- `signed_iexpr_wrap`, `signed_chrec_wrap` — Theorems; Normalization preserves wrapped values.
- `scev_expr`, `SOutside`, `SPhi`, `SAdd`, `SMul`, `SConst` — Inductive and constructors;
  Finite expressions describing recognized updates.
- `scev_update`, `SAddUpdate`, `SMulUpdate`, `SDoubleUpdate` — Inductive and constructors;
  Supported recurrence update kinds.
- `scev_binding`, `ScevBinding`, `sb_phi`, `sb_base`, `sb_update_value`, `sb_kind`, `sb_other`,
  `sb_phi_first` — Record, constructor and fields; Syntactic phi binding description.
- `scev_plan`, `ScevPlan`, `sp_bindings`, `sp_target` — Record, constructor and fields;
  Ranked recurrence recognition plan.
- `iexpr_variables`, `scev_expr_root`, `scev_expr_operations`, `scev_plan_operations` —
  Definitions; Finite syntactic plan observations.
- `scev_plan_check`, `scev_compile_plan`, `recognise_plan`, `recognise_plan_checked` —
  Definitions and theorem; Plan checking, compilation and producer correctness.
- `stay_arrivals` — Definition; Number of loop-header arrivals along a run prefix.
- `loop_view_laws` — Record; SSA, entry, back-edge and exit-test laws for the loop.
- `l_ssa` — Field; The loop's SSA view satisfies its laws.
- `l_strict` — Field; The loop's SSA view satisfies strictness laws.
- `l_header_not_entry` — Field; The loop header is not a graph entry.
- `l_entry_edge` — Field; Loop entry edges satisfy the view's entry condition.
- `l_back_edge` — Field; Loop back edges satisfy the view's back-edge condition.
- `l_simple` — Field; The loop has the required simple control-flow form.
- `l_header_inside`, `l_initial_outside`, `l_single_ingress` — Fields; Header membership and
  all-body single ingress from graph entries.
- `l_phi_binding`, `l_phi_stay` — Fields; Exact incoming parameter binding and header-stay frame.
- `l_test_outside`, `l_plan_op_at_back` — Fields; Bound invariance and local operation observations.
- `l_back_test` — Field; Back edges obey the loop exit test.
- `recognise` — Definition; Recognises a recurrence for an SSA value.
- `trip_count` — Definition; Computes a trip count for a supported recurrence and test.
- `nowrap_check` — Definition; Checks range evidence for a recurrence and bound.
- `eval_chrec_add` — Theorem; Evaluating recurrence addition gives the sum of evaluations.
- `eval_chrec_mul` — Theorem; Evaluating recurrence multiplication gives the product of evaluations.
- `eval_chrec_scale` — Theorem; Evaluating a scaled recurrence scales its evaluation.
- `scev_sound` — Theorem; Recognised recurrence values agree with reachable loop arrivals.
- `trip_count_sound` — Theorem; A certified trip count matches the affine exit test.
- `loop_trip_sound` — Theorem; Loop back edges respect the certified trip-count bound.

### `AnalysesCalls.v` — ANA-8

- `resolver` — Definition; Selects direct, resolved indirect or fallback call targets.
- `recursive` — Definition; Whether a function belongs to a recursive call component.
- `purity_spec` — Definition; Local impurity and call dependencies for purity summaries.
- `purity_cover` — Definition; Lifts effects into the purity summary's step cover.
- `frame_weights` — Record; Stack weight assigned to each function.
- `FrameWeights` — Constructor; Constructs the frame weights record.
- `weight` — Field; Stack weight assigned to a function.
- `stack_demand` — Definition; With a function encoding, computes finite raw-graph path demand.
- `stack_above` — Definition; Uses a function encoding to sum active-frame weights through a frame.
- `callee_leaf` — Definition; Tests whether a function has no possible callees.
- `push_ctx` — Definition; Adds a call site to a bounded call string.
- `callstring_system` — Definition; Context-indexed summary constraints.
- `ctx_of` — Definition; Call string associated with a frame in a state.
- `args_view` — Record; Actuals, formals and frame values for call arguments.
- `ArgsView` — Constructor; Constructs the args view record.
- `actuals` — Field; Actual argument values at a call site.
- `formals` — Field; Formal argument values of a callee.
- `frame_val` — Field; Reads a value from a call frame.
- `callers_index` — Definition; Indexes call sites by their possible callees.
- `callers_of` — Definition; Looks up the indexed call sites of a function.
- `arg_fact` — Definition; Joins caller argument facts for a formal parameter.
- `resolver_sound` — Theorem; The resolver includes every possible dynamic callee.
- `recursive_sound` — Theorem; With a function encoding, a repeated active function lies on a cycle.
- `unreachable_never_runs` — Theorem; Functions unreachable in the call graph never become active.
- `purity_sound` — Theorem; A pure summary excludes observable effects during execution.
- `stack_demand_exact` — Theorem; On finite closed graphs and listed queries, detects cycles and
  returns the attained maximum raw-path weight otherwise.
- `stack_demand_sound` — Theorem; With a function encoding and graph well-formedness, the
  path-weight summary bounds stack demand.
- `callee_leaf_sound` — Theorem; A leaf function makes no further call.
- `callstring_sound` — Theorem; Context-indexed summaries cover the matching call strings.
- `callers_index_agrees` — Theorem; The caller index contains exactly the indexed call sites.
- `arg_fact_sound` — Theorem; Joined argument facts cover actual arguments of calls.

### `AnalysesPointsToBase.v` — ANA-9a

- `ptr_op` — Inductive; Pointer allocation, copy, load, store and escape operations.
- `PAlloc` — Constructor; A pointer allocation operation.
- `PCopy` — Constructor; A pointer copy operation.
- `PLoad` — Constructor; A pointer load operation.
- `PStore` — Constructor; A pointer store operation.
- `PEscape` — Constructor; A pointer escape operation.
- `pts_key` — Inductive; Pointer-value and heap-site unknowns of points-to constraints.
- `PVal` — Constructor; A points-to unknown for a value.
- `PHeap` — Constructor; A points-to unknown for a heap site.
- `site_universe` — Definition; Finite allocation sites appearing in pointer operations.
- `pts_set` — Definition; Finite points-to set over the operation's sites.
- `pts_lattice` — Definition; Finite powerset lattice for points-to sets.
- `andersen_system` — Definition; Side-effecting constraints for Andersen points-to facts.
- `andersen_static` — Definition; Declares reads and side targets for Andersen constraints.
- `ptr_view` — Record; Memory and pointer operations observed during execution.
- `PtrView` — Constructor; Constructs the ptr view record.
- `pmem` — Field; Memory view used by pointer analysis.
- `pval` — Field; Reads a pointer value from a state.
- `pop` — Field; Pointer operations represented by a step.
- `held` — Field; Pointer stored in memory at an address.
- `pbyte` — Field; Byte stored in memory at an address.
- `pts_of` — Definition; Allocation site of a pointer value in a state.
- `heap_pts` — Definition; Whether a site may contain a pointer to another site.
- `ptr_view_laws` — Record; Initial and step-origin laws for pointer targets.
- `pop_listed` — Field; Pointer operations in a step belong to the operation list.
- `pts_initial` — Field; Initial pointer targets satisfy the points-to premise.
- `heap_initial` — Field; Initial heap pointers satisfy the points-to premise.
- `pts_origin` — Field; Every new pointer target has an allowed origin.
- `heap_origin` — Field; Every new heap pointer target has an allowed origin.
- `Build_ptr_view_laws` — Constructor; builds the pointer-view laws.
- `andersen_sound`, `andersen_monotone`, `andersen_terminates` — Andersen specification laws.

### `AnalysesPointsToDelta.v` — ANA-9a

- `andersen_delta`, `andersen_delta_least`, `andersen_delta_sound` — direct delta producer and laws.

### `AnalysesPointsTo.v` — ANA-9

- `relational_ptr_view`, `RelationalPtrView`, `rel_value`, `rel_heap` — Record, constructor and
  fields; relational value and heap observations.
- `relational_ptr_laws`, `Build_relational_ptr_laws` — Record and constructor; initial and
  step-origin laws for relational observations.
- `rel_value_initial`, `rel_heap_initial`, `rel_value_origin`, `rel_heap_origin` — Fields;
  independent initial and step-origin obligations.
- `relational_andersen_sound` — Theorem; post-solutions include relational observations.
- `steens_result` — Record; Pointer classes and their associated pointee classes.
- `SteensResult` — Constructor; Constructs the steens result record.
- `classes` — Field; Union-find classes of pointer variables.
- `pointee` — Field; Class of pointees associated with a pointer class.
- `may_alias` — Definition; Whether two pointer variables may share a unification class.
- `steensgaard` — Definition; Unifies pointer classes for Steensgaard points-to facts.
- `escaped_sites` — Definition; Least set of sites escaping through pointer operations.
- `write_universe` — Definition; Finite footprint universe for zero-byte facts.
- `written_set` — Definition; Finite set of written footprints.
- `zero_written_system` — Definition; Forward constraints tracking footprints written since entry.
- `zero_laws`, `z_address` — Record, field; zero-byte laws and retained pointer address transport.
- `z_view` — Field; Graph view underlying zero-byte analysis.
- `z_no_stays` — Field; The zero-byte graph has no point-preserving steps.
- `z_init` — Field; Initial existing blocks satisfy the zero-byte condition.
- `z_fresh` — Field; Fresh allocations contain zero bytes.
- `z_kept` — Field; Unwritten bytes preserve their prior zero value.
- `steensgaard_sound` — Theorem; Unification classes cover reachable aliases.
- `steensgaard_coarser` — Theorem; Steensgaard classes include least Andersen aliases.
- `escaped_closed` — Theorem; The computed escaped-site set is closed under escape dependencies.
- `zero_written_sound` — Theorem; Uncovered bytes of existing blocks remain zero.

### `AnalysesMemoryBase.v` — ANA-10a

- `barrier_view` — Record; Validation and invalidation information for memory accesses.
- `BarrierView` — Constructor; Constructs the barrier view record.
- `bgraph` — Field; Graph view underlying the access barrier analysis.
- `validates` — Field; Accesses validated by an edge.
- `barrier` — Field; Accesses invalidated by an edge.
- `accessible` — Field; Accessibility predicate for an access.
- `barrier_laws` — Record; Accessibility laws for validation and barriers.
- `b_view` — Field; The barrier graph view satisfies its laws.
- `b_no_stays` — Field; The barrier graph has no point-preserving steps.
- `validates_accessible` — Field; A validated access is accessible.
- `accessible_persists` — Field; Accessibility persists across non-barrier steps.
- `accessible_sub` — Field; Accessibility is preserved for covered subranges.
- `accessible_bytes` — Field; An accessible range admits the specified byte access.
- `validated_system` — Definition; Constraints tracking accesses validated since barriers.
- `store_view` — Record; Overwrites, reads and agreement for dead-store analysis.
- `StoreView` — Constructor; Constructs the store view record.
- `sgraph` — Field; Graph view underlying the dead-store analysis.
- `overwrites` — Field; Byte ranges overwritten by an edge.
- `mreads` — Field; Byte ranges read by an edge.
- `sagree` — Field; State agreement for the store analysis.
- `store_boundary` — Field; Prepared canonical boundary fact for each graph node.
- `dead_store_transfer` — Definition; Backward transfer for byte ranges covered by later writes.
- `dead_store_system` — Definition; Backward constraints for dead-store coverage.
- `dead_store_reached` — Definition; Listed-node assignments are reached.
- `store_laws` — Record; Step and ending laws for dead-store agreement.
- `s_view` — Field; The store graph view satisfies its laws.
- `s_no_stays` — Field; The store graph has no point-preserving steps.
- `s_agreement` — Field; The store relation satisfies agreement laws.
- `s_terminal_boundary` — Field; Actual ending points have an empty boundary.
- `s_step` — Field; Store agreement is preserved by matching steps on reached assignments.
- `s_ends` — Field; Store agreement preserves observable endings.
- `bytes_view` — Record; Allocation sites, bytes and node write footprints.
- `BytesView` — Constructor; Constructs the bytes view record.
- `bgv` — Field; Graph view underlying byte-level memory analysis.
- `writes_at` — Field; Footprints possibly written at a node.
- `bsite` — Field; Historical allocation site retained after free.
- `byte` — Field; Byte value at an allocation and offset.
- `bytes_laws` — Record; Byte preservation and graph laws for memory steps.
- `by_view` — Field; The byte graph view satisfies its laws.
- `by_no_stays` — Field; The byte graph has no point-preserving steps.
- `byte_frame` — Field; A changed byte is covered by the node's write footprints.
- `footprints_disjoint` — Definition; Tests whether two footprint lists have disjoint bytes.
- `invariant_load` — Definition; Tests loop-invariant address and non-overlapping loop writes.
- `validated_sound` — Theorem; Validated access facts imply the stated accessibility property.
- `dead_store_sound` — Theorem; Covered writes justify the dead-store agreement claim.
- `footprints_disjoint_sound` — Theorem; The disjointness test implies disjoint covered bytes.
- `immutable_sound` — Theorem; Bytes in a footprint without writes remain unchanged.
- `invariant_load_sound` — Theorem; Covered bytes stay unchanged within the loop.

- `byte_site_stable` — field; preserves a historical identity's site on each reachable step.
- `epoch_view`, `EpochView`, `epoch_bytes`, `epoch_live` — record, constructor and fields; concrete
  allocation identity and liveness view.
- `epoch_laws`, `Build_epoch_laws`, `epoch_byte_laws`, `epoch_live_site`,
  `epoch_allocate_fresh` — law record, constructor and fields; historical sites and fresh identity.
- `epoch_no_resurrection` — Theorem; a dead identity with a historical site remains dead.


### `AnalysesMemoryLegacy.v` — ANA-10e

- `mem_node`, `MDef`, `MLive` — memory definition or live-on-entry node.
- `memory_ssa`, `MemorySSA`, `def_of_load` — legacy load-to-definition candidate.
- `no_clobber_check`, `no_clobber_unchanged` — validated candidate and byte-frame theorem.

- `legacy_nodes`, `legacy_disjoint`, `legacy_disjoint_b`, `legacy_pair_clear` — all-walk legacy
  specification and exact disjointness test.
- `legacy_disjoint_b_correct`, `no_clobber_check_correct`, `project_memory_legacy_correct` —
  Theorems; disjointness reflection, checker reflection and safe projection.
- `project_memory_legacy` — Definition; conditional projection from the version walker.


### `AnalysesRules.v` — ANA-11

- `pred` — Inductive; Predicates of the liveness, neededness and reaching rule programs.
- `PUse` — Constructor; The base use predicate of the rules programs.
- `PDef` — Constructor; The base definition predicate of the rules programs.
- `PSucc` — Constructor; The control-flow successor predicate.
- `PNec` — Constructor; The necessary-value seed predicate.
- `PDep` — Constructor; The neededness dependency predicate.
- `PExitUse` — Constructor; The exit-use seed predicate.
- `PLive` — Constructor; The derived liveness predicate.
- `PNeeded` — Constructor; The derived neededness predicate.
- `PReaches` — Constructor; The derived reaching-definitions predicate.
- `pred_encoding` — Definition; Injective encoding of the rule-program predicates.
- `pred_arity` — Definition; Tuple arity of each rule-program predicate.
- `args2` — Definition; Encodes a two-element ground tuple.
- `args3` — Definition; Encodes a three-element ground tuple.
- `extract_live_facts` — Definition; Extracts liveness base facts from graph nodes and edges.
- `extract_needed_facts` — Definition; Extracts neededness base facts from the demand view.
- `v` — Definition; Constructs a rule variable from its index.
- `atm` — Definition; Constructs an atom from a predicate and its terms.
- `liveness_program` — Definition; Datalog rules for liveness.
- `neededness_program` — Definition; Datalog rules for neededness.
- `reaching_program` — Definition; Datalog rules for reaching definitions.
- `live_of_db` — Definition; Converts a rule database to liveness facts.
- `needed_of_db` — Definition; Converts a rule database to neededness facts.
- `reach_of_db` — Definition; Converts a rule database to reaching-definition facts.
- `rules_liveness_solves` — Theorem; The rules database yields a liveness post-solution.
- `rules_liveness_least` — Theorem; The rules liveness solution is least.
- `rules_neededness_solves` — Theorem; The rules database yields a neededness post-solution.
- `rules_neededness_least` — Theorem; The rules neededness solution is least.
- `rules_reaching_solves` — Theorem; The rules database yields a reaching-definitions post-solution.
- `rules_reaching_least` — Theorem; The rules reaching-definitions solution is least.
- `rules_liveness_model` — Theorem; The rules database represents the least liveness model.
- `rules_neededness_model` — Theorem; The rules database represents the least neededness model.
- `rules_reaching_model` — Theorem; The database represents the least reaching-definitions model.


## C19 additions

The owning API documents fix signatures and theorem statements. These entries are contracts,
not evidence of completed implementations. ANA-6 owns its direct Rewrite facade and legacy replay;
REW-7 owns the independent Order, SSA and word clients.

### `RewriteSyntax.v` — REW-1

- `rw_term` — public declaration; see the owning API contract.
- `RWVar` — public declaration; see the owning API contract.
- `RWApp` — public declaration; see the owning API contract.
- `rw_pattern` — public declaration; see the owning API contract.
- `RWHole` — public declaration; see the owning API contract.
- `RWPVar` — public declaration; see the owning API contract.
- `RWPApp` — public declaration; see the owning API contract.
- `rw_sort` — public declaration; see the owning API contract.
- `rwp_sort` — public declaration; see the owning API contract.
- `rw_signature` — public declaration; see the owning API contract.
- `RwSignature` — public declaration; see the owning API contract.
- `rw_var_sort` — public declaration; see the owning API contract.
- `rw_operator_shape` — public declaration; see the owning API contract.
- `rw_typed` — public declaration; see the owning API contract.
- `rw_typed_var` — public declaration; see the owning API contract.
- `rw_typed_app` — public declaration; see the owning API contract.
- `rwp_typed` — public declaration; see the owning API contract.
- `rwp_typed_hole` — public declaration; see the owning API contract.
- `rwp_typed_var` — public declaration; see the owning API contract.
- `rwp_typed_app` — public declaration; see the owning API contract.
- `rw_substitution` — public declaration; see the owning API contract.
- `rw_sub_typed` — public declaration; see the owning API contract.
- `rw_instantiate` — public declaration; see the owning API contract.
- `rw_instantiate_typed` — public declaration; see the owning API contract.

### `RewriteRules.v` — REW-1

- `rw_semantics` — public declaration; see the owning API contract.
- `RwSemantics` — public declaration; see the owning API contract.
- `rw_var_value` — public declaration; see the owning API contract.
- `rw_eval_op` — public declaration; see the owning API contract.
- `rw_denote` — public declaration; see the owning API contract.
- `rw_equiv` — public declaration; see the owning API contract.
- `rw_rule` — public declaration; see the owning API contract.
- `RwRule` — public declaration; see the owning API contract.
- `rw_holes` — public declaration; see the owning API contract.
- `rw_hole_sort` — public declaration; see the owning API contract.
- `rw_lhs` — public declaration; see the owning API contract.
- `rw_rhs` — public declaration; see the owning API contract.
- `rw_condition` — public declaration; see the owning API contract.
- `rw_rule_wf` — public declaration; see the owning API contract.
- `rw_rule_sound` — public declaration; see the owning API contract.

### `RewriteEquality.v` — REW-1

- `rw_equal` — public declaration; see the owning API contract.
- `rw_eq_refl` — public declaration; see the owning API contract.
- `rw_eq_sym` — public declaration; see the owning API contract.
- `rw_eq_trans` — public declaration; see the owning API contract.
- `rw_eq_app` — public declaration; see the owning API contract.
- `rw_eq_rule` — public declaration; see the owning API contract.
- `rw_equal_sound` — public declaration; see the owning API contract.
- `rw_equal_typed` — public declaration; see the owning API contract.

### `RewriteEgraph.v` — REW-2

- `rw_union_structure` — structural relationship of a successful union.

- `rw_id` — public declaration; see the owning API contract.
- `rw_node` — public declaration; see the owning API contract.
- `RWNVar` — public declaration; see the owning API contract.
- `RWNApp` — public declaration; see the owning API contract.
- `rw_node_sort` — public declaration; see the owning API contract.
- `rw_graph` — public declaration; see the owning API contract.
- `RwGraph` — public declaration; see the owning API contract.
- `rw_roots` — public declaration; see the owning API contract.
- `rw_nodes_in` — public declaration; see the owning API contract.
- `rw_class_roots` — public declaration; see the owning API contract.
- `rw_sorts` — public declaration; see the owning API contract.
- `rw_nodes` — public declaration; see the owning API contract.
- `rw_find` — public declaration; see the owning API contract.
- `rw_class_sort` — public declaration; see the owning API contract.
- `rw_node_at` — public declaration; see the owning API contract.
- `rw_represents` — public declaration; see the owning API contract.
- `rw_repr_var` — public declaration; see the owning API contract.
- `rw_repr_app` — public declaration; see the owning API contract.
- `rw_graph_wf` — public declaration; see the owning API contract.
- `rw_graph_sound` — public declaration; see the owning API contract.
- `rw_extends` — public declaration; see the owning API contract.
- `rw_clean` — public declaration; see the owning API contract.
- `rw_productive` — public declaration; see the owning API contract.
- `rw_joinable` — public declaration; see the owning API contract.
- `rw_empty` — public declaration; see the owning API contract.
- `rw_add` — public declaration; see the owning API contract.
- `rw_union` — public declaration; see the owning API contract.
- `rw_empty_wf` — public declaration; see the owning API contract.
- `rw_empty_sound` — public declaration; see the owning API contract.
- `rw_empty_productive` — public declaration; see the owning API contract.
- `rw_add_correct` — public declaration; see the owning API contract.
- `rw_union_correct` — public declaration; see the owning API contract.

### `RewriteIndex.v` — REW-2

- `rw_index_root_parents`, `rw_parent_nodes`, `rw_parent_nodes_agree` — canonical parent index.
- `rw_index_after_union`, `rw_index_after_union_agrees` — union index update and agreement.
- `rw_index_after_node_change`, `rw_index_after_node_change_agrees` — node updates and agreement.

- `rw_index` — public declaration; see the owning API contract.
- `RwIndex` — public declaration; see the owning API contract.
- `rw_index_ops` — public declaration; see the owning API contract.
- `rw_index_parents` — public declaration; see the owning API contract.
- `rw_lookup_list` — public declaration; see the owning API contract.
- `rw_index_agrees` — public declaration; see the owning API contract.
- `rw_build_index` — public declaration; see the owning API contract.
- `rw_build_index_agrees` — public declaration; see the owning API contract.

### `RewriteRebuild.v` — REW-2

- `rw_rebuild` — public declaration; see the owning API contract.
- `rw_rebuild_correct` — public declaration; see the owning API contract.

### `RewriteMatch.v` — REW-3

- `rwp_holes` — public declaration; see the owning API contract.
- `rw_assignment` — public declaration; see the owning API contract.
- `rw_covers` — public declaration; see the owning API contract.
- `rw_match` — public declaration; see the owning API contract.
- `rw_match_sound` — public declaration; see the owning API contract.
- `rw_match_complete` — public declaration; see the owning API contract.

### `RewriteAnalysis.v` — REW-4

- `rw_analysis` — public declaration; see the owning API contract.
- `RwAnalysis` — public declaration; see the owning API contract.
- `rw_fact_holds` — public declaration; see the owning API contract.
- `rw_fact_unknown` — public declaration; see the owning API contract.
- `rw_fact_combine` — public declaration; see the owning API contract.
- `rw_fact_transfer` — public declaration; see the owning API contract.
- `rw_fact_valid` — public declaration; see the owning API contract.
- `rw_facts_valid` — public declaration; see the owning API contract.
- `rw_analysis_laws` — public declaration; see the owning API contract.
- `rw_unknown_valid` — public declaration; see the owning API contract.
- `rw_combine_valid` — public declaration; see the owning API contract.
- `rw_transfer_valid` — public declaration; see the owning API contract.
- `rw_analyse_step` — public declaration; see the owning API contract.
- `rw_analyse_step_valid` — public declaration; see the owning API contract.

### `RewriteRun.v` — REW-5

- `rw_attempt` — public declaration; see the owning API contract.
- `RwAttempt` — public declaration; see the owning API contract.
- `rw_attempt_rule` — public declaration; see the owning API contract.
- `rw_attempt_root` — public declaration; see the owning API contract.
- `rw_attempt_sub` — public declaration; see the owning API contract.
- `rw_attempt_substitution` — public declaration; see the owning API contract.
- `rw_check_sub` — public declaration; see the owning API contract.
- `rw_check_sub_sound` — public declaration; see the owning API contract.
- `rw_check_sub_complete` — public declaration; see the owning API contract.
- `rw_rep_test` — public declaration; see the owning API contract.
- `rw_rep_test_spec` — public declaration; see the owning API contract.
- `rw_apply` — public declaration; see the owning API contract.
- `rw_apply_correct` — public declaration; see the owning API contract.
- `rw_stop` — public declaration; see the owning API contract.
- `RWStopped` — public declaration; see the owning API contract.
- `RWFuelExhausted` — public declaration; see the owning API contract.
- `rw_run_result` — public declaration; see the owning API contract.
- `RwRunResult` — public declaration; see the owning API contract.
- `rw_run_graph` — public declaration; see the owning API contract.
- `rw_run_stop` — public declaration; see the owning API contract.
- `rw_strategy` — public declaration; see the owning API contract.
- `rw_run` — public declaration; see the owning API contract.
- `rw_run_correct` — public declaration; see the owning API contract.

### `RewriteExtract.v` — REW-6

- `rw_tree_cost` — public declaration; see the owning API contract.
- `rw_extract_tree` — public declaration; see the owning API contract.
- `rw_extract_tree_some` — public declaration; see the owning API contract.
- `rw_extract_tree_none` — public declaration; see the owning API contract.
- `rw_extract_tree_equiv` — public declaration; see the owning API contract.

### `AnalysesEgraph.v` — ANA-6 (direct facade)

- `legacy_graph`, `legacy_root`, `legacy_saturate_direct` — direct facade and preservation.

- `legacy_signature` — public declaration; see the owning API contract.
- `legacy_embed` — public declaration; see the owning API contract.
- `legacy_project` — public declaration; see the owning API contract.
- `legacy_pattern` — public declaration; see the owning API contract.
- `legacy_substitution` — public declaration; see the owning API contract.
- `legacy_semantics` — public declaration; see the owning API contract.
- `legacy_admissible` — public declaration; see the owning API contract.
- `legacy_variables` — public declaration; see the owning API contract.
- `legacy_rule_holes` — public declaration; see the owning API contract.
- `legacy_total_sub` — public declaration; see the owning API contract.
- `legacy_rule` — public declaration; see the owning API contract.
- `legacy_at` — public declaration; see the owning API contract.
- `legacy_replace_at` — public declaration; see the owning API contract.
- `rw_at` — public declaration; see the owning API contract.
- `rw_replace_at` — public declaration; see the owning API contract.
- `legacy_project_embed` — public declaration; see the owning API contract.
- `legacy_embed_typed` — public declaration; see the owning API contract.
- `legacy_denote_agrees` — public declaration; see the owning API contract.
- `legacy_substitute_agrees` — public declaration; see the owning API contract.
- `legacy_at_agrees` — public declaration; see the owning API contract.
- `legacy_replace_agrees` — public declaration; see the owning API contract.
- `legacy_equiv_agrees` — public declaration; see the owning API contract.
- `legacy_cost_agrees` — public declaration; see the owning API contract.
- `legacy_rule_wf` — public declaration; see the owning API contract.
- `legacy_rule_sound` — public declaration; see the owning API contract.
- `legacy_guard_uses_witness` — public declaration; see the owning API contract.

### `AnalysesRewriteDomains.v` — REW-7

- `rw_order_holds` — public declaration; see the owning API contract.
- `rw_order_analysis` — public declaration; see the owning API contract.
- `rw_order_transfer_sound` — public declaration; see the owning API contract.
- `rw_order_analysis_laws` — public declaration; see the owning API contract.

### `AnalysesSsaRewrite.v` — REW-7

- `ssa_rw_semantics` — public declaration; see the owning API contract.
- `ssa_rewrite_value` — public declaration; see the owning API contract.
- `ssa_region_state` — public declaration; see the owning API contract.
- `ssa_region_semantics` — public declaration; see the owning API contract.
- `ssa_region_endings` — public declaration; see the owning API contract.
- `ssa_region_relation` — public declaration; see the owning API contract.
- `ssa_region_bisimulation` — public declaration; see the owning API contract.
- `ssa_region_rewrite_behaviour` — public declaration; see the owning API contract.
- `rw_replacement_laws` — public declaration; see the owning API contract.
- `rw_replacement_bisim` — public declaration; see the owning API contract.
- `rw_replacement_behaviour` — public declaration; see the owning API contract.

### `AnalysesRewriteWord.v` — REW-7

- `rw_word_op` — public declaration; see the owning API contract.
- `WordLit` — public declaration; see the owning API contract.
- `WordAdd` — public declaration; see the owning API contract.
- `WordMul` — public declaration; see the owning API contract.
- `WordDiv` — public declaration; see the owning API contract.
- `WordRotl` — public declaration; see the owning API contract.
- `rw_word_encoding` — public declaration; see the owning API contract.
- `rw_word_sig` — public declaration; see the owning API contract.
- `rw_word_eval` — public declaration; see the owning API contract.
- `rw_word_admissible` — public declaration; see the owning API contract.
- `rw_ground_pattern` — public declaration; see the owning API contract.
- `rw_word_add_zero` — public declaration; see the owning API contract.
- `rw_word_mul_one` — public declaration; see the owning API contract.
- `rw_word_rotate_zero` — public declaration; see the owning API contract.
- `rw_word_div_self` — public declaration; see the owning API contract.
- `rw_word_nonzero` — public declaration; see the owning API contract.
- `rw_word_analysis` — public declaration; see the owning API contract.
- `rw_word_nonzero_check` — public declaration; see the owning API contract.
- `rw_word_analysis_laws` — public declaration; see the owning API contract.
- `rw_word_singleton_nonzero` — public declaration; see the owning API contract.
- `rw_word_literal_fact` — public declaration; see the owning API contract.
- `rw_word_add_zero_sound` — public declaration; see the owning API contract.
- `rw_word_mul_one_sound` — public declaration; see the owning API contract.
- `rw_word_rotate_zero_sound` — public declaration; see the owning API contract.
- `rw_word_add_zero_wf` — public declaration; see the owning API contract.
- `rw_word_mul_one_wf` — public declaration; see the owning API contract.
- `rw_word_rotate_zero_wf` — public declaration; see the owning API contract.
- `rw_word_div_self_wf` — public declaration; see the owning API contract.
- `rw_word_div_self_sound` — public declaration; see the owning API contract.
- `rw_word_demo_add` — public declaration; see the owning API contract.
- `rw_word_demo_mul` — public declaration; see the owning API contract.
- `rw_word_demo_rotate` — public declaration; see the owning API contract.
- `rw_word_demo_div` — public declaration; see the owning API contract.
- `rw_word_demo_zero` — public declaration; see the owning API contract.

### `RulesJoin.v` — RUL-2a

- `join_strategy` — public declaration; see the owning API contract.
- `IndexedNested` — public declaration; see the owning API contract.
- `IndexedMultiway` — public declaration; see the owning API contract.
- `fire_rule_join` — public declaration; see the owning API contract.
- `fire_rule_join_exact` — public declaration; see the owning API contract.
- `fire_rule_join_wf` — public declaration; see the owning API contract.

### `RulesDelta.v` — RUL-2b

- `solve_program_delta` — public declaration; see the owning API contract.
- `solve_program_delta_exact` — public declaration; see the owning API contract.
- `solve_program_delta_none` — public declaration; see the owning API contract.
- `solve_program_delta_agrees` — public declaration; see the owning API contract.

### `CollectionsDenseSet.v` — COL-3

- `dense_universe` — public declaration; see the owning API contract.
- `DenseUniverse` — public declaration; see the owning API contract.
- `dense_keys` — public declaration; see the owning API contract.
- `dense_index` — public declaration; see the owning API contract.
- `dense_length` — public declaration; see the owning API contract.
- `dense_universe_wf` — public declaration; see the owning API contract.
- `dense_prepare` — public declaration; see the owning API contract.
- `dense_set` — public declaration; see the owning API contract.
- `dense_empty` — public declaration; see the owning API contract.
- `dense_mem` — public declaration; see the owning API contract.
- `dense_add` — public declaration; see the owning API contract.
- `dense_remove` — public declaration; see the owning API contract.
- `dense_union` — public declaration; see the owning API contract.
- `dense_inter` — public declaration; see the owning API contract.
- `dense_diff` — public declaration; see the owning API contract.
- `dense_subset` — public declaration; see the owning API contract.
- `dense_to_finset` — public declaration; see the owning API contract.
- `dense_of_finset` — public declaration; see the owning API contract.
- `dense_prepare_wf` — public declaration; see the owning API contract.
- `dense_mem_refines` — public declaration; see the owning API contract.
- `dense_roundtrip` — public declaration; see the owning API contract.
- `dense_union_mem` — public declaration; see the owning API contract.
- `dense_inter_mem` — public declaration; see the owning API contract.
- `dense_diff_mem` — public declaration; see the owning API contract.
- `dense_subset_spec` — public declaration; see the owning API contract.
- `dense_add_mem` — public declaration; see the owning API contract.
- `dense_remove_mem` — public declaration; see the owning API contract.

### `FixpointNested.v` — FIX-5

- `nested_run` — public declaration; see the owning API contract.
- `nested_solve_fuel` — public declaration; see the owning API contract.
- `nested_run_sound` — public declaration; see the owning API contract.
- `nested_run_eventually` — public declaration; see the owning API contract.

### `FixpointObserve.v` — FIX-6

- `observation_plan` — public declaration; see the owning API contract.
- `ObservationPlan` — public declaration; see the owning API contract.
- `observation_components` — public declaration; see the owning API contract.
- `observation_expire` — public declaration; see the owning API contract.
- `observation_prepare` — public declaration; see the owning API contract.
- `observation_plan_check` — public declaration; see the owning API contract.
- `observation_reference` — public declaration; see the owning API contract.
- `observation_project` — public declaration; see the owning API contract.
- `observation_full_reference` — public declaration; see the owning API contract.
- `observation_run` — public declaration; see the owning API contract.
- `observation_prepare_checked` — public declaration; see the owning API contract.
- `observation_run_refines` — public declaration; see the owning API contract.
- `observation_reference_projection` — public declaration; see the owning API contract.
- `observation_full_reference_sound` — public declaration; see the owning API contract.
- `observation_plan_complete` — public declaration; see the owning API contract.
- `observation_run_eventually` — public declaration; see the owning API contract.

### `FixpointLocalDirect.v` — FIX-7

- `local_direct_closure`, `local_direct_system`, `local_direct_static`, `local_direct` — static
  closure, restricted system and direct local producer.
- `local_direct_closure_wf`, `local_direct_closure_roots`, `local_direct_closure_complete` —
  closure properties.
- `local_direct_closure_least`, `local_direct_system_constraints` — least closure and exact
  restricted-constraint membership.
- `local_direct_roots`, `local_direct_closed` — root coverage and closed partial solution.

### `DomainsKnownBitsFast.v` — DOM-8

- `tnum_mul_precise` — public declaration; see the owning API contract.
- `known_bits_precise_domain` — public declaration; see the owning API contract.
- `tnum_mul_precise_sound` — public declaration; see the owning API contract.
- `known_bits_precise_word_laws` — public declaration; see the owning API contract.
- `tnum_mul_precise_constants` — public declaration; see the owning API contract.

### `ViewsSsaPoints.v` — VIEW-8

- `point_uses` — public declaration; see the owning API contract.
- `PointUses` — public declaration; see the owning API contract.
- `live_graph` — public declaration; see the owning API contract.
- `edge_use` — public declaration; see the owning API contract.
- `edge_def` — public declaration; see the owning API contract.
- `exit_use` — public declaration; see the owning API contract.
- `syntactic_live` — public declaration; see the owning API contract.
- `live_exit` — public declaration; see the owning API contract.
- `live_edge_use` — public declaration; see the owning API contract.
- `live_edge_next` — public declaration; see the owning API contract.
- `ssa_points` — public declaration; see the owning API contract.
- `SsaPoints` — public declaration; see the owning API contract.
- `point_chain` — public declaration; see the owning API contract.
- `point_chain_one` — public declaration; see the owning API contract.
- `point_chain_step` — public declaration; see the owning API contract.
- `point_model` — public declaration; see the owning API contract.
- `block_graph` — public declaration; see the owning API contract.
- `points_in_block` — public declaration; see the owning API contract.
- `instruction_edges` — public declaration; see the owning API contract.
- `parameter_edge` — public declaration; see the owning API contract.
- `block_of_point` — public declaration; see the owning API contract.
- `block_edge_of` — public declaration; see the owning API contract.
- `block_params` — public declaration; see the owning API contract.
- `block_edge_args` — public declaration; see the owning API contract.
- `point_definition` — public declaration; see the owning API contract.
- `point_use_at` — public declaration; see the owning API contract.
- `ssa_point_laws` — public declaration; see the owning API contract.
- `points_graph_wf` — public declaration; see the owning API contract.
- `points_out_nodup` — public declaration; see the owning API contract.
- `blocks_graph_wf` — public declaration; see the owning API contract.
- `blocks_out_nodup` — public declaration; see the owning API contract.
- `points_covered` — public declaration; see the owning API contract.
- `points_unique` — public declaration; see the owning API contract.
- `points_owner` — public declaration; see the owning API contract.
- `blocks_nonempty` — public declaration; see the owning API contract.
- `points_ordered` — public declaration; see the owning API contract.
- `instruction_edges_internal` — public declaration; see the owning API contract.
- `instruction_edges_complete` — public declaration; see the owning API contract.
- `parameter_edge_first` — public declaration; see the owning API contract.
- `parameter_edge_defs` — public declaration; see the owning API contract.
- `point_edge_projection` — public declaration; see the owning API contract.
- `phi_args_length` — public declaration; see the owning API contract.
- `phi_edge_use` — public declaration; see the owning API contract.
- `block_edge_covered` — public declaration; see the owning API contract.
- `block_edge_unique` — public declaration; see the owning API contract.
- `reachable_point_ssa` — public declaration; see the owning API contract.
- `point_ssa_single_entry` — public declaration; see the owning API contract.
- `point_ssa_uses_defined` — public declaration; see the owning API contract.
- `point_ssa_defs_at_home` — public declaration; see the owning API contract.
- `point_ssa_home_kills` — public declaration; see the owning API contract.

### `AnalysesSsaLiveQuery.v` — ANA-12

- `general_live_query` — Definition; General-graph liveness query from prepared Rules rows.
- `general_live_query_exact` — Theorem; Exact on listed nodes of a well-formed graph.

- `reduced_path` — public declaration; see the owning API contract.
- `rt_step` — public declaration; see the owning API contract.
- `rt_reaches` — public declaration; see the owning API contract.
- `ssa_query_graph` — public declaration; see the owning API contract.
- `SsaQueryGraph` — public declaration; see the owning API contract.
- `query_cfg` — public declaration; see the owning API contract.
- `query_dfs` — public declaration; see the owning API contract.
- `query_dom` — public declaration; see the owning API contract.
- `query_reduced` — public declaration; see the owning API contract.
- `query_back_closure` — public declaration; see the owning API contract.
- `ssa_query_values` — public declaration; see the owning API contract.
- `SsaQueryValues` — public declaration; see the owning API contract.
- `query_def` — public declaration; see the owning API contract.
- `query_uses` — public declaration; see the owning API contract.
- `live_index_get` — public declaration; see the owning API contract.
- `prepare_ssa_query_graph` — public declaration; see the owning API contract.
- `prepare_ssa_query_values` — public declaration; see the owning API contract.
- `ssa_live_query` — public declaration; see the owning API contract.
- `ssa_query_graph_structure` — public declaration; see the owning API contract.
- `ssa_query_graph_agrees` — public declaration; see the owning API contract.
- `ssa_query_values_agree` — public declaration; see the owning API contract.
- `ssa_live_query_exact` — public declaration; see the owning API contract.
- `ssa_live_query_dense` — public declaration; see the owning API contract.
- `ssa_live_query_rules` — public declaration; see the owning API contract.

### `AnalysesSsaLiveSets.v` — ANA-13

- `sparse_live_materialize` — public declaration; see the owning API contract.
- `sparse_live_at` — public declaration; see the owning API contract.
- `sparse_live_materialize_exact` — public declaration; see the owning API contract.
- `sparse_live_materialize_dense` — public declaration; see the owning API contract.
- `sparse_live_materialize_rules` — public declaration; see the owning API contract.
- `sparse_live_query_agrees` — public declaration; see the owning API contract.

### `AnalysesLiveness.v` — ANA-1

- `var_point_uses` — public declaration; see the owning API contract.
- `syntactic_live_least` — public declaration; see the owning API contract.

### `AnalysesRules.v` — ANA-11

- `syntactic_live_rules` — public declaration; see the owning API contract.


<!-- C19 memory names -->


### `ViewsMemoryEffects.v` — ANA-10b

- `memory_scope`, `MemoryRegions`, `MemoryAll`, `memory_scope_covers` — scope type, constructors
  and coverage predicate.
- `memory_effect`, `MemoryRead`, `MemoryWrite`, `MemoryReadWrite`, `MemoryCall`, `MemoryBarrier`,
  `effect_reads`, `effect_writes`, `effect_is_def` — ordered effects and their projections.
- `memory_effect_view`, `MemoryEffectView`, `effect_graph`, `edge_effects`, `effect_snapshot`,
  `effect_site`, `effect_byte`, `effect_step`, `effect_read`, `transition_read` — client view.
- `effect_trace`, `effect_trace_nil`, `effect_trace_cons`, `effect_trace_states`,
  `effect_states_nil`, `effect_states_cons` — ordered snapshot trace relations and constructors.
- `memory_effect_laws`, `Build_memory_effect_laws`, `effect_view_laws`, `effect_no_stays`,
  `effect_step_trace`, `effect_read_covered`, `effect_site_stable`, `effect_byte_frame` — laws.
- `effect_transition_byte_covered` — Theorem; a changed byte is covered by a listed effect.

### `AnalysesMemoryGraph.v` — ANA-10b

- `memory_version`, `MemoryLive`, `MemoryPhi`, `MemoryDef` — structural version identifiers.
- `memory_graph`, `MemoryGraph`, `memory_phis`, `memory_versions`, `memory_in`, `memory_before`,
  `memory_out`, `memory_operand` — graph representation and projections.
- `memory_occurrence`, `memory_phi_at`, `memory_valid_version`, `memory_after` — model predicates
  and effect transfer.
- `memory_edge_flow`, `memory_edge_nil`, `memory_edge_cons`, `memory_arrival` — local edge flow
  and incoming-edge phi selection.
- `memory_graph_wf`, `Build_memory_graph_wf`, `memory_cfg_wf`, `memory_phis_nodup`,
  `memory_phi_reachable`, `memory_versions_nodup`, `memory_versions_exact`,
  `memory_entries_arrive`, `memory_edges_flow`, `memory_edges_arrive`, `memory_in_valid`,
  `memory_out_valid`, `memory_before_domain`, `memory_operand_domain` — graph law record and fields.
- `memory_path_flow`, `memory_path_nil`, `memory_path_cons`, `memory_last_defs`,
  `memory_last_path` — path flow and last dynamic definition.
- `memory_edge_provenance`, `memory_edge_provenance_nil`, `memory_edge_provenance_cons`,
  `memory_provenance`, `memory_provenance_entry`, `memory_provenance_edge`,
  `memory_occurrence_history` — coupled static version and dynamic origin relations.
- `memory_path_correspondence`, `memory_occurrence_input_valid`,
  `memory_definition_before_occurrence`, `memory_execution_correspondence` — Theorems; graph,
  occurrence, provenance and concrete execution correspondence.

### `AnalysesMemoryFrontier.v` — ANA-10c

- `memory_dom_node`, `MemoryRoot`, `MemoryBlock`, `MemoryEdge`, `memory_dom_edge`, `MemoryStart`,
  `MemoryBegin`, `MemoryEnd` — split-edge graph identifiers.
- `memory_dom_node_encoding`, `memory_dom_edge_encoding`, `memory_dom_graph`, `memory_dom_defs`,
  `memory_frontier_build` — encodings, expanded graph, defining nodes and proved builder.
- `memory_dom_graph_wf`, `memory_dom_reachable`, `memory_frontier_phi_exact`,
  `memory_frontier_path` — Theorems; expansion, exact phi placement and path preservation.

### `AnalysesMemorySealed.v` — ANA-10d

- `memory_sealed_build` — Definition; directly proved sealed-block graph producer.
- `memory_sealed_path`, `memory_sealed_definition_before_occurrence` — Theorems; path and
  path-specific definition correspondence.

### `AnalysesMemoryWalk.v` — ANA-10e

- `memory_scopes_disjoint`, `memory_effect_has_read` — executable scope and read tests.
- `memory_scopes_disjoint_sound` — Theorem; a positive test excludes a common byte.
- `memory_walk_next`, `memory_walk_skip_def`, `memory_walk_phi`, `memory_walk_trace`,
  `memory_walk_single`, `memory_walk_cons`, `memory_trace_last`, `memory_walk_terminal` —
  declarative backward walk.
- `memory_clobber_result`, `MemoryClobberResult`, `clobber_roots`, `clobber_complete`,
  `memory_clobbers` — conservative finite query result and producer.
- `memory_clobbers_cover`, `memory_clobbers_complete`, `memory_clobbers_follow_execution` —
  Theorems; cut coverage, completed-walk exactness and dynamic provenance coverage.
- `memory_last_clobbers`, `memory_path_last_clobber` — path-specific last may-clobber.


### `AnalysesMemoryFlow.v` — ANA-10f

- `memory_version_encoding`, `memory_flow_facts`, `memory_flow_lattice`, `memory_flow_system`,
  `memory_flow_static`, `memory_flow_solve` — finite source system and total function result.
- `memory_flow_reaches`, `memory_flow_terminal`, `memory_flow_step` — finite source reachability.
- `memory_flow_least`, `memory_flow_exact`, `memory_flow_execution`,
  `memory_builders_flow_agree` — Theorems; leastness, reachability exactness and actual path
  source inclusion and agreement across builders.

### `AnalysesMemoryForward.v` — ANA-10f

- `memory_read_bytes` — Definition; increasing-address optional byte sequence.
- `memory_value_view`, `MemoryValueView`, `store_location`, `load_location`, `stored_value`,
  `loaded_value`, `decode_memory_value` — client value observation and decoding view.
- `memory_value_laws`, `Build_memory_value_laws`, `memory_value_byte_range`,
  `memory_store_encoding`, `memory_load_decoding` — concrete byte/value client laws.
- `memory_forward_value`, `memory_forward_projected` — Theorems; value equality for successful
  same-object, same-range accesses under the stated checked or directly projected condition.



<!-- C19 call names -->

### `AnalysesCallScc.v` — ANA-8a

- `call_index` — public declaration; see the call analysis contract.
- `CallIndex` — public declaration; see the call analysis contract.
- `indexed_targets` — public declaration; see the call analysis contract.
- `indexed_callers` — public declaration; see the call analysis contract.
- `prepare_calls` — public declaration; see the call analysis contract.
- `prepare_calls_targets` — public declaration; see the call analysis contract.
- `prepare_calls_callers` — public declaration; see the call analysis contract.
- `solve_scc_summaries` — public declaration; see the call analysis contract.
- `solve_scc_summaries_post` — public declaration; see the call analysis contract.
- `solve_scc_summaries_least` — public declaration; see the call analysis contract.
- `solve_scc_summaries_sound` — public declaration; see the call analysis contract.
- `reachable_context` — public declaration; see the call analysis contract.
- `context_root` — public declaration; see the call analysis contract.
- `context_call` — public declaration; see the call analysis contract.
- `solve_reachable_callstrings` — public declaration; see the call analysis contract.
- `reachable_callstrings_least` — public declaration; see the call analysis contract.
- `arg_facts_indexed` — public declaration; see the call analysis contract.
- `callers_index_wf` — public declaration; see the call analysis contract.
- `arg_facts_indexed_agrees` — public declaration; see the call analysis contract.

### `AnalysesInterprocedural.v` — ANA-8b

- `ip_kind` — public declaration; see the call analysis contract.
- `IpInternal` — public declaration; see the call analysis contract.
- `IpCall` — public declaration; see the call analysis contract.
- `IpReturn` — public declaration; see the call analysis contract.
- `ip_edge` — public declaration; see the call analysis contract.
- `IpEdge` — public declaration; see the call analysis contract.
- `ip_source` — public declaration; see the call analysis contract.
- `ip_target` — public declaration; see the call analysis contract.
- `ip_action` — public declaration; see the call analysis contract.
- `ip_pairs` — public declaration; see the call analysis contract.
- `ip_problem` — public declaration; see the call analysis contract.
- `IpProblem` — public declaration; see the call analysis contract.
- `ip_nodes` — public declaration; see the call analysis contract.
- `ip_sites` — public declaration; see the call analysis contract.
- `ip_facts` — public declaration; see the call analysis contract.
- `ip_edges` — public declaration; see the call analysis contract.
- `ip_problem_wf` — public declaration; see the call analysis contract.
- `ip_step` — public declaration; see the call analysis contract.
- `ip_step_internal` — public declaration; see the call analysis contract.
- `ip_step_call` — public declaration; see the call analysis contract.
- `ip_step_return` — public declaration; see the call analysis contract.
- `ip_path` — public declaration; see the call analysis contract.
- `ip_path_refl` — public declaration; see the call analysis contract.
- `ip_path_step` — public declaration; see the call analysis contract.
- `ifds_solve` — public declaration; see the call analysis contract.
- `ifds_solve_exact` — public declaration; see the call analysis contract.
- `ide_problem` — public declaration; see the call analysis contract.
- `IdeProblem` — public declaration; see the call analysis contract.
- `ide_graph` — public declaration; see the call analysis contract.
- `ide_lattice` — public declaration; see the call analysis contract.
- `ide_values` — public declaration; see the call analysis contract.
- `ide_weight` — public declaration; see the call analysis contract.
- `ide_laws` — public declaration; see the call analysis contract.
- `Build_ide_laws` — public declaration; see the call analysis contract.
- `ide_graph_wf` — public declaration; see the call analysis contract.
- `ide_value_finite` — public declaration; see the call analysis contract.
- `ide_lat_laws` — public declaration; see the call analysis contract.
- `ide_lub_laws` — public declaration; see the call analysis contract.
- `ide_distributive` — public declaration; see the call analysis contract.
- `ide_path` — public declaration; see the call analysis contract.
- `ide_path_refl` — public declaration; see the call analysis contract.
- `ide_path_step` — public declaration; see the call analysis contract.
- `ide_solve` — public declaration; see the call analysis contract.
- `ide_solve_exact` — public declaration; see the call analysis contract.

### `AnalysesCallEffects.v` — ANA-8c

- `return_projection` — public declaration; see the call analysis contract.
- `ReturnProjection` — public declaration; see the call analysis contract.
- `return_config` — public declaration; see the call analysis contract.
- `normal_return` — public declaration; see the call analysis contract.
- `return_projection_laws` — public declaration; see the call analysis contract.
- `Build_return_projection_laws` — public declaration; see the call analysis contract.
- `return_local_step` — public declaration; see the call analysis contract.
- `return_exit` — public declaration; see the call analysis contract.
- `may_return` — public declaration; see the call analysis contract.
- `may_return_sound` — public declaration; see the call analysis contract.
- `modref` — public declaration; see the call analysis contract.
- `ModRef` — public declaration; see the call analysis contract.
- `mr_reads` — public declaration; see the call analysis contract.
- `mr_writes` — public declaration; see the call analysis contract.
- `mr_allocates` — public declaration; see the call analysis contract.
- `mr_frees` — public declaration; see the call analysis contract.
- `mr_orders` — public declaration; see the call analysis contract.
- `mr_contains` — public declaration; see the call analysis contract.
- `unknown_modref` — public declaration; see the call analysis contract.
- `modref_lattice` — public declaration; see the call analysis contract.
- `modref_lattice_laws` — public declaration; see the call analysis contract.
- `modref_lattice_height` — public declaration; see the call analysis contract.
- `modref_spec` — public declaration; see the call analysis contract.
- `effect_observer` — public declaration; see the call analysis contract.
- `EffectObserver` — public declaration; see the call analysis contract.
- `actual_reads` — public declaration; see the call analysis contract.
- `actual_writes` — public declaration; see the call analysis contract.
- `actual_allocates` — public declaration; see the call analysis contract.
- `actual_frees` — public declaration; see the call analysis contract.
- `actual_orders` — public declaration; see the call analysis contract.
- `modref_covers` — public declaration; see the call analysis contract.
- `modref_local_laws` — public declaration; see the call analysis contract.
- `Build_modref_local_laws` — public declaration; see the call analysis contract.
- `modref_local_step` — public declaration; see the call analysis contract.
- `modref_sound` — public declaration; see the call analysis contract.

### `AnalysesSeg.v` — ANA-14

- `seg_event` — public declaration; see the SEG contract.
- `seg_bit_transfer` — public declaration; see the SEG contract.
- `seg_must_lattice` — public declaration; see the SEG contract.
- `seg_index` — public declaration; see the SEG contract.
- `SegIndex` — public declaration; see the SEG contract.
- `seg_graph` — public declaration; see the SEG contract.
- `seg_paths` — public declaration; see the SEG contract.
- `seg_interiors` — public declaration; see the SEG contract.
- `seg_forward_summary` — public declaration; see the SEG contract.
- `seg_backward_summary` — public declaration; see the SEG contract.
- `seg_path` — public declaration; see the SEG contract.
- `seg_internal_nodes` — public declaration; see the SEG contract.
- `seg_index_laws` — public declaration; see the SEG contract.
- `seg_wf` — public declaration; see the SEG contract.
- `seg_entries` — public declaration; see the SEG contract.
- `seg_nodes_original` — public declaration; see the SEG contract.
- `seg_boundaries` — public declaration; see the SEG contract.
- `seg_junctions` — public declaration; see the SEG contract.
- `seg_event_endpoints` — public declaration; see the SEG contract.
- `seg_path_valid` — public declaration; see the SEG contract.
- `seg_path_nodup` — public declaration; see the SEG contract.
- `seg_internal_nodup` — public declaration; see the SEG contract.
- `seg_internal_lookup` — public declaration; see the SEG contract.
- `seg_edge_partition` — public declaration; see the SEG contract.
- `seg_no_event_inside` — public declaration; see the SEG contract.
- `seg_interior_unique` — public declaration; see the SEG contract.
- `seg_interior_only` — public declaration; see the SEG contract.
- `seg_interior_degree` — public declaration; see the SEG contract.
- `build_expression_seg` — public declaration; see the SEG contract.
- `seg_summary_apply` — public declaration; see the SEG contract.
- `seg_forward_transfer` — public declaration; see the SEG contract.
- `seg_backward_transfer` — public declaration; see the SEG contract.
- `seg_available_system` — public declaration; see the SEG contract.
- `seg_busy_system` — public declaration; see the SEG contract.
- `seg_reconstruct_available` — public declaration; see the SEG contract.
- `seg_reconstruct_busy` — public declaration; see the SEG contract.
- `seg_available` — public declaration; see the SEG contract.
- `seg_busy` — public declaration; see the SEG contract.
- `seg_must_laws` — public declaration; see the SEG contract.
- `seg_must_lub` — public declaration; see the SEG contract.
- `seg_bit_distributive` — public declaration; see the SEG contract.
- `build_expression_seg_correct` — public declaration; see the SEG contract.
- `build_expression_seg_summaries` — public declaration; see the SEG contract.
- `seg_available_exact` — public declaration; see the SEG contract.
- `seg_busy_exact` — public declaration; see the SEG contract.


<!-- C19 SSA PRE names -->

### `AnalysesSsaPreGraph.v` — ANA-16

`frg_defs` and `frg_phi_needed` take explicit block and expression encodings;
`frg_phi_sites` and its exactness theorem also take block-edge and variable encodings.

- `pre_expression_view` — public declaration; see the SSA PRE contract.
- `PreExpressionView` — public declaration; see the SSA PRE contract.
- `pre_genkill` — public declaration; see the SSA PRE contract.
- `pre_total_pure` — public declaration; see the SSA PRE contract.
- `pre_recomputed` — public declaration; see the SSA PRE contract.
- `pre_expr_ssa` — public declaration; see the SSA PRE contract.
- `PreExprSsa` — public declaration; see the SSA PRE contract.
- `pre_ssa_points` — public declaration; see the SSA PRE contract.
- `pre_ssa_view` — public declaration; see the SSA PRE contract.
- `pre_expression` — public declaration; see the SSA PRE contract.
- `pre_seed_expressions` — public declaration; see the SSA PRE contract.
- `pre_value_universe` — public declaration; see the SSA PRE contract.
- `pre_expression_shape` — public declaration; see the SSA PRE contract.
- `pre_operands` — public declaration; see the SSA PRE contract.
- `pre_expr_eval` — public declaration; see the SSA PRE contract.
- `pre_phi_translate` — public declaration; see the SSA PRE contract.
- `pre_initial_available` — public declaration; see the SSA PRE contract.
- `pre_exit_point` — public declaration; see the SSA PRE contract.
- `pre_expr_in_family` — public declaration; see the SSA PRE contract.
- `pre_family_seed` — public declaration; see the SSA PRE contract.
- `pre_family_translate` — public declaration; see the SSA PRE contract.
- `pre_expr_universe` — public declaration; see the SSA PRE contract.
- `pre_phi_env` — public declaration; see the SSA PRE contract.
- `pre_phi_operand` — public declaration; see the SSA PRE contract.
- `pre_point_edge_index` — public declaration; see the SSA PRE contract.
- `pre_expr_ssa_laws` — public declaration; see the SSA PRE contract.
- `pre_expr_points` — public declaration; see the SSA PRE contract.
- `pre_expr_strict` — public declaration; see the SSA PRE contract.
- `pre_expr_block_graph` — public declaration; see the SSA PRE contract.
- `pre_expr_point_graph` — public declaration; see the SSA PRE contract.
- `pre_expr_reachable_blocks` — public declaration; see the SSA PRE contract.
- `pre_expr_reachable_points` — public declaration; see the SSA PRE contract.
- `pre_expr_entry_position` — public declaration; see the SSA PRE contract.
- `pre_expr_entry_no_incoming` — public declaration; see the SSA PRE contract.
- `pre_expr_params_nodup` — public declaration; see the SSA PRE contract.
- `pre_expr_value_nodup` — public declaration; see the SSA PRE contract.
- `pre_expr_occurrences` — public declaration; see the SSA PRE contract.
- `pre_expr_initial_in_family` — public declaration; see the SSA PRE contract.
- `pre_expr_finite_operands` — public declaration; see the SSA PRE contract.
- `pre_expr_shape_identity` — public declaration; see the SSA PRE contract.
- `pre_expr_shape_arity` — public declaration; see the SSA PRE contract.
- `pre_expr_runtime` — public declaration; see the SSA PRE contract.
- `pre_expr_operand_support` — public declaration; see the SSA PRE contract.
- `pre_expr_kill_operand` — public declaration; see the SSA PRE contract.
- `pre_expr_def_home` — public declaration; see the SSA PRE contract.
- `pre_expr_cross_no_defs` — public declaration; see the SSA PRE contract.
- `pre_expr_real_internal` — public declaration; see the SSA PRE contract.
- `pre_expr_closed_translation` — public declaration; see the SSA PRE contract.
- `pre_expr_translation_shape` — public declaration; see the SSA PRE contract.
- `pre_expr_translation_operands` — public declaration; see the SSA PRE contract.
- `pre_expr_translation_pure` — public declaration; see the SSA PRE contract.
- `pre_expr_translation_eval` — public declaration; see the SSA PRE contract.
- `frg_defs` — public declaration; see the SSA PRE contract.
- `frg_phi_needed` — public declaration; see the SSA PRE contract.
- `frg_phi_seed` — public declaration; see the SSA PRE contract.
- `frg_phi_operand_param` — constructor; Seeds a family expression at a listed non-entry
  block that has one of its operands as a block parameter.
- `frg_phi_iter` — public declaration; see the SSA PRE contract.
- `frg_phi_translate_seed` — public declaration; see the SSA PRE contract.
- `frg_phi_sites` — public declaration; see the SSA PRE contract.
- `pre_expr_universe_exact` — public declaration; see the SSA PRE contract.
- `frg_phi_sites_exact` — public declaration; see the SSA PRE contract.
- `pre_phi_env_parameter` — public declaration; see the SSA PRE contract.
- `pre_point_edge_index_exact` — public declaration; see the SSA PRE contract.
- `pre_phi_env_frame` — public declaration; see the SSA PRE contract.
- `pre_phi_env_substitution` — public declaration; see the SSA PRE contract.
- `frg_translation_agrees` — public declaration; see the SSA PRE contract.
- `frg_version` — public declaration; see the SSA PRE contract.
- `FrUnavailable` — public declaration; see the SSA PRE contract.
- `FrInitial` — public declaration; see the SSA PRE contract.
- `FrFresh` — public declaration; see the SSA PRE contract.
- `FrPhi` — public declaration; see the SSA PRE contract.
- `frg_operand` — public declaration; see the SSA PRE contract.
- `FrgOperand` — public declaration; see the SSA PRE contract.
- `frg_operand_version` — public declaration; see the SSA PRE contract.
- `frg_operand_real_use` — public declaration; see the SSA PRE contract.
- `factored_redundancy_graph` — public declaration; see the SSA PRE contract.
- `FactoredRedundancyGraph` — public declaration; see the SSA PRE contract.
- `frg_versions` — public declaration; see the SSA PRE contract.
- `frg_occurrence_index` — public declaration; see the SSA PRE contract.
- `frg_fresh_index` — public declaration; see the SSA PRE contract.
- `frg_phi_index` — public declaration; see the SSA PRE contract.
- `frg_phi_operands` — public declaration; see the SSA PRE contract.
- `frg_unsafe_seeds` — public declaration; see the SSA PRE contract.
- `frg_version_encoding` — public declaration; see the SSA PRE contract.
- `frg_version_expr` — public declaration; see the SSA PRE contract.
- `frg_version_point` — public declaration; see the SSA PRE contract.
- `frg_nearest_version` — public declaration; see the SSA PRE contract.
- `frg_no_dominating_real_use` — public declaration; see the SSA PRE contract.
- `frg_reusable` — public declaration; see the SSA PRE contract.
- `frg_wf` — public declaration; see the SSA PRE contract.
- `frg_versions_nodup` — public declaration; see the SSA PRE contract.
- `frg_versions_exact` — public declaration; see the SSA PRE contract.
- `frg_phi_exact` — public declaration; see the SSA PRE contract.
- `frg_occurrence_exact` — public declaration; see the SSA PRE contract.
- `frg_occurrence_domain` — public declaration; see the SSA PRE contract.
- `frg_fresh_exact` — public declaration; see the SSA PRE contract.
- `frg_fresh_domain` — public declaration; see the SSA PRE contract.
- `frg_fresh_required` — public declaration; see the SSA PRE contract.
- `frg_operand_exact` — public declaration; see the SSA PRE contract.
- `frg_operand_domain` — public declaration; see the SSA PRE contract.
- `frg_operand_selection` — public declaration; see the SSA PRE contract.
- `frg_operand_real_use_exact` — public declaration; see the SSA PRE contract.
- `frg_down_seed_exact` — public declaration; see the SSA PRE contract.
- `build_frg` — public declaration; see the SSA PRE contract.
- `build_frg_wf` — public declaration; see the SSA PRE contract.

### `AnalysesSsaPre.v` — ANA-15

- `pre_version` — public declaration; see the SSA PRE contract.
- `PreInitial` — public declaration; see the SSA PRE contract.
- `PreComputed` — public declaration; see the SSA PRE contract.
- `PreInserted` — public declaration; see the SSA PRE contract.
- `PreMerged` — public declaration; see the SSA PRE contract.
- `pre_version_expr` — public declaration; see the SSA PRE contract.
- `pre_plan` — public declaration; see the SSA PRE contract.
- `PrePlan` — public declaration; see the SSA PRE contract.
- `pre_insertions` — public declaration; see the SSA PRE contract.
- `pre_deletions` — public declaration; see the SSA PRE contract.
- `pre_reload_versions` — public declaration; see the SSA PRE contract.
- `pre_phi_versions` — public declaration; see the SSA PRE contract.
- `pre_inserted` — public declaration; see the SSA PRE contract.
- `pre_deleted` — public declaration; see the SSA PRE contract.
- `pre_extended_view` — public declaration; see the SSA PRE contract.
- `pre_version_point` — public declaration; see the SSA PRE contract.
- `pre_version_written` — public declaration; see the SSA PRE contract.
- `pre_phi_update` — public declaration; see the SSA PRE contract.
- `pre_placement_legal` — public declaration; see the SSA PRE contract.
- `ssapre_facts` — public declaration; see the SSA PRE contract.
- `SsaPreFacts` — public declaration; see the SSA PRE contract.
- `ssapre_downsafe` — public declaration; see the SSA PRE contract.
- `ssapre_can_available` — public declaration; see the SSA PRE contract.
- `ssapre_later` — public declaration; see the SSA PRE contract.
- `live_bool_get` — public declaration; see the SSA PRE contract.
- `ssapre_down_unsafe` — public declaration; see the SSA PRE contract.
- `ssapre_down_seed` — public declaration; see the SSA PRE contract.
- `ssapre_down_step` — public declaration; see the SSA PRE contract.
- `ssapre_cannot` — public declaration; see the SSA PRE contract.
- `ssapre_cannot_seed` — public declaration; see the SSA PRE contract.
- `ssapre_cannot_step` — public declaration; see the SSA PRE contract.
- `ssapre_later_reset` — public declaration; see the SSA PRE contract.
- `ssapre_later_seed` — public declaration; see the SSA PRE contract.
- `ssapre_later_step` — public declaration; see the SSA PRE contract.
- `solve_ssapre` — public declaration; see the SSA PRE contract.
- `ssa_pre_place` — public declaration; see the SSA PRE contract.
- `solve_ssapre_exact` — public declaration; see the SSA PRE contract.
- `ssa_pre_place_legal` — public declaration; see the SSA PRE contract.
- `ssa_pre_phi_versions_correct` — public declaration; see the SSA PRE contract.

### `AnalysesSsaPreSemantics.v` — ANA-15

- `pre_origin` — public declaration; see the SSA PRE contract.
- `PrePoint` — public declaration; see the SSA PRE contract.
- `PreOnEdge` — public declaration; see the SSA PRE contract.
- `pre_realizer` — public declaration; see the SSA PRE contract.
- `PreRealizer` — public declaration; see the SSA PRE contract.
- `pre_source` — public declaration; see the SSA PRE contract.
- `pre_source_end` — public declaration; see the SSA PRE contract.
- `pre_source_graph` — public declaration; see the SSA PRE contract.
- `pre_target` — public declaration; see the SSA PRE contract.
- `pre_target_end` — public declaration; see the SSA PRE contract.
- `pre_target_graph` — public declaration; see the SSA PRE contract.
- `pre_origin_of` — public declaration; see the SSA PRE contract.
- `pre_project_edge` — public declaration; see the SSA PRE contract.
- `pre_eval` — public declaration; see the SSA PRE contract.
- `pre_cached` — public declaration; see the SSA PRE contract.
- `pre_core_agree` — public declaration; see the SSA PRE contract.
- `pre_measure` — public declaration; see the SSA PRE contract.
- `pre_cache_agree` — public declaration; see the SSA PRE contract.
- `pre_boundary` — public declaration; see the SSA PRE contract.
- `pre_exit_covered` — public declaration; see the SSA PRE contract.
- `pre_phi_source_laws` — public declaration; see the SSA PRE contract.
- `pre_admin` — public declaration; see the SSA PRE contract.
- `pre_finish` — public declaration; see the SSA PRE contract.
- `pre_finish_boundary` — public declaration; see the SSA PRE contract.
- `pre_finish_admin` — public declaration; see the SSA PRE contract.
- `pre_macro_step` — public declaration; see the SSA PRE contract.
- `pre_paired_run` — public declaration; see the SSA PRE contract.
- `pre_paired_initial` — public declaration; see the SSA PRE contract.
- `pre_paired_step` — public declaration; see the SSA PRE contract.
- `pre_local_laws` — public declaration; see the SSA PRE contract.
- `pre_local_graph` — public declaration; see the SSA PRE contract.
- `pre_local_operands` — public declaration; see the SSA PRE contract.
- `pre_local_gen_value` — public declaration; see the SSA PRE contract.
- `pre_local_kill_frame` — public declaration; see the SSA PRE contract.
- `pre_local_kept` — public declaration; see the SSA PRE contract.
- `pre_local_insert` — public declaration; see the SSA PRE contract.
- `pre_local_replace` — public declaration; see the SSA PRE contract.
- `pre_local_cache_frame` — public declaration; see the SSA PRE contract.
- `pre_local_compute` — public declaration; see the SSA PRE contract.
- `pre_local_initial` — public declaration; see the SSA PRE contract.
- `pre_local_phi_select` — public declaration; see the SSA PRE contract.
- `pre_local_progress` — public declaration; see the SSA PRE contract.
- `pre_local_endings` — public declaration; see the SSA PRE contract.
- `ssa_pre_cache_invariant` — public declaration; see the SSA PRE contract.
- `ssa_pre_semantics` — public declaration; see the SSA PRE contract.

### `DomainsSignedBounds.v` — DOM-9

- `sb_half`, `SBEmpty`, `SBRange` — Inductive type and constructors; one sign hemisphere.
- `signed_bounds`, `SignedBounds`, `sb_zero`, `sb_one` — Record, constructor and fields.
- `sb_bit_gamma`, `sb_interval_gamma`, `sb_half_gamma`, `signed_bounds_gamma` — Definitions; meanings.
- `sb_reduce_half`, `signed_bounds_reduce` — Definitions; exact component hull reduction.
- `sb_reduce_half_gamma`, `sb_reduce_half_idempotent`, `sb_reduce_half_hulls` — Theorems.
- `sb_reduce_half_interval_hull`, `signed_bounds_reduce_gamma` — Theorems.
- `signed_bounds_reduce_idempotent` — Theorem.

### `DomainsSignedBoundsDomain.v` — DOM-9

- `signed_bounds_lattice`, `signed_bounds_wrank` — Definitions; lattice and widening rank.
- `signed_bounds_domain`, `signed_bounds_classic_domain`, `signed_bounds_numeric`,
  `signed_bounds_capped` — Definitions; domains.
- `signed_bounds_laws`, `signed_bounds_word_laws`, `signed_bounds_classic_word_laws`,
  `signed_bounds_numeric_laws` — Theorems.
- `signed_bounds_capped_laws` — Theorem.
- `signed_bounds_query` — Definition; reduced per-sign bit and bound query.
- `signed_bounds_query_sound`, `signed_bounds_query_empty`, `signed_bounds_query_bounds_exact` — Theorems.

<!-- AUD-API-IDE-PRE-NAMES-BEGIN -->

## Audit IDE and PRE names

The [analysis contract](analyses.md) fixes each exact definition and theorem type.
The following entries include exported constructors and record projections.

### `Galois.Analyses.AnalysesAuditIde`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIde.v`.

- `audit_ide_actual_generated_source` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_actual_generated_source_statement` — Definition.
- `audit_ide_actual_legacy_source` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_actual_legacy_source_statement` — Definition.
- `audit_ide_actual_legacy_whole_bound` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_actual_legacy_whole_bound_statement` — Definition.
- `audit_ide_caller_source` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_caller_source_statement` — Definition.
- `audit_ide_derived_encoding_adequacy` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_derived_encoding_adequacy_statement` — Definition.
- `audit_ide_encoding_body_receipts` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_encoding_body_receipts_statement` — Definition.
- `audit_ide_full_source` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_full_source_statement` — Definition.
- `audit_ide_generated_body_family` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_generated_body_family_statement` — Definition.
- `audit_ide_generated_family` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_generated_family_statement` — Definition.
- `audit_ide_horn_implementation_adequacy` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_horn_implementation_adequacy_statement` — Definition.
- `audit_ide_horn_rule_encoding_adequacy` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_horn_rule_encoding_adequacy_statement` — Definition.
- `audit_ide_implementation_adequacy` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_implementation_adequacy_statement` — Definition.
- `audit_ide_legacy_body_family` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_legacy_body_family_statement` — Definition.
- `audit_ide_legacy_family` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_legacy_family_statement` — Definition.
- `audit_ide_legacy_implementation_adequacy` — future Theorem in `AnalysesAuditIdeAdequacy`; owner
  AUD-IDE.
- `audit_ide_legacy_implementation_adequacy_statement` — Definition.
- `audit_ide_selector_body_family` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_selector_body_family_statement` — Definition.
- `audit_ide_selector_full_source` — future Theorem in `AnalysesAuditIdeAdequacy`; owner AUD-IDE.
- `audit_ide_selector_full_source_statement` — Definition.
- `ide_actual_fact_encoding_source` — Definition.
- `ide_actual_kind_encoding_source` — Definition.
- `ide_fact_encoding_receipts` — Definition.
- `ide_fact_expanded_source` — Definition.
- `ide_fact_source_encoding` — Definition.
- `ide_fact_source_encoding_work` — Definition.
- `ide_generated_actual_body_budget` — Definition.
- `ide_generated_actual_source` — Definition.
- `ide_generator_actual_body_budget` — Definition.
- `ide_generator_actual_source` — Definition.
- `ide_horn_actual_body_budget` — Definition.
- `ide_horn_actual_source` — Definition.
- `ide_horn_execution_body_receipts` — Definition.
- `ide_horn_literal_call_work` — Definition.
- `ide_horn_literal_work` — Definition.
- `ide_horn_preparation_budget` — Definition.
- `ide_horn_preparation_source` — Definition.
- `ide_horn_queue_actual_source` — Definition.
- `ide_horn_rule_expanded_source` — Definition.
- `ide_horn_rule_source_encoding` — Definition.
- `ide_horn_rule_source_encoding_work` — Definition.
- `ide_initial_actual_body_budget` — Definition.
- `ide_initial_actual_source` — Definition.
- `ide_legacy_actual_body_budget` — Definition.
- `ide_legacy_actual_fact_source` — Definition.
- `ide_legacy_actual_kind_source` — Definition.
- `ide_legacy_actual_lifted_source` — Definition.
- `ide_legacy_actual_reach_source` — Definition.
- `ide_legacy_actual_source` — Definition.
- `ide_legacy_actual_vector_source` — Definition.
- `ide_legacy_actual_vertex_source` — Definition.
- `ide_legacy_input_actual_source` — Definition.
- `ide_legacy_input_body_budget` — Definition.
- `ide_legacy_kind_body_allowance` — Definition.
- `ide_legacy_literal_event_work` — Definition.
- `ide_legacy_literal_work` — Definition.
- `ide_legacy_same_run_events` — Definition.
- `ide_legacy_table_actual_source` — Definition.
- `ide_legacy_table_body_budget` — Definition.
- `ide_legacy_total_body_allowance` — Definition.
- `ide_lifted_encoding_receipts` — Definition.
- `ide_lifted_source_encoding` — Definition.
- `ide_lifted_source_encoding_work` — Definition.
- `ide_machine_actual_body_budget` — Definition.
- `ide_machine_actual_source` — Definition.
- `ide_nested_receipts` — Definition.
- `ide_option_encoding_receipts` — Definition.
- `ide_option_expanded_source` — Definition.
- `ide_pair_key_expanded_source` — Definition.
- `ide_receipt_leaf` — Definition.
- `ide_recorded_map_budget` — Definition.
- `ide_recorded_map_source` — Definition.
- `ide_rule_tail_expanded_source` — Definition.
- `ide_triple_key_expanded_source` — Definition.
- `ide_value_list_encoding_receipts` — Definition.
- `ide_vertex_encoding_receipts` — Definition.
- `ide_vertex_expanded_source` — Definition.
- `ide_vertex_pair_encoding_receipts` — Definition.
- `ide_vertex_pair_expanded_source` — Definition.
- `ide_vertex_source_encoding` — Definition.
- `ide_vertex_source_encoding_work` — Definition.

### `Galois.Analyses.AnalysesAuditIdeBase`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIdeBase.v`.

- `AuditIdeArc` — constructor.
- `AuditIdeBinary` — constructor.
- `AuditIdeDerivedCons` — constructor.
- `AuditIdeDerivedFirst` — constructor.
- `AuditIdeDerivedGrow` — constructor.
- `AuditIdeDerivedNil` — constructor.
- `AuditIdeFiniteLegacy` — constructor.
- `AuditIdeFiniteSelection` — constructor.
- `AuditIdeFirst` — constructor.
- `AuditIdeGenerated` — constructor.
- `AuditIdeGeneratedCall` — constructor.
- `AuditIdeGeneratedIdentity` — constructor.
- `AuditIdeGeneratedInternal` — constructor.
- `AuditIdeGeneratedMatched` — constructor.
- `AuditIdeGeneratedPrefix` — constructor.
- `AuditIdeGeneratedRoot` — constructor.
- `AuditIdeGrow` — constructor.
- `AuditIdeMachine` — constructor.
- `AuditIdeMachineNext` — constructor.
- `AuditIdeMachineRefl` — constructor.
- `AuditIdeMachineTraceCons` — constructor.
- `AuditIdeMachineTraceNil` — constructor.
- `AuditIdeProbe` — constructor.
- `AuditIdeProbeCons` — constructor.
- `AuditIdeProbeDisabled` — constructor.
- `AuditIdeProbeFirst` — constructor.
- `AuditIdeProbeGrow` — constructor.
- `AuditIdeProbeNil` — constructor.
- `AuditIdeProbeStable` — constructor.
- `AuditIdeRegistry` — constructor.
- `AuditIdeSeed` — constructor.
- `AuditIdeSummary` — constructor.
- `AuditIdeTraceCons` — constructor.
- `AuditIdeTraceNil` — constructor.
- `AuditIdeUnary` — constructor.
- `IdeBodyCompose` — constructor.
- `IdeBodyEqual` — constructor.
- `IdeBodyEval` — constructor.
- `IdeBodyJoin` — constructor.
- `IdeRegistryAdapters` — constructor.
- `IdeRegistrySummary` — constructor.
- `audit_ide_arc` — Record.
- `audit_ide_arc_count` — Definition.
- `audit_ide_arc_from` — projection.
- `audit_ide_arc_kind` — projection.
- `audit_ide_arc_to` — projection.
- `audit_ide_arc_weight` — projection.
- `audit_ide_arcs` — Definition.
- `audit_ide_bound` — projection.
- `audit_ide_call_occurrences` — Definition.
- `audit_ide_compose` — projection.
- `audit_ide_composition` — projection.
- `audit_ide_congruence_laws` — Record.
- `audit_ide_derived_bound` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_derived_bound_statement` — Definition.
- `audit_ide_derived_trace` — Inductive.
- `audit_ide_derived_update` — Inductive.
- `audit_ide_dictionary_body` — Inductive.
- `audit_ide_dictionary_body_budget` — Definition.
- `audit_ide_dictionary_body_valid` — Definition.
- `audit_ide_dictionary_body_work` — Definition.
- `audit_ide_dictionary_invocation` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_dictionary_invocation_statement` — Definition.
- `audit_ide_distributes` — projection.
- `audit_ide_enqueue` — Definition.
- `audit_ide_eq_spec` — projection.
- `audit_ide_equal` — projection.
- `audit_ide_eval` — projection.
- `audit_ide_eval_proper` — projection.
- `audit_ide_finite_compatible_check` — Definition.
- `audit_ide_finite_path_equal` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_finite_path_equal_statement` — Definition.
- `audit_ide_finite_selection` — Record.
- `audit_ide_generated_rule` — Inductive.
- `audit_ide_graph_encoding_adapters` — Record.
- `audit_ide_graph_encoding_laws` — Definition.
- `audit_ide_id` — projection.
- `audit_ide_identity` — projection.
- `audit_ide_incidence_visits` — Definition.
- `audit_ide_incidence_visits_bound` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_incidence_visits_bound_statement` — Definition.
- `audit_ide_internal_occurrences` — Definition.
- `audit_ide_join` — projection.
- `audit_ide_lattice_laws` — projection.
- `audit_ide_legacy_adapter_laws` — Definition.
- `audit_ide_legacy_adapters` — Record.
- `audit_ide_legacy_query` — Definition.
- `audit_ide_lub_laws` — projection.
- `audit_ide_machine` — Record.
- `audit_ide_machine_closed` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_machine_closed_statement` — Definition.
- `audit_ide_machine_fuel` — Definition.
- `audit_ide_machine_incidence` — projection.
- `audit_ide_machine_incidence_correspondence` — future Theorem in `AnalysesAuditIdeBaseAdequacy`;
  owner AUD-IDE-BASE.
- `audit_ide_machine_incidence_correspondence_statement` — Definition.
- `audit_ide_machine_initial` — Definition.
- `audit_ide_machine_initial_holds` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_machine_initial_statement` — Definition.
- `audit_ide_machine_keys_valid` — Definition.
- `audit_ide_machine_loop` — Fixpoint.
- `audit_ide_machine_loop_trace` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_machine_loop_trace_statement` — Definition.
- `audit_ide_machine_pending` — projection.
- `audit_ide_machine_probes_rev` — projection.
- `audit_ide_machine_queued` — projection.
- `audit_ide_machine_reaches` — Inductive.
- `audit_ide_machine_rules` — projection.
- `audit_ide_machine_step` — Definition.
- `audit_ide_machine_step_holds` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_machine_step_statement` — Definition.
- `audit_ide_machine_table` — projection.
- `audit_ide_machine_terminates` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_machine_terminates_statement` — Definition.
- `audit_ide_machine_trace` — Inductive.
- `audit_ide_machine_valid` — Definition.
- `audit_ide_machine_values` — projection.
- `audit_ide_matching_occurrences` — Definition.
- `audit_ide_nat_lattice` — Definition.
- `audit_ide_nat_laws` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner AUD-IDE-BASE.
- `audit_ide_nat_laws_statement` — Definition.
- `audit_ide_nat_nonfinite` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_nat_nonfinite_statement` — Definition.
- `audit_ide_nat_registry` — Definition.
- `audit_ide_occurrence_rule_count` — Definition.
- `audit_ide_old_weights_proper` — Definition.
- `audit_ide_pointwise_join` — projection.
- `audit_ide_probe` — Record.
- `audit_ide_probe_changed` — projection.
- `audit_ide_probe_compose_count` — Definition.
- `audit_ide_probe_existing` — projection.
- `audit_ide_probe_join_count` — Definition.
- `audit_ide_probe_key` — projection.
- `audit_ide_probe_projection` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_probe_projection_statement` — Definition.
- `audit_ide_probe_rule` — projection.
- `audit_ide_probe_step` — Inductive.
- `audit_ide_probe_trace` — Inductive.
- `audit_ide_probe_updates` — Definition.
- `audit_ide_public_equal_weight_paths` — Definition.
- `audit_ide_public_equivalent_weight_paths` — Definition.
- `audit_ide_public_incidence_counts` — Definition.
- `audit_ide_public_view` — Definition.
- `audit_ide_query_cost` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner AUD-IDE-BASE.
- `audit_ide_query_cost_statement` — Definition.
- `audit_ide_query_eval_calls` — Definition.
- `audit_ide_query_key_bits` — Definition.
- `audit_ide_rank` — projection.
- `audit_ide_rank_bounded` — projection.
- `audit_ide_rank_progress` — projection.
- `audit_ide_registry` — Record.
- `audit_ide_registry_adapter_laws` — Definition.
- `audit_ide_registry_adapters` — Record.
- `audit_ide_registry_laws` — Record.
- `audit_ide_rule` — Inductive.
- `audit_ide_rule_budget` — Definition.
- `audit_ide_rule_incidence` — Definition.
- `audit_ide_rule_keys` — Definition.
- `audit_ide_rule_result` — Definition.
- `audit_ide_rule_sources` — Definition.
- `audit_ide_rule_spec` — Definition.
- `audit_ide_rule_spec_length` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_rule_spec_length_statement` — Definition.
- `audit_ide_rule_spec_membership` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_rule_spec_membership_statement` — Definition.
- `audit_ide_rule_table` — Definition.
- `audit_ide_rule_universe` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_rule_universe_statement` — Definition.
- `audit_ide_rules_closed` — Definition.
- `audit_ide_selected_backend` — Inductive.
- `audit_ide_selected_mode` — projection.
- `audit_ide_selected_query` — projection.
- `audit_ide_stream` — Definition.
- `audit_ide_stream_bottom_statement` — Definition.
- `audit_ide_stream_consumer_statement` — Definition.
- `audit_ide_stream_graph` — Definition.
- `audit_ide_stream_join` — Definition.
- `audit_ide_stream_lattice` — Definition.
- `audit_ide_stream_laws` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner AUD-IDE-BASE.
- `audit_ide_stream_laws_statement` — Definition.
- `audit_ide_stream_registry` — Definition.
- `audit_ide_stream_two_observations` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_stream_two_observations_statement` — Definition.
- `audit_ide_stream_uncountable` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_stream_uncountable_statement` — Definition.
- `audit_ide_stream_weight` — Definition.
- `audit_ide_strong_finite_registry_exists` — future Theorem in `AnalysesAuditIdeBaseAdequacy`;
  owner AUD-IDE-BASE.
- `audit_ide_strong_finite_registry_exists_statement` — Definition.
- `audit_ide_strong_path_correspondence` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_strong_path_correspondence_statement` — Definition.
- `audit_ide_summary` — Record.
- `audit_ide_summary_events` — projection.
- `audit_ide_summary_keys` — Definition.
- `audit_ide_summary_keys_holds` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_summary_keys_statement` — Definition.
- `audit_ide_summary_map` — projection.
- `audit_ide_summary_probes` — projection.
- `audit_ide_summary_query` — Definition.
- `audit_ide_summary_updates` — projection.
- `audit_ide_transition_incidence_visits` — Definition.
- `audit_ide_update` — Inductive.
- `audit_ide_update_trace` — Inductive.
- `audit_ide_updates_bound` — future Theorem in `AnalysesAuditIdeBaseAdequacy`; owner
  AUD-IDE-BASE.
- `audit_ide_updates_bound_statement` — Definition.
- `audit_ide_weight_adapter` — Definition.
- `ide_compose_adapter` — projection.
- `ide_compose_with_body` — Definition.
- `ide_equal_adapter` — projection.
- `ide_equal_with_body` — Definition.
- `ide_eval_adapter` — projection.
- `ide_eval_with_body` — Definition.
- `ide_fact_encoding_adapter` — projection.
- `ide_join_adapter` — projection.
- `ide_join_with_body` — Definition.
- `ide_lattice_join_adapter` — projection.
- `ide_lattice_order_adapter` — projection.
- `ide_legacy_graph_encoding` — projection.
- `ide_legacy_weight_adapter` — projection.
- `ide_node_encoding_adapter` — projection.
- `ide_registry` — Definition.
- `ide_registry_congruence_laws` — Definition.
- `ide_registry_generate` — Definition.
- `ide_registry_laws` — Definition.
- `ide_registry_path` — Definition.
- `ide_registry_query` — Definition.
- `ide_registry_summary` — Record.
- `ide_registry_summary_map` — projection.
- `ide_registry_summary_probes` — projection.
- `ide_site_encoding_adapter` — projection.
- `ide_value_encoding_adapter` — projection.

### `Galois.Analyses.AnalysesAuditIdeGenerated`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIdeGenerated.v`.

- `IdeSourceEval` — constructor.
- `IdeSourceFact` — constructor.
- `IdeSourceFuel` — constructor.
- `IdeSourceGenerator` — constructor.
- `IdeSourceInitial` — constructor.
- `IdeSourceLe` — constructor.
- `IdeSourceMachine` — constructor.
- `IdeSourceOldWeight` — constructor.
- `IdeSourceWeight` — constructor.
- `audit_ide_generated_full_source` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`; owner
  AUD-IDE-GEN.
- `audit_ide_generated_full_source_statement` — Definition.
- `audit_ide_generated_query_source` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`;
  owner AUD-IDE-GEN.
- `audit_ide_generated_query_source_statement` — Definition.
- `audit_ide_generated_query_with_bodies` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`;
  owner AUD-IDE-GEN.
- `audit_ide_generated_query_with_bodies_statement` — Definition.
- `audit_ide_generated_with_bodies` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`; owner
  AUD-IDE-GEN.
- `audit_ide_generated_with_bodies_statement` — Definition.
- `audit_ide_machine_with_bodies` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`; owner
  AUD-IDE-GEN.
- `audit_ide_machine_with_bodies_statement` — Definition.
- `ide_body_internal` — Definition.
- `ide_body_read` — Definition.
- `ide_enqueue_with_bodies_counted` — Definition.
- `ide_generate_arcs_with_bodies_counted` — Definition.
- `ide_generated_external_allowance` — Definition.
- `ide_generated_external_body_budget` — Definition.
- `ide_generated_external_body_valid` — Definition.
- `ide_generated_extra_input` — Definition.
- `ide_generated_primitive_adequacy` — future Theorem in `AnalysesAuditIdeGeneratedAdequacy`;
  owner AUD-IDE-GEN.
- `ide_generated_primitive_adequacy_statement` — Definition.
- `ide_generated_query_counted` — Definition.
- `ide_generated_query_with_bodies_counted` — Definition.
- `ide_generated_source_budget` — Definition.
- `ide_generated_source_call` — Inductive.
- `ide_generated_source_counted` — Definition.
- `ide_generated_with_bodies_counted` — Definition.
- `ide_generator_literal_event_work` — Definition.
- `ide_generator_source_extra` — Definition.
- `ide_generator_source_work` — Definition.
- `ide_initial_literal_event_work` — Definition.
- `ide_initial_source_extra` — Definition.
- `ide_initial_source_work` — Definition.
- `ide_loop_with_bodies_counted` — Fixpoint.
- `ide_machine_body_input_budget` — Definition.
- `ide_machine_body_valid` — Definition.
- `ide_machine_literal_event_work` — Definition.
- `ide_machine_source_extra` — Definition.
- `ide_machine_source_work` — Definition.
- `ide_registry_solve` — Definition.
- `ide_rule_with_bodies_counted` — Definition.
- `ide_source_keys` — Definition.
- `ide_source_rows` — Definition.
- `ide_source_vertices` — Definition.
- `ide_step_with_bodies_counted` — Definition.
- `ide_update_with_bodies_counted` — Definition.

### `Galois.Analyses.AnalysesAuditIdeLegacy`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIdeLegacy.v`.

- `IdeHornActionMap` — constructor.
- `IdeHornDistinct` — constructor.
- `IdeHornExecution` — constructor.
- `IdeHornIndex` — constructor.
- `IdeHornReads` — constructor.
- `IdeHornTarget` — constructor.
- `IdeLegacyDirectMap` — constructor.
- `IdeLegacyJoin` — constructor.
- `IdeLegacyJoinMap` — constructor.
- `IdeLegacyLiftedSet` — constructor.
- `IdeLegacyReach` — constructor.
- `IdeLegacyReachMap` — constructor.
- `IdeLegacyTables` — constructor.
- `IdeLegacyWeight` — constructor.
- `IdeLegacyWholeRun` — constructor.
- `IdeTableJoin` — constructor.
- `IdeTableRegistry` — constructor.
- `IdeValueMap` — constructor.
- `IdeValueSet` — constructor.
- `audit_ide_legacy_full_source` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `audit_ide_legacy_full_source_statement` — Definition.
- `audit_ide_legacy_with_bodies` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `audit_ide_legacy_with_bodies_statement` — Definition.
- `exact_map_implementation_adequacy` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `exact_map_implementation_adequacy_statement` — Definition.
- `exact_map_literal_work` — Definition.
- `exact_map_model_charge` — Definition.
- `ide_encoding_entry` — Definition.
- `ide_encoding_entry_work` — Definition.
- `ide_finite_domain_counted` — Definition.
- `ide_finite_domain_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_finite_domain_counted_correct_statement` — Definition.
- `ide_finite_domain_input_budget` — Definition.
- `ide_horn_action_rows_counted` — Definition.
- `ide_horn_actions_counted` — Definition.
- `ide_horn_arcs_counted` — Definition.
- `ide_horn_call` — Inductive.
- `ide_horn_call_work` — Definition.
- `ide_horn_calls_counted` — Definition.
- `ide_horn_credit` — Definition.
- `ide_horn_distinct` — Definition.
- `ide_horn_execution` — Record.
- `ide_horn_index_counted` — Definition.
- `ide_horn_index_push` — Definition.
- `ide_horn_initial` — projection.
- `ide_horn_initial_events` — projection.
- `ide_horn_input_budget` — Definition.
- `ide_horn_input_call` — Inductive.
- `ide_horn_input_geometry` — Definition.
- `ide_horn_key_max` — Definition.
- `ide_horn_kind_body` — Definition.
- `ide_horn_loop_counted` — Fixpoint.
- `ide_horn_matches_counted` — Definition.
- `ide_horn_nested_queue_source_work` — Definition.
- `ide_horn_preparation` — projection.
- `ide_horn_prepared` — projection.
- `ide_horn_queue_budget` — Definition.
- `ide_horn_queue_size` — Definition.
- `ide_horn_queue_source_event` — Definition.
- `ide_horn_queue_source_work` — Definition.
- `ide_horn_returned` — projection.
- `ide_horn_rule_encoding_body` — Definition.
- `ide_horn_rule_keys` — Definition.
- `ide_horn_rules_counted` — Definition.
- `ide_horn_rules_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_horn_rules_counted_correct_statement` — Definition.
- `ide_horn_run_events` — projection.
- `ide_horn_site_operand` — Definition.
- `ide_horn_source_work` — Definition.
- `ide_horn_total_counted` — Definition.
- `ide_horn_total_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_horn_total_counted_correct_statement` — Definition.
- `ide_horn_total_input_budget` — Definition.
- `ide_horn_total_work` — Definition.
- `ide_horn_vertices_counted` — Definition.
- `ide_indexed_eval_counted` — Definition.
- `ide_indexed_eval_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_indexed_eval_counted_correct_statement` — Definition.
- `ide_legacy_actual_bodies` — Definition.
- `ide_legacy_body_budget` — Definition.
- `ide_legacy_body_valid` — Definition.
- `ide_legacy_call` — Inductive.
- `ide_legacy_closed_geometry` — Definition.
- `ide_legacy_collect` — Definition.
- `ide_legacy_collect_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_legacy_collect_correct_statement` — Definition.
- `ide_legacy_collect_with_bodies` — Definition.
- `ide_legacy_collection_stage` — projection.
- `ide_legacy_contribution_stage` — projection.
- `ide_legacy_contributions` — Definition.
- `ide_legacy_direct_engine` — projection.
- `ide_legacy_direct_rules` — projection.
- `ide_legacy_domain` — Definition.
- `ide_legacy_function_keys` — Definition.
- `ide_legacy_graph_stage` — projection.
- `ide_legacy_join_put` — Definition.
- `ide_legacy_join_put_with_bodies` — Definition.
- `ide_legacy_lifted_edge` — Definition.
- `ide_legacy_lifted_edge_with_bodies` — Definition.
- `ide_legacy_lifted_engine` — projection.
- `ide_legacy_lifted_facts` — Definition.
- `ide_legacy_lifted_graph` — Definition.
- `ide_legacy_lifted_graph_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_legacy_lifted_graph_correct_statement` — Definition.
- `ide_legacy_lifted_graph_with_bodies` — Definition.
- `ide_legacy_lifted_query` — Definition.
- `ide_legacy_lifted_rules` — projection.
- `ide_legacy_operand_max` — Definition.
- `ide_legacy_query_input_budget` — Definition.
- `ide_legacy_seed_stage` — projection.
- `ide_legacy_value_index` — Definition.
- `ide_legacy_value_index_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_legacy_value_index_correct_statement` — Definition.
- `ide_legacy_vertices` — Definition.
- `ide_legacy_weight` — Definition.
- `ide_legacy_weight_with_bodies` — Definition.
- `ide_legacy_whole_counted` — Definition.
- `ide_legacy_whole_counted_with_bodies` — Definition.
- `ide_legacy_whole_input_budget` — Definition.
- `ide_legacy_whole_query` — Definition.
- `ide_legacy_whole_run` — Record.
- `ide_legacy_whole_work` — Definition.
- `ide_lifted_encoding_body` — Definition.
- `ide_list_encoding_adequacy` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_list_encoding_adequacy_statement` — Definition.
- `ide_list_encoding_body` — Fixpoint.
- `ide_list_encoding_source_work` — Definition.
- `ide_registry_counted` — Definition.
- `ide_registry_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_registry_counted_correct_statement` — Definition.
- `ide_registry_input_budget` — Definition.
- `ide_table_apply_counted` — Definition.
- `ide_table_build_counted` — Fixpoint.
- `ide_table_build_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_table_build_counted_correct_statement` — Definition.
- `ide_table_build_input_budget` — Definition.
- `ide_table_call` — Inductive.
- `ide_table_eval_counted` — Definition.
- `ide_table_literal_event_work` — Definition.
- `ide_table_literal_work` — Definition.
- `ide_table_max_operand` — Definition.
- `ide_tables_implementation_adequacy` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_tables_implementation_adequacy_statement` — Definition.
- `ide_vectors_counted` — Fixpoint.
- `ide_vectors_counted_correct` — future Theorem in `AnalysesAuditIdeLegacyAdequacy`; owner
  AUD-IDE-LEGACY.
- `ide_vectors_counted_correct_statement` — Definition.
- `ide_vectors_input_budget` — Definition.
- `ide_vertex_encoding_body` — Definition.

### `Galois.Analyses.AnalysesAuditIdeModels`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIdeModels.v`.

- `AuditIdeCheckCounts` — constructor.
- `AuditIdeGeneratedRun` — constructor.
- `AuditIdeStrictAllCons` — constructor.
- `AuditIdeStrictAllNil` — constructor.
- `AuditIdeStrictEdgeRun` — constructor.
- `AuditIdeStrictPairRun` — constructor.
- `AuditIdeStrictValueRun` — constructor.
- `IdeCheckEdge` — constructor.
- `IdeCheckEval` — constructor.
- `IdeCheckLe` — constructor.
- `IdeCheckOldWeight` — constructor.
- `IdeCheckPair` — constructor.
- `IdeCheckWeight` — constructor.
- `IdeGeneratorCase` — constructor.
- `IdeGeneratorEdge` — constructor.
- `IdeGeneratorIndexGet` — constructor.
- `IdeGeneratorIndexSet` — constructor.
- `IdeGeneratorMatch` — constructor.
- `IdeGeneratorRule` — constructor.
- `IdeGeneratorWeight` — constructor.
- `IdeInitCase` — constructor.
- `IdeInitIndexGet` — constructor.
- `IdeInitIndexSet` — constructor.
- `IdeInitQueueAdd` — constructor.
- `IdeInitSeq` — constructor.
- `IdeInitTableSet` — constructor.
- `IdeMachineCase` — constructor.
- `IdeMachineCompose` — constructor.
- `IdeMachineEqual` — constructor.
- `IdeMachineFactRead` — constructor.
- `IdeMachineFactWrite` — constructor.
- `IdeMachineIncidenceRead` — constructor.
- `IdeMachineJoin` — constructor.
- `IdeMachineQueueAdd` — constructor.
- `IdeMachineQueueMember` — constructor.
- `IdeMachineQueueRemove` — constructor.
- `IdeMachineRuleRead` — constructor.
- `audit_ide_check_add` — Definition.
- `audit_ide_check_comparisons` — projection.
- `audit_ide_check_counts` — Record.
- `audit_ide_check_edges` — projection.
- `audit_ide_check_event` — Inductive.
- `audit_ide_check_event_counts` — Definition.
- `audit_ide_check_pairs` — projection.
- `audit_ide_check_strict_execution` — Definition.
- `audit_ide_check_strict_execution_exists` — future Theorem in `AnalysesAuditIdeModelsAdequacy`;
  owner AUD-IDE-MODELS.
- `audit_ide_check_strict_execution_exists_statement` — Definition.
- `audit_ide_check_strict_traced` — Definition.
- `audit_ide_check_trace_counts` — Definition.
- `audit_ide_check_values` — projection.
- `audit_ide_check_zero` — Definition.
- `audit_ide_enqueue_counted` — Fixpoint.
- `audit_ide_enqueue_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_enqueue_counted_statement` — Definition.
- `audit_ide_fuel_model` — Definition.
- `audit_ide_generate_arcs_counted` — Fixpoint.
- `audit_ide_generate_index_counted` — Fixpoint.
- `audit_ide_generate_index_plain` — Definition.
- `audit_ide_generate_matches_counted` — Fixpoint.
- `audit_ide_generate_matches_plain` — Definition.
- `audit_ide_generate_pairs_counted` — Fixpoint.
- `audit_ide_generated_run` — Record.
- `audit_ide_generator_call` — Inductive.
- `audit_ide_generator_counted` — Definition.
- `audit_ide_generator_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_generator_counted_statement` — Definition.
- `audit_ide_generator_input_budget` — Definition.
- `audit_ide_generator_input_width` — Definition.
- `audit_ide_generator_model_budget` — Definition.
- `audit_ide_generator_model_event` — Definition.
- `audit_ide_generator_model_work` — Definition.
- `audit_ide_ground_rules` — Definition.
- `audit_ide_incidence_size` — Definition.
- `audit_ide_indexed_rows` — Definition.
- `audit_ide_initial_call` — Inductive.
- `audit_ide_initial_counted` — Definition.
- `audit_ide_initial_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_initial_counted_statement` — Definition.
- `audit_ide_initial_fact_width` — Definition.
- `audit_ide_initial_index_counted` — Fixpoint.
- `audit_ide_initial_input_budget` — Definition.
- `audit_ide_initial_keys_counted` — Fixpoint.
- `audit_ide_initial_model_budget` — Definition.
- `audit_ide_initial_model_event` — Definition.
- `audit_ide_initial_model_work` — Definition.
- `audit_ide_initial_pending_counted` — Fixpoint.
- `audit_ide_initial_table_counted` — Fixpoint.
- `audit_ide_loop_counted` — Fixpoint.
- `audit_ide_loop_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_loop_counted_statement` — Definition.
- `audit_ide_machine_call` — Inductive.
- `audit_ide_machine_fact_keys` — Definition.
- `audit_ide_machine_fact_width` — Definition.
- `audit_ide_machine_input_budget` — Definition.
- `audit_ide_machine_model_bound` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_machine_model_bound_statement` — Definition.
- `audit_ide_machine_model_budget` — Definition.
- `audit_ide_machine_model_event` — Definition.
- `audit_ide_machine_model_work` — Definition.
- `audit_ide_machine_nat_keys` — Definition.
- `audit_ide_machine_nat_width` — Definition.
- `audit_ide_producer_counted` — Definition.
- `audit_ide_producer_model_budget` — Definition.
- `audit_ide_producer_model_work` — Definition.
- `audit_ide_rule_counted` — Definition.
- `audit_ide_rule_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_rule_counted_statement` — Definition.
- `audit_ide_run_final` — projection.
- `audit_ide_run_generator_events` — projection.
- `audit_ide_run_initial` — projection.
- `audit_ide_run_initial_events` — projection.
- `audit_ide_run_keys` — projection.
- `audit_ide_run_loop_events` — projection.
- `audit_ide_run_rules` — projection.
- `audit_ide_step_counted` — Definition.
- `audit_ide_step_counted_holds` — future Theorem in `AnalysesAuditIdeModelsAdequacy`; owner
  AUD-IDE-MODELS.
- `audit_ide_step_counted_statement` — Definition.
- `audit_ide_strict_all` — Fixpoint.
- `audit_ide_strict_all_execution` — Inductive.
- `audit_ide_strict_check_contract` — Definition.
- `audit_ide_strict_edge` — Definition.
- `audit_ide_strict_edge_execution` — Inductive.
- `audit_ide_strict_pair` — Definition.
- `audit_ide_strict_pair_count` — Definition.
- `audit_ide_strict_pair_execution` — Inductive.
- `audit_ide_strict_value` — Definition.
- `audit_ide_strict_value_execution` — Inductive.

### `Galois.Analyses.AnalysesAuditIdeSelect`

Card: AUD-IDE-CODE.

Owned path: `theories/Analyses/AnalysesAuditIdeSelect.v`.

- `IdeSourceSelection` — constructor.
- `audit_ide_compatibility_full_source` — future Theorem in `AnalysesAuditIdeSelectAdequacy`;
  owner AUD-IDE-SELECT.
- `audit_ide_compatibility_full_source_statement` — Definition.
- `audit_ide_execute_closed` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_execute_exact` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_execute_finite` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_execute_trace` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_finite_agreement` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_finite_select_correct` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_execute` — Definition.
- `audit_ide_fixed_execute_closed_statement` — Definition.
- `audit_ide_fixed_execute_trace_statement` — Definition.
- `audit_ide_fixed_finite_agreement_statement` — Definition.
- `audit_ide_fixed_finite_select_correct_statement` — Definition.
- `audit_ide_fixed_generator_exact_rows_statement` — Definition.
- `audit_ide_fixed_generator_occurrences_statement` — Definition.
- `audit_ide_fixed_generator_producer_statement` — Definition.
- `audit_ide_fixed_machine_consumer_statement` — Definition.
- `audit_ide_fixed_path_exact_statement` — Definition.
- `audit_ide_fixed_public_bottom` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_public_bottom_statement` — Definition.
- `audit_ide_fixed_public_finite_agreement` — future Theorem in `AnalysesAuditIdeSelectAdequacy`;
  owner AUD-IDE-SELECT.
- `audit_ide_fixed_public_finite_agreement_statement` — Definition.
- `audit_ide_fixed_public_incidence_bound_statement` — Definition.
- `audit_ide_fixed_public_paths` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_public_paths_statement` — Definition.
- `audit_ide_fixed_public_probe_counts_statement` — Definition.
- `audit_ide_fixed_public_select_correct` — future Theorem in `AnalysesAuditIdeSelectAdequacy`;
  owner AUD-IDE-SELECT.
- `audit_ide_fixed_public_select_correct_statement` — Definition.
- `audit_ide_fixed_public_updates` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_public_updates_statement` — Definition.
- `audit_ide_fixed_rule_generator_statement` — Definition.
- `audit_ide_fixed_stream_bottom` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_stream_bottom_execute_statement` — Definition.
- `audit_ide_fixed_stream_bottom_statement` — Definition.
- `audit_ide_fixed_stream_consumer` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_fixed_stream_consumer_statement` — Definition.
- `audit_ide_fixed_stream_execute_statement` — Definition.
- `audit_ide_generator_exact_rows` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_generator_occurrences` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_machine_consumer` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_nonempty_full_source` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_nonempty_full_source_statement` — Definition.
- `audit_ide_path_exact` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_producer_counted_holds` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_public_incidence_bound` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_public_probe_counts_holds` — future Theorem in `AnalysesAuditIdeSelectAdequacy`;
  owner AUD-IDE-SELECT.
- `audit_ide_rule_generator` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_select_full_source` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_select_full_source_statement` — Definition.
- `audit_ide_select_with_bodies` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_select_with_bodies_statement` — Definition.
- `audit_ide_selector_client` — Definition.
- `audit_ide_selector_fallback_consumer` — future Theorem in `AnalysesAuditIdeSelectAdequacy`;
  owner AUD-IDE-SELECT.
- `audit_ide_selector_fallback_consumer_statement` — Definition.
- `audit_ide_selector_fast_consumer` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_selector_fast_consumer_statement` — Definition.
- `audit_ide_selector_registry` — Definition.
- `audit_ide_stream_bottom` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_stream_consumer` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_strong_finite_agreement` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `audit_ide_strong_path_exact` — future Theorem in `AnalysesAuditIdeSelectAdequacy`; owner
  AUD-IDE-SELECT.
- `ide_compatibility_body_budget` — Definition.
- `ide_compatibility_body_valid` — Definition.
- `ide_compatibility_counted` — Definition.
- `ide_compatibility_input_budget` — Definition.
- `ide_compatibility_value_counted` — Definition.
- `ide_compatibility_value_with_bodies` — Definition.
- `ide_compatibility_with_bodies` — Definition.
- `ide_registry_select` — Definition.
- `ide_select_body_allowance` — Definition.
- `ide_select_input_budget` — Definition.
- `ide_select_query_budget` — Definition.
- `ide_select_source_counted` — Definition.
- `ide_select_with_bodies` — Definition.
- `ide_source_build_work` — projection.
- `ide_source_check` — projection.
- `ide_source_generated` — projection.
- `ide_source_legacy` — projection.
- `ide_source_mode` — projection.
- `ide_source_selected_query` — projection.
- `ide_source_selected_query_work` — projection.
- `ide_source_selection` — Record.

### `Galois.Analyses.AnalysesAuditPre`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPre.v`.

- `AuditSnapshotSyntax` — constructor.
- `PreBodyFinalize` — constructor.
- `PreBodyFrg` — constructor.
- `PreBodyMaterialize` — constructor.
- `PreBodySolve` — constructor.
- `PreDomSourceData` — constructor.
- `PreViewEncode` — constructor.
- `PreViewOut` — constructor.
- `PreViewSource` — constructor.
- `PreViewTarget` — constructor.
- `audit_entry_block_view` — Definition.
- `audit_entry_block_view_holds` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_block_view_statement` — Definition.
- `audit_entry_construct_points` — Definition.
- `audit_entry_construct_points_holds` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_entry_construct_points_statement` — Definition.
- `audit_entry_point_endings` — Definition.
- `audit_entry_point_graph` — Definition.
- `audit_entry_point_path` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_point_path_complete` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_point_path_complete_statement` — Definition.
- `audit_entry_point_path_statement` — Definition.
- `audit_entry_point_ready` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_point_ready_statement` — Definition.
- `audit_entry_point_semantics` — Definition.
- `audit_entry_point_semantics_holds` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_entry_point_semantics_statement` — Definition.
- `audit_entry_point_view` — Definition.
- `audit_entry_snapshot` — Definition.
- `audit_entry_snapshot_behavior` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_snapshot_behavior_statement` — Definition.
- `audit_entry_snapshot_get` — Definition.
- `audit_entry_snapshot_get_holds` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_entry_snapshot_get_statement` — Definition.
- `audit_entry_source_bijection` — projection.
- `audit_entry_source_defs` — projection.
- `audit_entry_source_kills` — projection.
- `audit_entry_source_laws` — Record.
- `audit_entry_source_params_unique` — projection.
- `audit_entry_source_points` — projection.
- `audit_entry_source_uses` — projection.
- `audit_entry_values_of` — Definition.
- `audit_pre_body_composition` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_body_composition_statement` — Definition.
- `audit_pre_caller_source` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_caller_source_statement` — Definition.
- `audit_pre_certificate_full_source` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_pre_certificate_full_source_statement` — Definition.
- `audit_pre_full_snapshot_behavior` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_full_snapshot_behavior_statement` — Definition.
- `audit_pre_full_snapshot_laws` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_full_snapshot_laws_statement` — Definition.
- `audit_pre_full_snapshot_semantics` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_pre_full_snapshot_semantics_statement` — Definition.
- `audit_pre_full_snapshot_value` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_full_snapshot_value_statement` — Definition.
- `audit_pre_graph_callback_instances` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_pre_graph_callback_instances_statement` — Definition.
- `audit_pre_implementation_adequacy` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_pre_implementation_adequacy_statement` — Definition.
- `audit_pre_place_full_source` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_place_full_source_statement` — Definition.
- `audit_pre_place_source_model` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_pre_place_source_model_statement` — Definition.
- `audit_pre_source_block_graph` — projection.
- `audit_pre_source_blocks_reachable` — projection.
- `audit_pre_source_cross_no_defs` — projection.
- `audit_pre_source_def_home` — projection.
- `audit_pre_source_initial_family` — projection.
- `audit_pre_source_occurrences` — projection.
- `audit_pre_source_point_graph` — projection.
- `audit_pre_source_point_laws` — projection.
- `audit_pre_source_points_reachable` — projection.
- `audit_pre_source_real_internal` — projection.
- `audit_pre_source_runtime` — projection.
- `audit_pre_source_universe_unique` — projection.
- `audit_snapshot_endings` — Definition.
- `audit_snapshot_eval` — projection.
- `audit_snapshot_family` — projection.
- `audit_snapshot_graph_laws` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_graph_laws_statement` — Definition.
- `audit_snapshot_graph_view` — Definition.
- `audit_snapshot_initial` — projection.
- `audit_snapshot_kill` — projection.
- `audit_snapshot_old_block_projection` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_snapshot_old_block_projection_statement` — Definition.
- `audit_snapshot_old_edge_projection` — future Theorem in `AnalysesAuditPreAdequacy`; owner
  AUD-SP.
- `audit_snapshot_old_edge_projection_statement` — Definition.
- `audit_snapshot_old_expression` — projection.
- `audit_snapshot_old_value` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_old_value_statement` — Definition.
- `audit_snapshot_operands` — projection.
- `audit_snapshot_pre` — Definition.
- `audit_snapshot_pre_behavior` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_pre_behavior_statement` — Definition.
- `audit_snapshot_pre_laws` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_pre_laws_statement` — Definition.
- `audit_snapshot_pre_runtime` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_pre_runtime_statement` — Definition.
- `audit_snapshot_pre_source_laws` — Record.
- `audit_snapshot_pure` — projection.
- `audit_snapshot_semantics` — Definition.
- `audit_snapshot_shape` — projection.
- `audit_snapshot_source_args` — projection.
- `audit_snapshot_source_graph` — projection.
- `audit_snapshot_source_params` — projection.
- `audit_snapshot_source_points` — projection.
- `audit_snapshot_source_view` — projection.
- `audit_snapshot_ssa_view` — Definition.
- `audit_snapshot_ssa_view_from` — Definition.
- `audit_snapshot_state` — Definition.
- `audit_snapshot_step_frame` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_step_frame_statement` — Definition.
- `audit_snapshot_syntax` — Record.
- `audit_snapshot_translate` — projection.
- `audit_snapshot_view_laws` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_view_laws_statement` — Definition.
- `audit_snapshot_view_source_laws` — Record.
- `audit_snapshot_view_structure` — future Theorem in `AnalysesAuditPreAdequacy`; owner AUD-SP.
- `audit_snapshot_view_structure_statement` — Definition.
- `audit_virtual_payload` — Definition.
- `audit_virtual_state` — Definition.
- `full_snapshot_endings` — Definition.
- `full_snapshot_pre` — Definition.
- `full_snapshot_pre_behavior` — Definition.
- `full_snapshot_pre_laws` — Definition.
- `full_snapshot_semantics` — Definition.
- `full_snapshot_semantics_law` — Definition.
- `full_snapshot_ssa_view` — Definition.
- `full_snapshot_value_law` — Definition.
- `full_snapshot_view` — Definition.
- `full_virtual_payload` — Definition.
- `full_virtual_state` — Definition.
- `pre_dom_dfs_events` — projection.
- `pre_dom_erase` — projection.
- `pre_dom_external_work` — Definition.
- `pre_dom_fixed_run` — Definition.
- `pre_dom_lt` — projection.
- `pre_dom_parents` — projection.
- `pre_dom_prepare_events` — projection.
- `pre_dom_result` — projection.
- `pre_dom_search` — projection.
- `pre_dom_semi` — projection.
- `pre_dom_source_data` — Record.
- `pre_dom_whole_work` — Definition.
- `pre_graph_view_call` — Inductive.
- `pre_place_body_call` — Inductive.
- `pre_place_from_backends_budget` — Definition.
- `pre_place_from_backends_counted` — Definition.
- `pre_place_graph_budget` — Definition.
- `pre_place_graph_run` — Definition.
- `pre_view_encode` — Definition.
- `pre_view_frontier` — Definition.
- `pre_view_out` — Definition.
- `pre_view_prepare` — Definition.
- `pre_view_source` — Definition.
- `pre_view_target` — Definition.
- `pre_view_virtual` — Definition.
- `pre_view_weight` — Definition.

### `Galois.Analyses.AnalysesAuditPreFamily`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPreFamily.v`.

- `PreFamilyAdd` — constructor.
- `PreFamilyEdges` — constructor.
- `PreFamilyExpr` — constructor.
- `PreFamilyMul` — constructor.
- `PreFamilyNMul` — constructor.
- `PreFamilyOfNat` — constructor.
- `PreFamilyOperands` — constructor.
- `PreFamilyOut` — constructor.
- `PreFamilySucc` — constructor.
- `PreFamilyTranslate` — constructor.
- `audit_pre_arithmetic_implementation_adequacy` — future Theorem in
  `AnalysesAuditPreFamilyAdequacy`; owner AUD-SP-FAMILY.
- `audit_pre_arithmetic_implementation_adequacy_statement` — Definition.
- `audit_pre_family_full_source` — future Theorem in `AnalysesAuditPreFamilyAdequacy`; owner
  AUD-SP-FAMILY.
- `audit_pre_family_full_source_statement` — Definition.
- `pre_discover_counted_erases` — future Theorem in `AnalysesAuditPreFamilyAdequacy`; owner
  AUD-SP-FAMILY.
- `pre_discover_counted_erases_statement` — Definition.
- `pre_discover_run_counted` — Fixpoint.
- `pre_discover_step_counted` — Definition.
- `pre_expr_universe_counted` — Definition.
- `pre_family_bound_counted` — Definition.
- `pre_family_call` — Inductive.
- `pre_family_edges_counted` — Definition.
- `pre_family_input_budget` — Definition.
- `pre_length_counted` — Fixpoint.
- `pre_nadd_body` — Definition.
- `pre_nadd_counted` — Definition.
- `pre_nmul_body` — Definition.
- `pre_nofnat_body` — Definition.
- `pre_npower_counted` — Definition.
- `pre_nsucc_body` — Definition.
- `pre_of_nat_counted` — Definition.
- `pre_positive_add_body` — Fixpoint.
- `pre_positive_mul_body` — Fixpoint.
- `pre_positive_power_counted` — Fixpoint.
- `pre_positive_succ_body` — Fixpoint.
- `pre_translated_counted` — Definition.

### `Galois.Analyses.AnalysesAuditPreFinite`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPreFinite.v`.

- `PfcAccept` — constructor.
- `PfcExprs` — constructor.
- `PfcNatAdd` — constructor.
- `PfcNatLe` — constructor.
- `PfcPhi` — constructor.
- `PfcRecomputed` — constructor.
- `PfcReload` — constructor.
- `PfcRows` — constructor.
- `audit_pre_bounded_correction` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_bounded_correction_statement` — Definition.
- `audit_pre_choose_best` — Fixpoint.
- `audit_pre_choose_best_holds` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_choose_best_statement` — Definition.
- `audit_pre_edge_support` — Definition.
- `audit_pre_edge_support_holds` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_edge_support_statement` — Definition.
- `audit_pre_enumerate` — Definition.
- `audit_pre_enumerate_exact` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_enumerate_exact_statement` — Definition.
- `audit_pre_enumerate_nodup` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_enumerate_nodup_statement` — Definition.
- `audit_pre_enumerate_size` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_enumerate_size_statement` — Definition.
- `audit_pre_enumeration` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_finite_source` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_finite_source_statement` — Definition.
- `audit_pre_is_minimal` — Definition.
- `audit_pre_legal` — Definition.
- `audit_pre_maps` — Fixpoint.
- `audit_pre_minimum_check` — Definition.
- `audit_pre_objective_evidence` — future Theorem in `AnalysesAuditPreFiniteAdequacy`; owner
  AUD-SP-FINITE.
- `audit_pre_objective_evidence_statement` — Definition.
- `audit_pre_phi_keys` — Definition.
- `audit_pre_plan_supported` — Definition.
- `audit_pre_static_cost` — Definition.
- `audit_pre_sublists` — Fixpoint.
- `audit_pre_version_supported` — Definition.
- `audit_pre_versions` — Definition.
- `pre_checker_exact` — projection.
- `pre_checker_laws` — Record.
- `pre_choose_best_counted` — Fixpoint.
- `pre_competitor_legal` — Definition.
- `pre_enumerate_counted` — Definition.
- `pre_enumerate_input_budget` — Definition.
- `pre_finite_add_counted` — Definition.
- `pre_finite_call` — Inductive.
- `pre_finite_geometry` — Definition.
- `pre_finite_le_counted` — Definition.
- `pre_finite_length_counted` — Fixpoint.
- `pre_finite_objective` — Definition.
- `pre_finite_operand_max` — Definition.
- `pre_finite_phi_body` — Definition.
- `pre_finite_phi_keys_counted` — Definition.
- `pre_finite_versions_counted` — Definition.
- `pre_maps_counted` — Fixpoint.
- `pre_minimum_check_counted` — Definition.
- `pre_minimum_input_budget` — Definition.
- `pre_objective_evidence` — Definition.
- `pre_row_contains_counted` — Definition.
- `pre_static_cost_counted` — Definition.
- `pre_sublists_counted` — Fixpoint.

### `Galois.Analyses.AnalysesAuditPreFrg`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPreFrg.v`.

- `FrgFamily` — constructor.
- `FrgFuel` — constructor.
- `FrgParents` — constructor.
- `FrgPhi` — constructor.
- `FrgRename` — constructor.
- `PhiBlockOf` — constructor.
- `PhiBlockParams` — constructor.
- `PhiBlocks` — constructor.
- `PhiFrontier` — constructor.
- `PhiGraphBody` — constructor.
- `PhiGraphDfs` — constructor.
- `PhiGraphEncode` — constructor.
- `PhiGraphOut` — constructor.
- `PhiGraphPrepare` — constructor.
- `PhiGraphTarget` — constructor.
- `PhiHome` — constructor.
- `PhiOccurrences` — constructor.
- `PhiPairs` — constructor.
- `PhiParameters` — constructor.
- `PhiPred` — constructor.
- `PhiRename` — constructor.
- `PhiSource` — constructor.
- `PhiUnion` — constructor.
- `PrnArguments` — constructor.
- `PrnBlockSource` — constructor.
- `PrnBlockTarget` — constructor.
- `PrnChildren` — constructor.
- `PrnDefinitions` — constructor.
- `PrnEncodeE` — constructor.
- `PrnEncodeU` — constructor.
- `PrnEqual` — constructor.
- `PrnExit` — constructor.
- `PrnExitPoint` — constructor.
- `PrnFresh` — constructor.
- `PrnGroupBU` — constructor.
- `PrnGroupEU` — constructor.
- `PrnGroupVU` — constructor.
- `PrnInitial` — constructor.
- `PrnInstructions` — constructor.
- `PrnKilled` — constructor.
- `PrnLink` — constructor.
- `PrnOccurrence` — constructor.
- `PrnOperands` — constructor.
- `PrnOut` — constructor.
- `PrnParameter` — constructor.
- `PrnPhis` — constructor.
- `PrnPoints` — constructor.
- `PrnPred` — constructor.
- `PrnPure` — constructor.
- `PrnRecomputed` — constructor.
- `PrnScope` — constructor.
- `PrnSeen` — constructor.
- `PrnSetArgument` — constructor.
- `PrnSetU` — constructor.
- `PrnSites` — constructor.
- `PrnTarget` — constructor.
- `PrnTranslate` — constructor.
- `PrnUnsafe` — constructor.
- `PrnVersions` — constructor.
- `audit_pre_frg_from_graph_source` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner
  AUD-SP-FRG.
- `audit_pre_frg_from_graph_source_statement` — Definition.
- `pre_build_frg_from_graph` — Definition.
- `pre_build_frg_from_graph_counted` — Definition.
- `pre_build_frg_from_graph_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner
  AUD-SP-FRG.
- `pre_build_frg_from_graph_erases_statement` — Definition.
- `pre_definitions_query_counted` — Definition.
- `pre_frg_call` — Inductive.
- `pre_frg_children_counted` — Fixpoint.
- `pre_frg_from_graph_input_budget` — Definition.
- `pre_frg_length_counted` — Fixpoint.
- `pre_group_add_counted` — Definition.
- `pre_group_lookup_counted` — Definition.
- `pre_occurrence_blocks_counted` — Definition.
- `pre_parameter_blocks_counted` — Definition.
- `pre_phi_call` — Inductive.
- `pre_phi_direct_counted` — Definition.
- `pre_phi_encode_adapter` — Definition.
- `pre_phi_frontier_counted` — Definition.
- `pre_phi_graph_body_work` — Definition.
- `pre_phi_graph_call` — Inductive.
- `pre_phi_graph_counted` — Definition.
- `pre_phi_graph_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner AUD-SP-FRG.
- `pre_phi_graph_erases_statement` — Definition.
- `pre_phi_helpers_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner AUD-SP-FRG.
- `pre_phi_helpers_erases_statement` — Definition.
- `pre_phi_next_counted` — Definition.
- `pre_phi_out_adapter` — Definition.
- `pre_phi_out_counted` — Definition.
- `pre_phi_sites_counted` — Definition.
- `pre_phi_starts_counted` — Definition.
- `pre_phi_target_adapter` — Definition.
- `pre_phi_ub_body` — Definition.
- `pre_phi_union_counted` — Definition.
- `pre_rename_alter_candidates_counted` — Definition.
- `pre_rename_alter_counted` — Definition.
- `pre_rename_alter_index_counted` — Definition.
- `pre_rename_argument_counted` — Definition.
- `pre_rename_argument_index_counted` — Definition.
- `pre_rename_beu_body` — Definition.
- `pre_rename_block_counted` — Definition.
- `pre_rename_bu_be_body` — Definition.
- `pre_rename_bu_body` — Definition.
- `pre_rename_call` — Inductive.
- `pre_rename_cells_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner AUD-SP-FRG.
- `pre_rename_cells_erases_statement` — Definition.
- `pre_rename_definitions_counted` — Definition.
- `pre_rename_edge_code` — Definition.
- `pre_rename_edges_counted` — Definition.
- `pre_rename_equal` — Definition.
- `pre_rename_exit_counted` — Definition.
- `pre_rename_exit_index_counted` — Definition.
- `pre_rename_expr_code` — Definition.
- `pre_rename_fresh_versions_counted` — Definition.
- `pre_rename_initial_counted` — Definition.
- `pre_rename_instruction_counted` — Definition.
- `pre_rename_mark_counted` — Definition.
- `pre_rename_occurrence_counted` — Definition.
- `pre_rename_operand_index_counted` — Definition.
- `pre_rename_phi_index_counted` — Definition.
- `pre_rename_run_counted` — Fixpoint.
- `pre_rename_same_counted` — Definition.
- `pre_rename_setup_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner AUD-SP-FRG.
- `pre_rename_setup_erases_statement` — Definition.
- `pre_rename_step_counted` — Definition.
- `pre_rename_top_counted` — Definition.
- `pre_rename_version_body` — Definition.
- `pre_rename_versions_counted` — Definition.
- `pre_rename_walk_erases` — future Theorem in `AnalysesAuditPreFrgAdequacy`; owner AUD-SP-FRG.
- `pre_rename_walk_erases_statement` — Definition.

### `Galois.Analyses.AnalysesAuditPrePlan`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPrePlan.v`.

- `PfArguments` — constructor.
- `PfDom` — constructor.
- `PfEdges` — constructor.
- `PfExpr` — constructor.
- `PfExpressionTarget` — constructor.
- `PfFlags` — constructor.
- `PfIdom` — constructor.
- `PfInitial` — constructor.
- `PfKill` — constructor.
- `PfNodeRows` — constructor.
- `PfOccurrence` — constructor.
- `PfOutputs` — constructor.
- `PfParameter` — constructor.
- `PfPhi` — constructor.
- `PfPositiveCompare` — constructor.
- `PfPure` — constructor.
- `PfRecomputed` — constructor.
- `PfReload` — constructor.
- `PfScope` — constructor.
- `PfSource` — constructor.
- `PfTarget` — constructor.
- `PfTranslate` — constructor.
- `PrBlockEdge` — constructor.
- `PrFinalize` — constructor.
- `PrLinks` — constructor.
- `PrOut` — constructor.
- `PrPhis` — constructor.
- `PrPointIndex` — constructor.
- `PreMaterializePhi` — constructor.
- `PreMaterializeRecomputed` — constructor.
- `PreMaterializeReload` — constructor.
- `PreMaterializeRows` — constructor.
- `PreMaterializeSet` — constructor.
- `audit_pre_finalize_order_source` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `audit_pre_finalize_order_source_statement` — Definition.
- `audit_pre_materialize_full_source` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `audit_pre_materialize_full_source_statement` — Definition.
- `pre_add_argument_row_counted` — Definition.
- `pre_add_phi_row_counted` — Definition.
- `pre_argument_counted` — Definition.
- `pre_argument_rows_counted` — Definition.
- `pre_available_counted` — Definition.
- `pre_define_phi_counted` — Definition.
- `pre_dominates_counted` — Definition.
- `pre_expression_add_counted` — Definition.
- `pre_expression_rows_counted` — Definition.
- `pre_finalize_call` — Inductive.
- `pre_finalize_helpers_erasure` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `pre_finalize_helpers_erasure_statement` — Definition.
- `pre_finalize_loop_erases` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `pre_finalize_loop_erases_statement` — Definition.
- `pre_finalize_order_counted` — Definition.
- `pre_finalize_order_erases` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `pre_finalize_order_erases_statement` — Definition.
- `pre_finalize_order_input_budget` — Definition.
- `pre_finalize_rows_erases` — future Theorem in `AnalysesAuditPrePlanAdequacy`; owner
  AUD-SP-PLAN.
- `pre_finalize_rows_erases_statement` — Definition.
- `pre_flag_body` — Definition.
- `pre_flag_get_counted` — Definition.
- `pre_initial_scope_counted` — Definition.
- `pre_insert_operand_counted` — Definition.
- `pre_materialize_call` — Inductive.
- `pre_materialize_counted` — Definition.
- `pre_materialize_input_budget` — Definition.
- `pre_materialize_input_operand` — Definition.
- `pre_node_counted` — Definition.
- `pre_occurrence_counted` — Definition.
- `pre_phi_body` — Definition.
- `pre_phi_rows_counted` — Definition.
- `pre_point_index_counted` — Definition.
- `pre_rows_call` — Inductive.
- `pre_scope_body` — Definition.
- `pre_select_counted` — Definition.
- `pre_table_step_counted` — Definition.
- `pre_version_point_counted` — Definition.
- `pre_will_counted` — Definition.

### `Galois.Analyses.AnalysesAuditPrePlanSupport`

Card: AUD-SP-PLAN-SUPPORT.

Owned path: `theories/Analyses/AnalysesAuditPrePlanSupport.v`.

- `pre_finalize_order_bound` — future Theorem; owner AUD-SP-PLAN-SUPPORT.

### `Galois.Analyses.AnalysesAuditPreSolve`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPreSolve.v`.

- `PreClosureDfs` — constructor.
- `PreClosureEncode` — constructor.
- `PreClosureOut` — constructor.
- `PreClosurePrepare` — constructor.
- `PreClosureRows` — constructor.
- `PreClosureSet` — constructor.
- `PreClosureTarget` — constructor.
- `PreSolverClosure` — constructor.
- `PreSolverFlags` — constructor.
- `PreSolverKeys` — constructor.
- `PreSolverLinks` — constructor.
- `audit_pre_reset_closure_full_source` — future Theorem in `AnalysesAuditPreSolveAdequacy`; owner
  AUD-SP-SOLVE.
- `audit_pre_reset_closure_full_source_statement` — Definition.
- `audit_pre_solve_full_source` — future Theorem in `AnalysesAuditPreSolveAdequacy`; owner
  AUD-SP-SOLVE.
- `audit_pre_solve_full_source_statement` — Definition.
- `pre_closure_call` — Inductive.
- `pre_reset_add_counted` — Definition.
- `pre_reset_body_work` — Definition.
- `pre_reset_closure_input_budget` — Definition.
- `pre_reset_closure_source` — Definition.
- `pre_reset_encode_adapter` — Definition.
- `pre_reset_index_source` — Definition.
- `pre_reset_nodes_source` — Definition.
- `pre_reset_out_adapter` — Definition.
- `pre_reset_out_adapter_erases` — future Theorem in `AnalysesAuditPreSolveAdequacy`; owner
  AUD-SP-SOLVE.
- `pre_reset_out_adapter_erases_statement` — Definition.
- `pre_reset_out_source` — Definition.
- `pre_reset_source_operand` — Definition.
- `pre_reset_target_adapter` — Definition.
- `pre_solve_input_budget` — Definition.
- `pre_solve_source` — Definition.
- `pre_solve_source_erases` — future Theorem in `AnalysesAuditPreSolveAdequacy`; owner
  AUD-SP-SOLVE.
- `pre_solve_source_erases_statement` — Definition.
- `pre_solver_call` — Inductive.
- `pre_solver_cannot_arcs` — Definition.
- `pre_solver_cannot_seeds` — Definition.
- `pre_solver_closure` — Definition.
- `pre_solver_down_arcs` — Definition.
- `pre_solver_flags` — Definition.
- `pre_solver_get` — Definition.
- `pre_solver_input_support` — Definition.
- `pre_solver_key_body` — Definition.
- `pre_solver_later_arcs` — Definition.
- `pre_solver_later_seeds` — Definition.
- `pre_solver_member` — Definition.

### `Galois.Analyses.AnalysesAuditPreSource`

Card: AUD-SP-CODE.

Owned path: `theories/Analyses/AnalysesAuditPreSource.v`.

- `PreClosureDfsReceipt` — constructor.
- `PreClosureEncodeReceipt` — constructor.
- `PreClosureEventArithmetic` — constructor.
- `PreClosureEventCall` — constructor.
- `PreClosureEventCase` — constructor.
- `PreClosureEventConstruct` — constructor.
- `PreClosureEventKeyBit` — constructor.
- `PreClosureOutReceipt` — constructor.
- `PreClosurePrepareReceipt` — constructor.
- `PreClosureRowsReceipt` — constructor.
- `PreClosureSetReceipt` — constructor.
- `PreClosureTargetReceipt` — constructor.
- `PrePhiGraphBody` — constructor.
- `PrePhiGraphDfs` — constructor.
- `PrePhiGraphEncode` — constructor.
- `PrePhiGraphOut` — constructor.
- `PrePhiGraphPrepare` — constructor.
- `PrePhiGraphTarget` — constructor.
- `PreViewAdapters` — constructor.
- `audit_pre_body_source_family` — future Theorem in `AnalysesAuditPreSourceAdequacy`; owner
  AUD-SP-SOURCE.
- `audit_pre_body_source_family_statement` — Definition.
- `audit_pre_certificate_body_source` — future Theorem in `AnalysesAuditPreSourceAdequacy`; owner
  AUD-SP-SOURCE.
- `audit_pre_certificate_body_source_statement` — Definition.
- `audit_pre_full_source` — future Theorem in `AnalysesAuditPreSourceAdequacy`; owner
  AUD-SP-SOURCE.
- `audit_pre_full_source_statement` — Definition.
- `audit_pre_place_body_source` — future Theorem in `AnalysesAuditPreSourceAdequacy`; owner
  AUD-SP-SOURCE.
- `audit_pre_place_body_source_statement` — Definition.
- `audit_pre_view_adapter_laws` — Definition.
- `audit_pre_view_adapters` — Record.
- `pre_actual_external_receipt` — Definition.
- `pre_actual_map_receipt` — Definition.
- `pre_audit_event_receipt` — Definition.
- `pre_block_edge_encoder` — projection.
- `pre_block_edge_of_source` — projection.
- `pre_block_encoder` — projection.
- `pre_block_of_source` — projection.
- `pre_block_out_source` — projection.
- `pre_block_params_source` — projection.
- `pre_block_source_source` — projection.
- `pre_block_target_source` — projection.
- `pre_block_view_receipt` — Definition.
- `pre_body_call_receipt` — Definition.
- `pre_closure_call_receipt` — Inductive.
- `pre_definitions_source` — projection.
- `pre_dfs_callback_calls` — Definition.
- `pre_dom_actual_callback_calls` — Definition.
- `pre_dom_body_callback_calls` — Definition.
- `pre_dom_callback_calls` — Definition.
- `pre_edge_encoder` — projection.
- `pre_erase_callback_calls` — Definition.
- `pre_exit_source` — projection.
- `pre_expr_encoder` — projection.
- `pre_expression_target_source` — projection.
- `pre_family_call_receipt` — Definition.
- `pre_finalize_call_receipt` — Definition.
- `pre_finite_call_receipt` — Definition.
- `pre_fixed_calls_receipt` — Definition.
- `pre_frg_call_receipt` — Definition.
- `pre_frg_version_receipt` — Definition.
- `pre_frontier_callback_calls` — Definition.
- `pre_home_source` — projection.
- `pre_initial_source` — projection.
- `pre_instructions_source` — projection.
- `pre_internal_receipt` — Definition.
- `pre_kill_source` — projection.
- `pre_lt_callback_calls` — Definition.
- `pre_map_callback_calls` — Definition.
- `pre_materialize_call_receipt` — Definition.
- `pre_operands_source` — projection.
- `pre_pair_source_receipt` — Definition.
- `pre_parameter_source` — projection.
- `pre_phi_call_receipt` — Definition.
- `pre_phi_graph_call_receipt` — Inductive.
- `pre_place_graph_body_run` — Definition.
- `pre_point_encoder` — projection.
- `pre_point_out_source` — projection.
- `pre_point_source_source` — projection.
- `pre_point_target_source` — projection.
- `pre_point_view_receipt` — Definition.
- `pre_points_source` — projection.
- `pre_prepare_callback_calls` — Definition.
- `pre_pure_source` — projection.
- `pre_receipt_allowance` — Definition.
- `pre_receipt_trace` — Definition.
- `pre_receipt_work` — Definition.
- `pre_recomputed_source` — projection.
- `pre_rename_call_receipt` — Definition.
- `pre_rows_call_receipt` — Definition.
- `pre_semi_callback_calls` — Definition.
- `pre_semi_producer_callback_calls` — Definition.
- `pre_set_callback_calls` — Definition.
- `pre_solver_call_receipt` — Definition.
- `pre_translate_source` — projection.
- `pre_value_encoder` — projection.
- `pre_virtual_callback_calls` — Definition.

### `Galois.Analyses.AnalysesAuditSource`

Card: AUD-SOURCE-MODELS.

Owned path: `theories/Analyses/AnalysesAuditSource.v`.

- `AuditExternalAdapter` — constructor.
- `AuditExternalReceipt` — constructor.
- `ExactCounted` — constructor.
- `ExactElements` — constructor.
- `ExactEncode` — constructor.
- `ExactGet` — constructor.
- `ExactRemove` — constructor.
- `ExactSet` — constructor.
- `ExternalBinary` — constructor.
- `ExternalCase` — constructor.
- `ExternalConstruct` — constructor.
- `ExternalDivide` — constructor.
- `ExternalEmit` — constructor.
- `ExternalMultiply` — constructor.
- `ExternalOrFalse` — constructor.
- `ExternalOrTrue` — constructor.
- `ExternalReturn` — constructor.
- `ExternalUnary` — constructor.
- `audit_base_encoding_receipts` — Definition.
- `audit_bool_or_adapter` — Definition.
- `audit_bool_or_source` — Inductive.
- `audit_external_adapter` — Record.
- `audit_external_adapter_laws` — Definition.
- `audit_external_body` — Definition.
- `audit_external_body_positive` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_external_body_positive_statement` — Definition.
- `audit_external_frame` — Inductive.
- `audit_external_frame_work` — Definition.
- `audit_external_instrumentation_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_external_instrumentation_erases_statement` — Definition.
- `audit_external_receipt` — Record.
- `audit_external_same_call` — Definition.
- `audit_external_same_call_exists` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_external_same_call_exists_statement` — Definition.
- `audit_external_trace_work` — Definition.
- `audit_list_encoding_receipts` — Definition.
- `audit_option_encoding_receipts` — Definition.
- `audit_pair_encoding_receipts` — Definition.
- `audit_pre_derived_encoding_adequacy` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_pre_derived_encoding_adequacy_statement` — Definition.
- `audit_pre_map_implementation_adequacy` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_pre_map_implementation_adequacy_statement` — Definition.
- `audit_pre_pair_encoding_adequacy` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `audit_pre_pair_encoding_adequacy_statement` — Definition.
- `audit_source_body_work` — Definition.
- `audit_sum_encoding_receipts` — Definition.
- `exact_all` — Fixpoint.
- `exact_append` — Fixpoint.
- `exact_append_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner AUD-SOURCE-BASE.
- `exact_append_erases_statement` — Definition.
- `exact_bind` — Definition.
- `exact_bodies` — projection.
- `exact_call` — Definition.
- `exact_case` — Definition.
- `exact_counted` — Record.
- `exact_elements` — Definition.
- `exact_encode` — Definition.
- `exact_events` — projection.
- `exact_external_call` — Definition.
- `exact_filter` — Fixpoint.
- `exact_flat_map` — Fixpoint.
- `exact_fold_left` — Fixpoint.
- `exact_fold_left_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `exact_fold_left_erases_statement` — Definition.
- `exact_fold_right` — Fixpoint.
- `exact_fold_right_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner
  AUD-SOURCE-BASE.
- `exact_fold_right_erases_statement` — Definition.
- `exact_get` — Definition.
- `exact_get_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner AUD-SOURCE-BASE.
- `exact_get_erases_statement` — Definition.
- `exact_lift` — Definition.
- `exact_map` — Fixpoint.
- `exact_map_call` — Inductive.
- `exact_map_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner AUD-SOURCE-BASE.
- `exact_map_erases_statement` — Definition.
- `exact_ne_nodes` — Fixpoint.
- `exact_remove` — Definition.
- `exact_return` — Definition.
- `exact_rev` — Fixpoint.
- `exact_set` — Definition.
- `exact_set_elements` — Definition.
- `exact_set_erases` — future Theorem in `AnalysesAuditSourceAdequacy`; owner AUD-SOURCE-BASE.
- `exact_set_erases_statement` — Definition.
- `exact_set_mem` — Definition.
- `exact_set_of_list` — Definition.
- `exact_trie_nodes` — Definition.
- `exact_units` — projection.
- `exact_value` — projection.
- `external_counted` — projection.
- `external_events` — projection.
- `external_input_budget` — projection.
- `external_source` — projection.
- `external_value` — projection.
- `ide_fact_body` — Definition.
- `ide_option_body` — Definition.
- `pre_external_encode` — Definition.
- `pre_external_encode_work` — Definition.
- `pre_frg_source_encoding` — Definition.
- `pre_frg_source_work` — Definition.
- `pre_map_fixed_charge` — Definition.
- `pre_map_literal_work` — Definition.
- `pre_pair_encode_body` — Definition.
- `pre_triple_source_encoding` — Definition.
- `pre_triple_source_work` — Definition.

### `Galois.Tests.Analyses.AnalysesAuditIdeExamples`

Card: AUD-IDE.

Owned path: `tests/Analyses/AnalysesAuditIdeExamples.v`.

- `audit_ide_body_nonempty_full_source` — future Theorem.
- `audit_ide_body_nonempty_full_source_statement` — Definition.
- `audit_ide_constant_edge` — Definition.
- `audit_ide_identity_edge` — Definition.

### `Galois.Tests.Analyses.AnalysesAuditIdeLegacyExamples`

Card: AUD-IDE-LEGACY.

Owned path: `tests/Analyses/AnalysesAuditIdeLegacyExamples.v`.

- `ide_vectors_empty_range` — Example.
- `ide_vectors_two_by_two` — Example.

### `Galois.Tests.Analyses.AnalysesAuditPreExamples`

Card: AUD-SP.

Owned path: `tests/Analyses/AnalysesAuditPreExamples.v`.

- `audit_pre_existing_caller_consumer` — future Theorem.
- `audit_pre_existing_caller_consumer_statement` — Definition.
- `audit_pre_existing_client_certificate` — future Theorem.
- `audit_pre_existing_client_certificate_statement` — Definition.

### `Galois.Tests.Analyses.AnalysesAuditPreSourceExamples`

Card: AUD-SP-SOURCE.

Owned path: `tests/Analyses/AnalysesAuditPreSourceExamples.v`.

- `audit_pre_existing_source_consumer` — future Theorem.
- `audit_pre_existing_source_consumer_statement` — Definition.
- `audit_pre_nonempty_full_source` — future Theorem.
- `audit_pre_nonempty_full_source_statement` — Definition.

### `Galois.Tests.Analyses.AnalysesAuditSourceExamples`

Card: AUD-SOURCE-BASE.

Owned path: `tests/Analyses/AnalysesAuditSourceExamples.v`.

- `audit_bool_or_adapter_closed` — Example.

<!-- AUD-API-IDE-PRE-NAMES-END -->

<!-- AUD-API-CL-MEM-NAMES-BEGIN -->

## AnalysesAuditMemoryClobbersSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_clobber_search_event` (Definition); `docs/api/analyses.md`.
- `audit_clobbers_source_run` (Record); `docs/api/analyses.md`.
- `audit_clobbers_source_result` (field); `docs/api/analyses.md`.
- `audit_clobbers_source_index` (field); `docs/api/analyses.md`.
- `audit_clobbers_source_search` (field); `docs/api/analyses.md`.
- `audit_clobbers_source_elements` (field); `docs/api/analyses.md`.
- `audit_clobbers_source_distinct` (field); `docs/api/analyses.md`.
- `audit_clobbers_source_roots` (field); `docs/api/analyses.md`.
- `audit_memory_clobbers_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_clobbers_full_source_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_clobbers_whole_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_clobbers_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_clobbers_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryClobbersSourceAdequacy`.

- `audit_memory_clobbers_source_erases`: `audit_memory_clobbers_source_erases_statement`; owner
  AUD-MW-SEARCH.
- `audit_memory_clobbers_whole_input_bound`: `audit_memory_clobbers_whole_input_bound_statement`;
  owner AUD-MW-SEARCH.

## AnalysesAuditMemoryDisjoint

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_disjoint_event` (Inductive); `docs/api/analyses.md`.
- `AuditDisjointOuter` (constructor); `docs/api/analyses.md`.
- `AuditDisjointInner` (constructor); `docs/api/analyses.md`.
- `AuditDisjointPair` (constructor); `docs/api/analyses.md`.
- `audit_disjoint_pair` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_inner` (Fixpoint); `docs/api/analyses.md`.
- `audit_footprints_disjoint` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_scopes_disjoint` (Definition); `docs/api/analyses.md`.
- `audit_footprints_disjoint_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_scopes_disjoint_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_pairs` (Fixpoint); `docs/api/analyses.md`.
- `audit_disjoint_pairs_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_pair_work` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_disjoint_inner_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_disjoint_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_disjoint_source_work_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryDisjointAdequacy`.

- `audit_footprints_disjoint_erases`: `audit_footprints_disjoint_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_scopes_disjoint_erases`: `audit_memory_scopes_disjoint_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_disjoint_pairs_count`: `audit_disjoint_pairs_count_statement`; owner AUD-MW-TABLES.
- `audit_disjoint_source_work`: `audit_disjoint_source_work_statement`; owner AUD-MW-TABLES.

## AnalysesAuditMemoryDistinct

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_distinct_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoryDistinctCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoryDistinctProbe` (constructor); `docs/api/analyses.md`.
- `AuditMemoryDistinctAdd` (constructor); `docs/api/analyses.md`.
- `AuditMemoryDistinctKeep` (constructor); `docs/api/analyses.md`.
- `audit_memory_distinct_from` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_distinct` (Definition); `docs/api/analyses.md`.
- `audit_memory_distinct_from_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_distinct_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_distinct_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_distinct_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_distinct_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryDistinctAdequacy`.

- `audit_memory_distinct_from_erases`: `audit_memory_distinct_from_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_distinct_erases`: `audit_memory_distinct_erases_statement`; owner AUD-MW-TABLES.
- `audit_memory_distinct_source_bound`: `audit_memory_distinct_source_bound_statement`; owner
  AUD-MW-TABLES.

## AnalysesAuditMemoryEffects

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_effect_event` (Inductive); `docs/api/analyses.md`.
- `AuditEffectRow` (constructor); `docs/api/analyses.md`.
- `AuditEffectSet` (constructor); `docs/api/analyses.md`.
- `audit_memory_effects_from` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_effects_from_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_effects_from_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_map_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_effect_events_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_effects_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_effects_work_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_get_event` (Inductive); `docs/api/analyses.md`.
- `AuditEffectEdgeGet` (constructor); `docs/api/analyses.md`.
- `AuditEffectIndexGet` (constructor); `docs/api/analyses.md`.
- `audit_memory_effect_get` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_get_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_get_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_get_work` (Fixpoint); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryEffectsAdequacy`.

- `audit_memory_effects_from_erases`: `audit_memory_effects_from_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_effects_from_count`: `audit_memory_effects_from_count_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_effects_work_bound`: `audit_memory_effects_work_bound_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_effect_get_erases`: `audit_memory_effect_get_erases_statement`; owner AUD-MW-TABLES.
- `audit_memory_effect_get_count`: `audit_memory_effect_get_count_statement`; owner AUD-MW-TABLES.

## AnalysesAuditMemoryEncoding

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `scope_code` (Definition); `docs/api/analyses.md`.
- `memo_key` (Definition); `docs/api/analyses.md`.
- `audit_memory_version_event` (Inductive); `docs/api/analyses.md`.
- `AuditVersionLive` (constructor); `docs/api/analyses.md`.
- `AuditVersionPhi` (constructor); `docs/api/analyses.md`.
- `AuditVersionDef` (constructor); `docs/api/analyses.md`.
- `audit_memory_version_encode` (Definition); `docs/api/analyses.md`.
- `audit_memory_version_encode_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_footprint_encode` (Definition); `docs/api/analyses.md`.
- `audit_memory_footprint_encode_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_encode` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_encode_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_key_encode` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_key_encode_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_version_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_footprint_event` (Definition); `docs/api/analyses.md`.
- `audit_memory_footprint_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_event` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_key_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_footprint_list_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_scope_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_work_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryEncodingAdequacy`.

- `audit_memory_version_encode_erases`: `audit_memory_version_encode_erases_statement`; owner
  AUD-MEM-BASE.
- `audit_memory_footprint_encode_erases`: `audit_memory_footprint_encode_erases_statement`; owner
  AUD-MEM-BASE.
- `audit_memory_scope_encode_erases`: `audit_memory_scope_encode_erases_statement`; owner
  AUD-MEM-BASE.
- `audit_memory_memo_key_encode_erases`: `audit_memory_memo_key_encode_erases_statement`; owner
  AUD-MEM-BASE.
- `audit_memory_scope_work_bound`: `audit_memory_scope_work_bound_statement`; owner AUD-MEM-BASE.

## AnalysesAuditMemoryFamilyClosure

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_internal_body_closure_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_source_closure_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_legacy_source_closure_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_source_closure_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_complete_source_contract_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_snapshot_plain_closure_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_adapted_source_contract_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_contract_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_public_source_contract_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryFamilyClosureAdequacy`.

- `audit_memory_internal_body_closure`: `audit_memory_internal_body_closure_statement`; owner
  AUD-MW.
- `audit_memory_memo_source_closure`: `audit_memory_memo_source_closure_statement`; owner AUD-MW.
- `audit_memory_legacy_source_closure`: `audit_memory_legacy_source_closure_statement`; owner
  AUD-MW.
- `audit_memory_phi_source_closure`: `audit_memory_phi_source_closure_statement`; owner AUD-MW.
- `audit_memory_complete_source_contract`: `audit_memory_complete_source_contract_statement`;
  owner AUD-MW.
- `audit_memory_snapshot_plain_closure`: `audit_memory_snapshot_plain_closure_statement`; owner
  AUD-MW.
- `audit_memory_adapted_source_contract`: `audit_memory_adapted_source_contract_statement`; owner
  AUD-MW.
- `audit_memory_memo_legacy_contract`: `audit_memory_memo_legacy_contract_statement`; owner AUD-MW.
- `audit_memory_public_source_contract`: `audit_memory_public_source_contract_statement`; owner
  AUD-MW.

## AnalysesAuditMemoryGraphCallbacks

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_snapshot_graph_body` (Inductive); `docs/api/analyses.md`.
- `AuditSnapshotNodeBody` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotOutBody` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotTargetBody` (constructor); `docs/api/analyses.md`.
- `audit_snapshot_graph_body_work` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_graph_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_target_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_snapshot_graph_input_budget` (Fixpoint); `docs/api/analyses.md`.

## AnalysesAuditMemoryIndex

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_index_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoryIndexNil` (constructor); `docs/api/analyses.md`.
- `AuditMemoryIndexPut` (constructor); `docs/api/analyses.md`.
- `audit_memory_result_index` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_result_index_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_result_index_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_index_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_index_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_result_index_work_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryIndexAdequacy`.

- `audit_memory_result_index_erases`: `audit_memory_result_index_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_result_index_count`: `audit_memory_result_index_count_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_result_index_work_bound`: `audit_memory_result_index_work_bound_statement`; owner
  AUD-MW-TABLES.

## AnalysesAuditMemoryInitial

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `AuditMemoryInitialEvents` (constructor); `docs/api/analyses.md`.
- `audit_memory_initial_events` (Record); `docs/api/analyses.md`.
- `audit_memory_initial_prepare` (field); `docs/api/analyses.md`.
- `audit_memory_initial_table` (field); `docs/api/analyses.md`.
- `audit_memory_initial` (Definition); `docs/api/analyses.md`.
- `audit_memory_initial_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_initial_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryInitialAdequacy`.

- `audit_memory_initial_erases`: `audit_memory_initial_erases_statement`; owner AUD-MW-MEMO.
- `audit_memory_initial_source_bound`: `audit_memory_initial_source_bound_statement`; owner
  AUD-MW-MEMO.

## AnalysesAuditMemoryInputBudget

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_version_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_footprint_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_scope_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_key_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_encoders_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_pair_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_disjoint_inner_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_disjoint_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_scopes_disjoint_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_get_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_operand_calls_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_raw_next_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_raw_next_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_empty_disjoint_input_budget` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryInputBudgetAdequacy`.

- `audit_memory_encoders_input_bound`: `audit_memory_encoders_input_bound_statement`; owner
  AUD-MW-TABLES.
- `audit_raw_next_whole_input_bound`: `audit_raw_next_whole_input_bound_statement`; owner
  AUD-MW-TABLES.

## AnalysesAuditMemoryLegacyBytes

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_projection_historical_bytes_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyBytesAdequacy`.

- `audit_legacy_projection_historical_bytes`:
  `audit_legacy_projection_historical_bytes_statement`; owner AUD-MW-LEGACY.

## AnalysesAuditMemoryLegacyCfg

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_cfg_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacyCfgRowCase` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCfgOutCall` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCfgTargetCall` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCfgDistinct` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCfgPairCase` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCfgPair` (constructor); `docs/api/analyses.md`.
- `audit_legacy_cfg_targets` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_cfg_pairs` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_cfg_row` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_rows` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_row_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_cfg_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyCfgAdequacy`.

- `audit_legacy_cfg_erases`: `audit_legacy_cfg_erases_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_cfg_source_bound`: `audit_legacy_cfg_source_bound_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyChecker

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_pair_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacyPairLoadProbe` (constructor); `docs/api/analyses.md`.
- `AuditLegacyPairOwnerCompare` (constructor); `docs/api/analyses.md`.
- `AuditLegacyPairDefinitionProbe` (constructor); `docs/api/analyses.md`.
- `AuditLegacyPairSuccessors` (constructor); `docs/api/analyses.md`.
- `AuditLegacyPairReads` (constructor); `docs/api/analyses.md`.
- `AuditLegacyPairSlice` (constructor); `docs/api/analyses.md`.
- `audit_legacy_pair_check_full` (Definition); `docs/api/analyses.md`.
- `audit_legacy_checker_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacyCheckerCase` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCheckerMissing` (constructor); `docs/api/analyses.md`.
- `AuditLegacyCheckerCandidate` (constructor); `docs/api/analyses.md`.
- `audit_legacy_check_nodes` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_pair_check_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_pair_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_pair_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_checker_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_check_nodes_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_load_graph` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_load_pair_fixture` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_load_fixture_retains_body_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_owner_pair_fixture` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_owner_fixture_retains_body_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_head_two_nodes_fixture` (Definition); `docs/api/analyses.md`.
- `audit_legacy_false_head_two_nodes_fixture_retains_tail_statement` (Definition);
  `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyCheckerAdequacy`.

- `audit_legacy_pair_check_erases`: `audit_legacy_pair_check_erases_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_check_nodes_erases`: `audit_legacy_check_nodes_erases_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_false_load_fixture_retains_body`:
  `audit_legacy_false_load_fixture_retains_body_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_false_owner_fixture_retains_body`:
  `audit_legacy_false_owner_fixture_retains_body_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_false_head_two_nodes_fixture_retains_tail`:
  `audit_legacy_false_head_two_nodes_fixture_retains_tail_statement`; owner AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyGuard

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_guard_event` (Inductive); `docs/api/analyses.md`.
- `AuditGuardSource` (constructor); `docs/api/analyses.md`.
- `AuditGuardNodeEncode` (constructor); `docs/api/analyses.md`.
- `AuditGuardEqual` (constructor); `docs/api/analyses.md`.
- `AuditGuardReached` (constructor); `docs/api/analyses.md`.
- `AuditGuardListed` (constructor); `docs/api/analyses.md`.
- `audit_legacy_guard` (Definition); `docs/api/analyses.md`.
- `audit_legacy_guard_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_guard_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_guard_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_guard_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_guard_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyGuardAdequacy`.

- `audit_legacy_guard_erases`: `audit_legacy_guard_erases_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_guard_count`: `audit_legacy_guard_count_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_guard_source_bound`: `audit_legacy_guard_source_bound_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyInputBudget

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_targets_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_cfg_row_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_overlap_row_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_overlap_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_slice_nodes_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_sum_vertex_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_dfs_vertices` (Definition); `docs/api/analyses.md`.
- `audit_legacy_dfs_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_full_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_pair_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_successors_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_check_nodes_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_cfg_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyInputBudgetAdequacy`.

- `audit_legacy_no_clobber_whole_input_bound`:
  `audit_legacy_no_clobber_whole_input_bound_statement`; owner AUD-MW-LEGACY-BASE.
- `audit_legacy_cfg_whole_input_bound`: `audit_legacy_cfg_whole_input_bound_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyNoClobber

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_prepare_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_events` (Record); `docs/api/analyses.md`.
- `audit_legacy_check_cfg_events` (field); `docs/api/analyses.md`.
- `audit_legacy_check_prepare_events` (field); `docs/api/analyses.md`.
- `audit_legacy_check_reached_events` (field); `docs/api/analyses.md`.
- `audit_legacy_check_nodes_events` (field); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_no_clobber_erases_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyNoClobberAdequacy`.

- `audit_legacy_no_clobber_erases`: `audit_legacy_no_clobber_erases_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyOverlap

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_overlap_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacyOverlapOuter` (constructor); `docs/api/analyses.md`.
- `AuditLegacyOverlapInner` (constructor); `docs/api/analyses.md`.
- `AuditLegacyOverlapPair` (constructor); `docs/api/analyses.md`.
- `audit_legacy_overlap_pair` (Definition); `docs/api/analyses.md`.
- `audit_legacy_overlap_inner` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_overlap_exists` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_disjoint` (Definition); `docs/api/analyses.md`.
- `audit_legacy_overlap_pairs` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_disjoint_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_overlap_pair_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_overlap_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_overlap_inner_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_overlap_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_overlap_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyOverlapAdequacy`.

- `audit_legacy_disjoint_erases`: `audit_legacy_disjoint_erases_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_overlap_pair_count`: `audit_legacy_overlap_pair_count_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_overlap_source_bound`: `audit_legacy_overlap_source_bound_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacyProjectionSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_projection_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacyProjectionProposal` (constructor); `docs/api/analyses.md`.
- `AuditLegacyProjectionRetainNone` (constructor); `docs/api/analyses.md`.
- `AuditLegacyProjectionRetain` (constructor); `docs/api/analyses.md`.
- `audit_legacy_projection_proposal_event` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_retain_event` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_definition_event` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_definition_source` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_definition_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_projection_check_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_definition_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_whole_input_bound_at` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_whole_input_bound_adapted_at` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_source_erases_at` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_source_erases_at` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_check_whole_input_bound_adapted_statement` (Definition);
  `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyProjectionSourceAdequacy`.

- `audit_legacy_projection_source_erases`: `audit_legacy_projection_source_erases_statement`;
  owner AUD-MW-LEGACY.
- `audit_legacy_projection_check_source_erases`:
  `audit_legacy_projection_check_source_erases_statement`; owner AUD-MW-LEGACY.
- `audit_legacy_projection_check_whole_input_bound`:
  `audit_legacy_projection_check_whole_input_bound_statement`; owner AUD-MW-LEGACY.
- `audit_legacy_projection_check_whole_input_bound_adapted`:
  `audit_legacy_projection_check_whole_input_bound_adapted_statement`; owner AUD-MW-LEGACY.

## AnalysesAuditMemoryLegacyProposalSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_source_proposal_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacySourceLoad` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceGuard` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceEffect` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceBefore` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceReadTest` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceReads` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceClobbers` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceSource` (constructor); `docs/api/analyses.md`.
- `AuditLegacySourceReturn` (constructor); `docs/api/analyses.md`.
- `audit_legacy_finish_proposal` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_source_with` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_full_clobbers` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_source` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_guard_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_with_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_occurrence_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacyProposalSourceAdequacy`.

- `audit_legacy_occurrence_source_erases`: `audit_legacy_occurrence_source_erases_statement`;
  owner AUD-MW-LEGACY.
- `audit_legacy_occurrence_whole_input_bound`:
  `audit_legacy_occurrence_whole_input_bound_statement`; owner AUD-MW-LEGACY.

## AnalysesAuditMemoryLegacySetupSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_setup_run` (Record); `docs/api/analyses.md`.
- `audit_legacy_setup_cfg` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_prepared` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_reached` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_listed` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_table` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_cfg_events` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_prepare_events` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_reached_events` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_edges_events` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_listed_events` (field); `docs/api/analyses.md`.
- `audit_legacy_setup_table_events` (field); `docs/api/analyses.md`.
- `audit_legacy_projection_setup` (Definition); `docs/api/analyses.md`.
- `audit_legacy_setup_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_listed_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_setup_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_legacy_projection_setup_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_setup_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacySetupSourceAdequacy`.

- `audit_legacy_projection_setup_erases`: `audit_legacy_projection_setup_erases_statement`; owner
  AUD-MW-LEGACY.
- `audit_legacy_setup_whole_input_bound`: `audit_legacy_setup_whole_input_bound_statement`; owner
  AUD-MW-LEGACY.

## AnalysesAuditMemoryLegacySlice

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_slice_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacySliceNode` (constructor); `docs/api/analyses.md`.
- `AuditLegacySliceWrite` (constructor); `docs/api/analyses.md`.
- `audit_legacy_slice_nodes` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_slice_nodes_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_slice_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_slice_nodes_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacySliceAdequacy`.

- `audit_legacy_slice_nodes_erases`: `audit_legacy_slice_nodes_erases_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_slice_nodes_source_bound`: `audit_legacy_slice_nodes_source_bound_statement`;
  owner AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacySliceFull

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_dfs_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_legacy_reached_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_full_events` (Record); `docs/api/analyses.md`.
- `audit_legacy_slice_forward_dfs` (field); `docs/api/analyses.md`.
- `audit_legacy_slice_reverse_dfs` (field); `docs/api/analyses.md`.
- `audit_legacy_slice_node_checks` (field); `docs/api/analyses.md`.
- `audit_legacy_slice_full` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_full_source_work` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_full_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_legacy_slice_full_trace_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacySliceFullAdequacy`.

- `audit_legacy_slice_full_erases`: `audit_legacy_slice_full_erases_statement`; owner
  AUD-MW-LEGACY-BASE.
- `audit_legacy_slice_full_trace_bound`: `audit_legacy_slice_full_trace_bound_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryLegacySuccessor

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_legacy_successor_event` (Inductive); `docs/api/analyses.md`.
- `AuditLegacySuccessorLookup` (constructor); `docs/api/analyses.md`.
- `AuditLegacySuccessorMapCase` (constructor); `docs/api/analyses.md`.
- `AuditLegacySuccessorTarget` (constructor); `docs/api/analyses.md`.
- `audit_legacy_successor_map` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_successors_counted` (Definition); `docs/api/analyses.md`.
- `audit_legacy_successor_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_legacy_successors_erases_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryLegacySuccessorAdequacy`.

- `audit_legacy_successors_erases`: `audit_legacy_successors_erases_statement`; owner
  AUD-MW-LEGACY-BASE.

## AnalysesAuditMemoryMemo

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memo_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoActive` (constructor); `docs/api/analyses.md`.
- `AuditMemoLookup` (constructor); `docs/api/analyses.md`.
- `AuditMemoExpand` (constructor); `docs/api/analyses.md`.
- `AuditMemoAddActive` (constructor); `docs/api/analyses.md`.
- `AuditMemoStore` (constructor); `docs/api/analyses.md`.
- `AuditMemoUnion` (constructor); `docs/api/analyses.md`.
- `audit_memo_union` (Definition); `docs/api/analyses.md`.
- `audit_memo_successor_occurrences` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_source_work` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree` (Inductive); `docs/api/analyses.md`.
- `AuditMemoTreeActive` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeDone` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeBusy` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeFuel` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeTerminal` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeBranchComplete` (constructor); `docs/api/analyses.md`.
- `AuditMemoTreeBranchIncomplete` (constructor); `docs/api/analyses.md`.
- `audit_memo_children` (mutual); `docs/api/analyses.md`.
- `AuditMemoChildrenNil` (constructor); `docs/api/analyses.md`.
- `AuditMemoChildrenCons` (constructor); `docs/api/analyses.md`.
- `audit_memo_tree_total_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree_deterministic_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree_source_bound_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree_total_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree_deterministic_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_tree_source_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_query_type` (Definition); `docs/api/analyses.md`.
- `audit_memo_query_execution_contract` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoAdequacy`.

- `audit_memo_tree_total`: `audit_memo_tree_total_statement`; owner AUD-MW-MEMO.
- `audit_memo_tree_deterministic`: `audit_memo_tree_deterministic_statement`; owner AUD-MW-MEMO.
- `audit_memo_tree_source_bound`: `audit_memo_tree_source_bound_statement`; owner AUD-MW-MEMO.

## AnalysesAuditMemoryMemoAdaptedSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_memo_public_whole_input_bound_adapted_statement` (Definition);
  `docs/api/analyses.md`.
- `audit_memory_memo_initial_whole_input_bound_adapted_statement` (Definition);
  `docs/api/analyses.md`.
- `audit_snapshot_query_whole_input_bound_adapted_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_whole_input_bound_adapted_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoAdaptedSourceAdequacy`.

- `audit_memory_memo_public_whole_input_bound_adapted`:
  `audit_memory_memo_public_whole_input_bound_adapted_statement`; owner AUD-MW-MEMO.
- `audit_memory_memo_initial_whole_input_bound_adapted`:
  `audit_memory_memo_initial_whole_input_bound_adapted_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_whole_input_bound_adapted`:
  `audit_snapshot_query_whole_input_bound_adapted_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_refresh_whole_input_bound_adapted`:
  `audit_snapshot_refresh_whole_input_bound_adapted_statement`; owner AUD-MW-MEMO.

## AnalysesAuditMemoryMemoComposition

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_memo_composed_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoCompositionAdequacy`.

- `audit_memory_memo_composed_bound`: `audit_memory_memo_composed_bound_statement`; owner
  AUD-MW-MEMO.

## AnalysesAuditMemoryMemoExecute

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memo_control_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoEnterCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoChildrenCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoCreditCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoPredPositiveCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoPredDoubleCase` (constructor); `docs/api/analyses.md`.
- `audit_memo_pred_double` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_pred` (Definition); `docs/api/analyses.md`.
- `audit_memo_pred_correct_statement` (Definition); `docs/api/analyses.md`.
- `AuditMemoExecution` (constructor); `docs/api/analyses.md`.
- `audit_memo_execution` (Record); `docs/api/analyses.md`.
- `audit_memo_value` (field); `docs/api/analyses.md`.
- `audit_memo_cache` (field); `docs/api/analyses.md`.
- `audit_memo_credit` (field); `docs/api/analyses.md`.
- `audit_memo_body_events` (field); `docs/api/analyses.md`.
- `audit_memo_control_events` (field); `docs/api/analyses.md`.
- `audit_memo_credit_bounded` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_children` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_execute_body` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_tree_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_tree_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query_semantics_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_pred_borrow_fixture` (Example); `docs/api/analyses.md`.
- `audit_memo_execute_zero_credit_fixture` (Example); `docs/api/analyses.md`.
- `audit_memo_execute_terminal_fixture` (Example); `docs/api/analyses.md`.
- `audit_memo_execute_done_preserves_credit_fixture` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoExecuteAdequacy`.

- `audit_memo_pred_correct`: `audit_memo_pred_correct_statement`; owner AUD-MW-MEMO.
- `audit_memo_execute_tree`: `audit_memo_execute_tree_statement`; owner AUD-MW-MEMO.
- `audit_memory_memo_query_semantics`: `audit_memory_memo_query_semantics_statement`; owner
  AUD-MW-MEMO.

## AnalysesAuditMemoryMemoExecuteBound

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memo_credit_width` (Definition); `docs/api/analyses.md`.
- `audit_memo_execution_source_work` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_projection_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query_counted_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_execute_plain_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_query_execution_contract_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoExecuteBoundAdequacy`.

- `audit_memo_execute_projection`: `audit_memo_execute_projection_statement`; owner AUD-MW-MEMO.
- `audit_memo_execute_whole_input_bound`: `audit_memo_execute_whole_input_bound_statement`; owner
  AUD-MW-MEMO.
- `audit_memory_memo_query_counted_erases`: `audit_memory_memo_query_counted_erases_statement`;
  owner AUD-MW-MEMO.
- `audit_memory_memo_query_whole_input_bound`:
  `audit_memory_memo_query_whole_input_bound_statement`; owner AUD-MW-MEMO.
- `audit_memo_execute_plain_erases`: `audit_memo_execute_plain_erases_statement`; owner AUD-MW-MEMO.
- `audit_memory_memo_query_execution_contract`:
  `audit_memory_memo_query_execution_contract_statement`; owner AUD-MW-MEMO.

## AnalysesAuditMemoryMemoLegacyPlain

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memo_legacy_request` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_one` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_nodes` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_project` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_semantics_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoLegacyPlainAdequacy`.

- `audit_memory_memo_legacy_semantics`: `audit_memory_memo_legacy_semantics_statement`; owner
  AUD-MW-LEGACY.

## AnalysesAuditMemoryMemoLegacySource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `AuditMemoLegacyReceipt` (constructor); `docs/api/analyses.md`.
- `audit_memo_legacy_receipt` (Record); `docs/api/analyses.md`.
- `audit_memo_legacy_scope_body` (field); `docs/api/analyses.md`.
- `audit_memo_legacy_execution` (field); `docs/api/analyses.md`.
- `audit_memo_legacy_proposal_event` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_one_event` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_receipt_work` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_setup_counted` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_clobber_counted` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_receipt_after` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_legacy_one_counted` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_nodes_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoLegacyNodesCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoLegacyNodesOne` (constructor); `docs/api/analyses.md`.
- `AuditMemoLegacyNodesStore` (constructor); `docs/api/analyses.md`.
- `audit_memo_legacy_nodes_counted` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_project_counted` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_one_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_legacy_nodes_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_legacy_query_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_prefix_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_finish_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_one_input_budget` (Inductive); `docs/api/analyses.md`.
- `AuditMemoLegacyBudgetNoQuery` (constructor); `docs/api/analyses.md`.
- `AuditMemoLegacyBudgetQuery` (constructor); `docs/api/analyses.md`.
- `audit_memo_legacy_nodes_input_budget` (Inductive); `docs/api/analyses.md`.
- `AuditMemoLegacyBudgetNil` (constructor); `docs/api/analyses.md`.
- `AuditMemoLegacyBudgetCons` (constructor); `docs/api/analyses.md`.
- `audit_memo_legacy_lookup_counted` (Definition); `docs/api/analyses.md`.
- `audit_memo_legacy_lookup_source_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_check_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_source_erases_at` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_source_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_check_source_work` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_whole_input_bound_at` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_legacy_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoLegacySourceAdequacy`.

- `audit_memo_legacy_lookup_source_bound`: `audit_memo_legacy_lookup_source_bound_statement`;
  owner AUD-MW-LEGACY.
- `audit_memory_memo_legacy_source_erases`: `audit_memory_memo_legacy_source_erases_statement`;
  owner AUD-MW-LEGACY.
- `audit_memory_memo_legacy_whole_input_bound`:
  `audit_memory_memo_legacy_whole_input_bound_statement`; owner AUD-MW-LEGACY.

## AnalysesAuditMemoryMemoPlain

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `AuditPlainMemoResult` (constructor); `docs/api/analyses.md`.
- `audit_plain_memo_result` (Record); `docs/api/analyses.md`.
- `audit_plain_memo_value` (field); `docs/api/analyses.md`.
- `audit_plain_memo_cache` (field); `docs/api/analyses.md`.
- `audit_plain_memo_credit` (field); `docs/api/analyses.md`.
- `audit_plain_memo_bounded` (Definition); `docs/api/analyses.md`.
- `audit_plain_memo_children` (Fixpoint); `docs/api/analyses.md`.
- `audit_plain_memo_body` (Definition); `docs/api/analyses.md`.
- `audit_memo_compute` (Definition); `docs/api/analyses.md`.
- `audit_plain_memo_terminal_fixture` (Example); `docs/api/analyses.md`.

## AnalysesAuditMemoryMemoPublicSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_memo_public_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_public_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_public_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_initial_source_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_initial_source_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_initial_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoPublicSourceAdequacy`.

- `audit_memory_memo_public_source_erases`: `audit_memory_memo_public_source_erases_statement`;
  owner AUD-MW-MEMO.
- `audit_memory_memo_public_whole_input_bound`:
  `audit_memory_memo_public_whole_input_bound_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_source_erases`: `audit_snapshot_query_source_erases_statement`; owner
  AUD-MW-MEMO.
- `audit_memory_memo_initial_source_erases`: `audit_memory_memo_initial_source_erases_statement`;
  owner AUD-MW-MEMO.
- `audit_memory_memo_initial_whole_input_bound`:
  `audit_memory_memo_initial_whole_input_bound_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_whole_input_bound`: `audit_snapshot_query_whole_input_bound_statement`;
  owner AUD-MW-MEMO.

## AnalysesAuditMemoryMemoSnapshot

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_snapshot_memo_cache` (Record); `docs/api/analyses.md`.
- `audit_cache_snapshot` (field); `docs/api/analyses.md`.
- `audit_cache_prepared` (field); `docs/api/analyses.md`.
- `audit_cache_effect_index` (field); `docs/api/analyses.md`.
- `audit_cache_entries` (field); `docs/api/analyses.md`.
- `audit_snapshot_refresh_event` (Inductive); `docs/api/analyses.md`.
- `AuditSnapshotEpochCompare` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotRefreshHit` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotRefreshMiss` (constructor); `docs/api/analyses.md`.
- `audit_snapshot_prepare_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_out_adapter` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_effect_adapter` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_match_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_match_execution_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_miss_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_miss_execution_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_cache_valid` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_observation_context_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_epoch_compare_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_source_work` (Fixpoint); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoSnapshotAdequacy`.

- `audit_snapshot_refresh_match`: `audit_snapshot_refresh_match_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_refresh_match_execution`: `audit_snapshot_refresh_match_execution_statement`;
  owner AUD-MW-MEMO.
- `audit_snapshot_refresh_miss`: `audit_snapshot_refresh_miss_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_refresh_miss_execution`: `audit_snapshot_refresh_miss_execution_statement`;
  owner AUD-MW-MEMO.
- `audit_snapshot_refresh_observation_context`:
  `audit_snapshot_refresh_observation_context_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_refresh_epoch_compare_erases`:
  `audit_snapshot_refresh_epoch_compare_erases_statement`; owner AUD-MW-MEMO.

## AnalysesAuditMemoryMemoSnapshotSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_snapshot_refresh_source_event` (Inductive); `docs/api/analyses.md`.
- `AuditSnapshotSourceEpoch` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotSourceHit` (constructor); `docs/api/analyses.md`.
- `AuditSnapshotSourceMiss` (constructor); `docs/api/analyses.md`.
- `audit_snapshot_refresh_source` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_full_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_snapshot_refresh_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_source_hit_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_source_miss_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_saved_values_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoSnapshotSourceAdequacy`.

- `audit_snapshot_refresh_source_hit`: `audit_snapshot_refresh_source_hit_statement`; owner
  AUD-MW-MEMO.
- `audit_snapshot_refresh_source_miss`: `audit_snapshot_refresh_source_miss_statement`; owner
  AUD-MW-MEMO.
- `audit_snapshot_refresh_whole_input_bound`:
  `audit_snapshot_refresh_whole_input_bound_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_saved_values`: `audit_snapshot_query_saved_values_statement`; owner
  AUD-MW-MEMO.

## AnalysesAuditMemoryMemoWhole

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memo_build_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memo_union_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_active_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_lookup_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_store_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_add_active_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_probe_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memo_input_budget_run` (Inductive); `docs/api/analyses.md`.
- `AuditMemoBudgetActive` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetDone` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetBusy` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetFuel` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetTerminal` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetBranch` (constructor); `docs/api/analyses.md`.
- `audit_memo_children_input_budget_run` (mutual); `docs/api/analyses.md`.
- `AuditMemoBudgetChildrenNil` (constructor); `docs/api/analyses.md`.
- `AuditMemoBudgetChildrenCons` (constructor); `docs/api/analyses.md`.
- `audit_memo_whole_input_bound_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_input_budget_deterministic_at` (Definition); `docs/api/analyses.md`.
- `audit_memo_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_input_budget_deterministic_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_memo_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memo_union_budget_nonempty` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryMemoWholeAdequacy`.

- `audit_memo_whole_input_bound`: `audit_memo_whole_input_bound_statement`; owner AUD-MW-MEMO.
- `audit_memo_input_budget_deterministic`: `audit_memo_input_budget_deterministic_statement`;
  owner AUD-MW-MEMO.
- `audit_memory_memo_whole_input_bound`: `audit_memory_memo_whole_input_bound_statement`; owner
  AUD-MW-MEMO.

## AnalysesAuditMemoryPhiAdaptedSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_phi_prune_whole_input_bound_adapted_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_optional_closure_source_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_total_closure_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiAdaptedSourceAdequacy`.

- `audit_memory_phi_prune_whole_input_bound_adapted`:
  `audit_memory_phi_prune_whole_input_bound_adapted_statement`; owner AUD-MP.
- `audit_phi_optional_closure_source_bound`: `audit_phi_optional_closure_source_bound_statement`;
  owner AUD-MP.
- `audit_phi_total_closure_source_bound`: `audit_phi_total_closure_source_bound_statement`; owner
  AUD-MP.

## AnalysesAuditMemoryPhiConsumer

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_closure_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiClosureCall` (constructor); `docs/api/analyses.md`.
- `AuditPhiClosureRead` (constructor); `docs/api/analyses.md`.
- `audit_phi_output_optional_call` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_total_call` (Definition); `docs/api/analyses.md`.
- `audit_phi_closure_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_closure_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_closure_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_optional_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_fields_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_prune` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_prune_semantics_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_producer_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_closure_none_skips_representative` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiConsumerAdequacy`.

- `audit_phi_closure_whole_input_bound`: `audit_phi_closure_whole_input_bound_statement`; owner
  AUD-MP.
- `audit_phi_output_optional_erases`: `audit_phi_output_optional_erases_statement`; owner AUD-MP.
- `audit_phi_output_fields_erases`: `audit_phi_output_fields_erases_statement`; owner AUD-MP.
- `audit_memory_phi_prune_semantics`: `audit_memory_phi_prune_semantics_statement`; owner AUD-MP.
- `audit_memory_phi_producer_erases`: `audit_memory_phi_producer_erases_statement`; owner AUD-MP.

## AnalysesAuditMemoryPhiInputBudget

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_get_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_set_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_operand_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_rows_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_dependency_row_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_self_edges_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_mark_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_component_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_cycles_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_rep_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_compare_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_all_same_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_resolve_step_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_pass_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_output_keep_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_filter_nodes_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_filter_versions_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_output_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_graph_targets_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_graph_callback_envelope` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_producer_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiInputBudgetAdequacy`.

- `audit_phi_producer_whole_input_bound`: `audit_phi_producer_whole_input_bound_statement`; owner
  AUD-MP.

## AnalysesAuditMemoryPhiPlain

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_compute_rep` (Definition); `docs/api/analyses.md`.
- `audit_phi_compute_step` (Definition); `docs/api/analyses.md`.
- `audit_phi_compute_output` (Definition); `docs/api/analyses.md`.
- `audit_phi_compute` (Definition); `docs/api/analyses.md`.
- `audit_phi_plain_kept_live_fixture` (Example); `docs/api/analyses.md`.

## AnalysesAuditMemoryPhiPrepare

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_prepare_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiInputs` (constructor); `docs/api/analyses.md`.
- `AuditPhiGraph` (constructor); `docs/api/analyses.md`.
- `AuditPhiPrepared` (constructor); `docs/api/analyses.md`.
- `AuditPhiScc` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycles` (constructor); `docs/api/analyses.md`.
- `audit_phi_prepare_dependencies` (Definition); `docs/api/analyses.md`.
- `audit_phi_prepare_dependencies_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_prepare_phase_count_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiPrepareAdequacy`.

- `audit_phi_prepare_dependencies_erases`: `audit_phi_prepare_dependencies_erases_statement`;
  owner AUD-MP.
- `audit_phi_prepare_phase_count`: `audit_phi_prepare_phase_count_statement`; owner AUD-MP.

## AnalysesAuditMemoryPhiProducer

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_producer_rep` (Definition); `docs/api/analyses.md`.
- `audit_phi_graph_callback_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiGraphEncodeBody` (constructor); `docs/api/analyses.md`.
- `AuditPhiGraphOutBody` (constructor); `docs/api/analyses.md`.
- `audit_phi_graph_callback_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_prepare_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_phi_scc_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_output` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiOutputPhiCase` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputRepRead` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputRepEncode` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputRepCompare` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputSetBuild` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputPhiProbe` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputVersionCase` (constructor); `docs/api/analyses.md`.
- `AuditPhiOutputVersionProbe` (constructor); `docs/api/analyses.md`.
- `audit_phi_output_keep_phis` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_output_filter_nodes` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_output_filter_versions` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_producer_output_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_dependency_row_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiDependencyRowGet` (constructor); `docs/api/analyses.md`.
- `AuditPhiDependencyRowCase` (constructor); `docs/api/analyses.md`.
- `AuditPhiDependencyEdgeKeep` (constructor); `docs/api/analyses.md`.
- `audit_phi_dependency_row_entries` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_dependency_row` (Definition); `docs/api/analyses.md`.
- `audit_phi_dependency_rows_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_dependency_graph_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_dependency_row_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_dependency_rows_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_cycle_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiCycleComponent` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleSuccessors` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleEdgeCase` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleTarget` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleEncode` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleCompare` (constructor); `docs/api/analyses.md`.
- `AuditPhiCycleMark` (constructor); `docs/api/analyses.md`.
- `audit_phi_cycle_self_edges` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_component_cyclic_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_cycle_mark_nodes` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_cycle_flags_from` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_cycle_flags_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_cycle_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_cycle_flags_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_output_counted_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_run` (Record); `docs/api/analyses.md`.
- `audit_phi_run_index` (field); `docs/api/analyses.md`.
- `audit_phi_run_order` (field); `docs/api/analyses.md`.
- `audit_phi_run_representatives` (field); `docs/api/analyses.md`.
- `audit_phi_run_output` (field); `docs/api/analyses.md`.
- `audit_phi_run_output_events` (field); `docs/api/analyses.md`.
- `audit_phi_run_rows` (field); `docs/api/analyses.md`.
- `audit_phi_run_dependency_rows` (field); `docs/api/analyses.md`.
- `audit_phi_run_preparation` (field); `docs/api/analyses.md`.
- `audit_phi_run_graph_preparation` (field); `docs/api/analyses.md`.
- `audit_phi_run_scc_events` (field); `docs/api/analyses.md`.
- `audit_phi_run_cycle_events` (field); `docs/api/analyses.md`.
- `audit_phi_run_resolution` (field); `docs/api/analyses.md`.
- `audit_phi_produce` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_resolution_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_index_source_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_output_shape_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_producer_phase_counts_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_singleton_cycle_scans_later_edge` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiProducerAdequacy`.

- `audit_phi_cycle_flags_erases`: `audit_phi_cycle_flags_erases_statement`; owner AUD-MP.
- `audit_phi_output_counted_erases`: `audit_phi_output_counted_erases_statement`; owner AUD-MP.
- `audit_phi_producer_resolution`: `audit_phi_producer_resolution_statement`; owner AUD-MP.
- `audit_phi_producer_index_source`: `audit_phi_producer_index_source_statement`; owner AUD-MP.
- `audit_phi_producer_output_shape`: `audit_phi_producer_output_shape_statement`; owner AUD-MP.
- `audit_phi_producer_phase_counts`: `audit_phi_producer_phase_counts_statement`; owner AUD-MP.

## AnalysesAuditMemoryPhiPublic

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_phi_prune_wf_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_prune_pack` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_graph_pack` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_public_semantics_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_public_projection_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiPublicAdequacy`.

- `audit_memory_phi_prune_wf`: `audit_memory_phi_prune_wf_statement`; owner AUD-MP.
- `audit_memory_phi_public_semantics`: `audit_memory_phi_public_semantics_statement`; owner AUD-MP.
- `audit_memory_phi_public_projection`: `audit_memory_phi_public_projection_statement`; owner
  AUD-MP.

## AnalysesAuditMemoryPhiResolve

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_resolve_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiCycleProbe` (constructor); `docs/api/analyses.md`.
- `AuditPhiInputsProbe` (constructor); `docs/api/analyses.md`.
- `AuditPhiRepresentative` (constructor); `docs/api/analyses.md`.
- `AuditPhiVersionEncode` (constructor); `docs/api/analyses.md`.
- `AuditPhiCompare` (constructor); `docs/api/analyses.md`.
- `AuditPhiForall` (constructor); `docs/api/analyses.md`.
- `AuditPhiWrite` (constructor); `docs/api/analyses.md`.
- `audit_phi_rep` (Definition); `docs/api/analyses.md`.
- `audit_phi_compare` (Definition); `docs/api/analyses.md`.
- `audit_phi_all_same` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_resolve_step` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_step_refines_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_resolve_source_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_source_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_all` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_resolve_all_refines_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_resolve_all_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_resolve_all_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiResolveAdequacy`.

- `audit_phi_resolve_step_refines`: `audit_phi_resolve_step_refines_statement`; owner AUD-MP.
- `audit_phi_resolve_source_bound`: `audit_phi_resolve_source_bound_statement`; owner AUD-MP.
- `audit_phi_resolve_all_refines`: `audit_phi_resolve_all_refines_statement`; owner AUD-MP.
- `audit_phi_resolve_all_source_bound`: `audit_phi_resolve_all_source_bound_statement`; owner
  AUD-MP.

## AnalysesAuditMemoryPhiRows

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_distinct_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiDistinctCase` (constructor); `docs/api/analyses.md`.
- `AuditPhiDistinctProbe` (constructor); `docs/api/analyses.md`.
- `AuditPhiDistinctAdd` (constructor); `docs/api/analyses.md`.
- `AuditPhiDistinctKeep` (constructor); `docs/api/analyses.md`.
- `audit_phi_distinct_from` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_row_event` (Inductive); `docs/api/analyses.md`.
- `AuditPhiPred` (constructor); `docs/api/analyses.md`.
- `AuditPhiDistinctKeys` (constructor); `docs/api/analyses.md`.
- `AuditPhiRowOperand` (constructor); `docs/api/analyses.md`.
- `AuditPhiRowStore` (constructor); `docs/api/analyses.md`.
- `audit_phi_row_operands` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_input_row` (Definition); `docs/api/analyses.md`.
- `audit_phi_input_rows` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_distinct_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_input_rows_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_rows_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_input_rows_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_phi_distinct_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_rows_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_rows_source_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_input_rows_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiRowsAdequacy`.

- `audit_phi_distinct_erases`: `audit_phi_distinct_erases_statement`; owner AUD-MP.
- `audit_phi_input_rows_erases`: `audit_phi_input_rows_erases_statement`; owner AUD-MP.
- `audit_phi_input_rows_count`: `audit_phi_input_rows_count_statement`; owner AUD-MP.
- `audit_phi_input_rows_source_bound`: `audit_phi_input_rows_source_bound_statement`; owner AUD-MP.

## AnalysesAuditMemoryPhiSetup

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_phi_input_graph_body` (Inductive); `docs/api/analyses.md`.
- `AuditPhiInputNodeBody` (constructor); `docs/api/analyses.md`.
- `AuditPhiInputOutBody` (constructor); `docs/api/analyses.md`.
- `AuditPhiInputTargetBody` (constructor); `docs/api/analyses.md`.
- `audit_phi_input_graph_body_work` (Definition); `docs/api/analyses.md`.
- `audit_phi_input_graph_callbacks` (Definition); `docs/api/analyses.md`.
- `audit_phi_predecessors_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_prune_counted` (Definition); `docs/api/analyses.md`.
- `audit_phi_input_targets_envelope` (Fixpoint); `docs/api/analyses.md`.
- `audit_phi_input_graph_envelope` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_phi_prune_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_phi_prune_counted_erases_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiSetupAdequacy`.

- `audit_memory_phi_prune_whole_input_bound`:
  `audit_memory_phi_prune_whole_input_bound_statement`; owner AUD-MP.
- `audit_memory_phi_prune_counted_erases`: `audit_memory_phi_prune_counted_erases_statement`;
  owner AUD-MP.

## AnalysesAuditMemoryPhiState

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `PhiResult` (constructor); `docs/api/analyses.md`.
- `phi_result` (Record); `docs/api/analyses.md`.
- `phi_graph` (field); `docs/api/analyses.md`.
- `phi_representatives` (field); `docs/api/analyses.md`.
- `phi_rep` (Definition); `docs/api/analyses.md`.
- `phi_history_projection` (Definition); `docs/api/analyses.md`.
- `phi_dependency_path` (Inductive); `docs/api/analyses.md`.
- `PhiDependencyEdge` (constructor); `docs/api/analyses.md`.
- `PhiDependencyExtend` (constructor); `docs/api/analyses.md`.
- `phi_projection_statement` (Definition); `docs/api/analyses.md`.
- `phi_terminal_elimination_statement` (Definition); `docs/api/analyses.md`.
- `phi_self_only_retained_statement` (Definition); `docs/api/analyses.md`.
- `phi_cycle_retained_statement` (Definition); `docs/api/analyses.md`.
- `phi_legacy_checked_statement` (Definition); `docs/api/analyses.md`.
- `phi_legacy_byte_statement` (Definition); `docs/api/analyses.md`.
- `memory_prune_with_map_type` (Definition); `docs/api/analyses.md`.
- `memory_prune_projection` (Definition); `docs/api/analyses.md`.
- `memory_prune_type` (Definition); `docs/api/analyses.md`.
- `memory_prune_from_map` (Definition); `docs/api/analyses.md`.
- `memory_phi_projection_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_terminal_removed_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_cycles_retained_statement` (Definition); `docs/api/analyses.md`.
- `memory_frontier_pruned` (Definition); `docs/api/analyses.md`.
- `memory_sealed_pruned` (Definition); `docs/api/analyses.md`.
- `memory_pruned_builders_projection_statement` (Definition); `docs/api/analyses.md`.
- `memory_prune_legacy_checked_statement` (Definition); `docs/api/analyses.md`.
- `memory_prune_legacy_bytes_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_removed_has_operand_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_resolved_removed_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_output_shape_statement` (Definition); `docs/api/analyses.md`.
- `memory_phi_map_domain_statement` (Definition); `docs/api/analyses.md`.
- `PhiDependencyEdgeData` (constructor); `docs/api/analyses.md`.
- `phi_dependency_edge` (Record); `docs/api/analyses.md`.
- `dependency_source` (field); `docs/api/analyses.md`.
- `dependency_key` (field); `docs/api/analyses.md`.
- `dependency_target` (field); `docs/api/analyses.md`.
- `phi_input_rows` (Definition); `docs/api/analyses.md`.
- `phi_dependency_rows_from_inputs` (Definition); `docs/api/analyses.md`.
- `phi_dependency_graph_from_inputs` (Definition); `docs/api/analyses.md`.
- `phi_dependency_graph` (Definition); `docs/api/analyses.md`.
- `phi_dependency_ready_statement` (Definition); `docs/api/analyses.md`.
- `phi_dependency_paths_statement` (Definition); `docs/api/analyses.md`.
- `phi_component_cyclic` (Definition); `docs/api/analyses.md`.
- `phi_cycle_flags` (Definition); `docs/api/analyses.md`.
- `PhiDependencyIndex` (constructor); `docs/api/analyses.md`.
- `phi_dependency_index` (Record); `docs/api/analyses.md`.
- `phi_index_inputs` (field); `docs/api/analyses.md`.
- `phi_index_graph` (field); `docs/api/analyses.md`.
- `phi_index_prepared` (field); `docs/api/analyses.md`.
- `phi_index_scc` (field); `docs/api/analyses.md`.
- `phi_index_cycles` (field); `docs/api/analyses.md`.
- `phi_prepare_dependencies` (Definition); `docs/api/analyses.md`.
- `phi_cycle_flags_statement` (Definition); `docs/api/analyses.md`.
- `phi_rep_from_map` (Definition); `docs/api/analyses.md`.
- `phi_same_rep` (Definition); `docs/api/analyses.md`.
- `phi_resolve_step` (Inductive); `docs/api/analyses.md`.
- `PhiResolveCyclic` (constructor); `docs/api/analyses.md`.
- `PhiResolveEmpty` (constructor); `docs/api/analyses.md`.
- `PhiResolveEqual` (constructor); `docs/api/analyses.md`.
- `PhiResolveKeep` (constructor); `docs/api/analyses.md`.
- `phi_resolve_trace` (Inductive); `docs/api/analyses.md`.
- `PhiResolveTraceNil` (constructor); `docs/api/analyses.md`.
- `PhiResolveTraceCons` (constructor); `docs/api/analyses.md`.
- `phi_resolution_statement` (Definition); `docs/api/analyses.md`.
- `phi_resolve_step_total_statement` (Definition); `docs/api/analyses.md`.
- `phi_resolve_step_deterministic_statement` (Definition); `docs/api/analyses.md`.
- `memory_prune_public_type` (Definition); `docs/api/analyses.md`.
- `memory_prune_wf_contract` (Definition); `docs/api/analyses.md`.
- `memory_prune_map_projection_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_projection_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_terminal_removed_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_cycles_retained_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_removed_has_operand_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_resolved_removed_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_output_shape_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_map_domain_contract` (Definition); `docs/api/analyses.md`.
- `memory_pruned_builders_projection_contract` (Definition); `docs/api/analyses.md`.
- `memory_prune_legacy_checked_contract` (Definition); `docs/api/analyses.md`.
- `memory_prune_legacy_bytes_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_dependency_ready_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_dependency_paths_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_cycle_flags_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_resolution_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_resolution_total_contract` (Definition); `docs/api/analyses.md`.
- `memory_phi_resolution_deterministic_contract` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryPhiStateAdequacy`.

- `phi_dependency_ready`: `phi_dependency_ready_statement`; owner AUD-MP.
- `phi_dependency_paths`: `phi_dependency_paths_statement`; owner AUD-MP.
- `phi_cycle_flags`: `phi_cycle_flags_statement`; owner AUD-MP.
- `phi_resolve_step_total`: `phi_resolve_step_total_statement`; owner AUD-MP.
- `phi_resolve_step_deterministic`: `phi_resolve_step_deterministic_statement`; owner AUD-MP.

## AnalysesAuditMemoryRawNext

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_raw_next_event` (Inductive); `docs/api/analyses.md`.
- `AuditRawBranch` (constructor); `docs/api/analyses.md`.
- `AuditRawIncoming` (constructor); `docs/api/analyses.md`.
- `AuditRawOperand` (constructor); `docs/api/analyses.md`.
- `AuditRawEffectGet` (constructor); `docs/api/analyses.md`.
- `AuditRawBefore` (constructor); `docs/api/analyses.md`.
- `AuditRawDisjoint` (constructor); `docs/api/analyses.md`.
- `audit_memory_operands` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_raw_next` (Definition); `docs/api/analyses.md`.
- `audit_memory_raw_next_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_operands_count_statement` (Definition); `docs/api/analyses.md`.
- `audit_raw_next_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_raw_next_source_work` (Definition); `docs/api/analyses.md`.
- `audit_raw_next_source_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_raw_next_first_missing_skips_before` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryRawNextAdequacy`.

- `audit_memory_raw_next_erases`: `audit_memory_raw_next_erases_statement`; owner AUD-MW-MEMO.
- `audit_memory_operands_count`: `audit_memory_operands_count_statement`; owner AUD-MW-MEMO.
- `audit_raw_next_source_bound`: `audit_raw_next_source_bound_statement`; owner AUD-MW-MEMO.

## AnalysesAuditMemorySearch

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_search_event` (Inductive); `docs/api/analyses.md`.
- `AuditSearchFuel` (constructor); `docs/api/analyses.md`.
- `AuditSearchStep` (constructor); `docs/api/analyses.md`.
- `AuditSearchRead` (constructor); `docs/api/analyses.md`.
- `AuditSearchWrite` (constructor); `docs/api/analyses.md`.
- `AuditSearchRoot` (constructor); `docs/api/analyses.md`.
- `AuditSearchNext` (constructor); `docs/api/analyses.md`.
- `audit_memory_search_step` (Definition); `docs/api/analyses.md`.
- `audit_memory_search_run` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_search_steps` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_search_run_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_search_step_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_search_primitive_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_search_source_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_search_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemorySearchAdequacy`.

- `audit_memory_search_run_erases`: `audit_memory_search_run_erases_statement`; owner AUD-MW-SEARCH.
- `audit_memory_search_step_bound`: `audit_memory_search_step_bound_statement`; owner AUD-MW-SEARCH.
- `audit_memory_search_source_bound`: `audit_memory_search_source_bound_statement`; owner
  AUD-MW-SEARCH.

## AnalysesAuditMemorySearchAdaptedSource

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_clobbers_whole_input_bound_adapted_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemorySearchAdaptedSourceAdequacy`.

- `audit_memory_clobbers_whole_input_bound_adapted`:
  `audit_memory_clobbers_whole_input_bound_adapted_statement`; owner AUD-MW-SEARCH.

## AnalysesAuditMemorySearchInputBudget

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_search_read_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_search_write_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_search_step_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_search_run_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_search_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_search_empty_input_budget` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemorySearchInputBudgetAdequacy`.

- `audit_search_whole_input_bound`: `audit_search_whole_input_bound_statement`; owner AUD-MW-SEARCH.

## AnalysesAuditMemorySharedBudget

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_edges_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_distinct_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_index_input_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_row_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_table_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_table_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.
- `audit_shared_duplicate_distinct_budget` (Example); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemorySharedBudgetAdequacy`.

- `audit_memory_table_whole_input_bound`: `audit_memory_table_whole_input_bound_statement`; owner
  AUD-MW-TABLES.

## AnalysesAuditMemorySnapshotPublic

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_snapshot_refresh_compute` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_saved_state` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_semantic_valid` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_plain_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_refresh_semantic_valid_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_semantic_valid_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_coverage_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_complete_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_current_coverage_statement` (Definition); `docs/api/analyses.md`.
- `audit_snapshot_query_current_complete_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemorySnapshotPublicAdequacy`.

- `audit_snapshot_refresh_plain_erases`: `audit_snapshot_refresh_plain_erases_statement`; owner
  AUD-MW-MEMO.
- `audit_snapshot_refresh_semantic_valid`: `audit_snapshot_refresh_semantic_valid_statement`;
  owner AUD-MW-MEMO.
- `audit_snapshot_query_semantic_valid`: `audit_snapshot_query_semantic_valid_statement`; owner
  AUD-MW-MEMO.
- `audit_snapshot_query_coverage`: `audit_snapshot_query_coverage_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_complete`: `audit_snapshot_query_complete_statement`; owner AUD-MW-MEMO.
- `audit_snapshot_query_current_coverage`: `audit_snapshot_query_current_coverage_statement`;
  owner AUD-MW-MEMO.
- `audit_snapshot_query_current_complete`: `audit_snapshot_query_current_complete_statement`;
  owner AUD-MW-MEMO.

Only `audit_snapshot_query_semantic_valid_statement` adds saved-graph `memory_graph_wf` and saved
`memory_valid_version ... start` premises. Current-snapshot coverage retains its exact original
epoch, domain and current-state premises. Names and theorem owners do not change.

## AnalysesAuditMemoryState

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `scope_code_injective_statement` (Definition); `docs/api/analyses.md`.
- `memo_entry` (Inductive); `docs/api/analyses.md`.
- `MemoBusy` (constructor); `docs/api/analyses.md`.
- `MemoDone` (constructor); `docs/api/analyses.md`.
- `memo_state` (Record); `docs/api/analyses.md`.
- `memo_adjacency` (field); `docs/api/analyses.md`.
- `memo_effect_index` (field); `docs/api/analyses.md`.
- `memo_entries` (field); `docs/api/analyses.md`.
- `memo_valid` (Definition); `docs/api/analyses.md`.
- `memo_initial` (Definition); `docs/api/analyses.md`.
- `memo_initial_statement` (Definition); `docs/api/analyses.md`.
- `memo_preserved_statement` (Definition); `docs/api/analyses.md`.
- `memo_coverage_statement` (Definition); `docs/api/analyses.md`.
- `memo_complete_statement` (Definition); `docs/api/analyses.md`.
- `memo_execution_statement` (Definition); `docs/api/analyses.md`.
- `memo_hit_statement` (Definition); `docs/api/analyses.md`.
- `memo_store_complete_statement` (Definition); `docs/api/analyses.md`.
- `memo_second_query_statement` (Definition); `docs/api/analyses.md`.
- `busy_cut` (Definition); `docs/api/analyses.md`.
- `busy_cut_coverage_statement` (Definition); `docs/api/analyses.md`.
- `busy_cut_trace_statement` (Definition); `docs/api/analyses.md`.
- `graph_observations_equal` (Definition); `docs/api/analyses.md`.
- `memory_observations_equal` (Definition); `docs/api/analyses.md`.
- `MemoSnapshot` (constructor); `docs/api/analyses.md`.
- `memo_snapshot` (Record); `docs/api/analyses.md`.
- `snapshot_epoch` (field); `docs/api/analyses.md`.
- `snapshot_graph` (field); `docs/api/analyses.md`.
- `snapshot_effects` (field); `docs/api/analyses.md`.
- `snapshot_memory` (field); `docs/api/analyses.md`.
- `memo_epoch_laws` (Record); `docs/api/analyses.md`.
- `epoch_equal_observations` (field); `docs/api/analyses.md`.
- `epoch_matches` (Definition); `docs/api/analyses.md`.
- `refresh_valid_statement` (Definition); `docs/api/analyses.md`.
- `refresh_mismatch_statement` (Definition); `docs/api/analyses.md`.
- `refresh_match_statement` (Definition); `docs/api/analyses.md`.
- `memo_legacy_checked_statement` (Definition); `docs/api/analyses.md`.
- `memo_legacy_bytes_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryStateAdequacy`.

- `scope_code_injective`: `scope_code_injective_statement`; owner AUD-MEM-BASE.
- `memo_initial`: `memo_initial_statement`; owner AUD-MEM-BASE.
- `busy_cut_coverage`: `busy_cut_coverage_statement`; owner AUD-MEM-BASE.
- `busy_cut_trace`: `busy_cut_trace_statement`; owner AUD-MEM-BASE.

## AnalysesAuditMemoryTable

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_memory_edges_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoryEdgesCase` (constructor); `docs/api/analyses.md`.
- `AuditMemoryEdgesOut` (constructor); `docs/api/analyses.md`.
- `audit_memory_edges` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_row_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoryEffectsCallback` (constructor); `docs/api/analyses.md`.
- `AuditMemoryRowBuild` (constructor); `docs/api/analyses.md`.
- `audit_memory_effect_row` (Definition); `docs/api/analyses.md`.
- `audit_memory_table_event` (Inductive); `docs/api/analyses.md`.
- `AuditMemoryTableEdges` (constructor); `docs/api/analyses.md`.
- `AuditMemoryTableDistinct` (constructor); `docs/api/analyses.md`.
- `AuditMemoryTableIndex` (constructor); `docs/api/analyses.md`.
- `audit_memory_effect_table` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_table_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_edges_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_edges_budget` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_row_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_table_work` (Fixpoint); `docs/api/analyses.md`.
- `audit_memory_table_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_effect_table_source_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryTableAdequacy`.

- `audit_memory_effect_table_erases`: `audit_memory_effect_table_erases_statement`; owner
  AUD-MW-TABLES.
- `audit_memory_effect_table_source_bound`: `audit_memory_effect_table_source_bound_statement`;
  owner AUD-MW-TABLES.

## AnalysesAuditMemoryWalkIndex

Public package: `Galois.Analyses`.

Card: AUD-MEM-MODELS

- `audit_walk_predecessors` (Definition); `docs/api/analyses.md`.
- `audit_walk_successors` (Definition); `docs/api/analyses.md`.
- `audit_walk_raw_event` (Definition); `docs/api/analyses.md`.
- `audit_walk_index_event` (Definition); `docs/api/analyses.md`.
- `audit_walk_index_run` (Record); `docs/api/analyses.md`.
- `audit_walk_index_value` (field); `docs/api/analyses.md`.
- `audit_walk_index_table` (field); `docs/api/analyses.md`.
- `audit_walk_index_prepare` (field); `docs/api/analyses.md`.
- `audit_walk_index_rows` (field); `docs/api/analyses.md`.
- `audit_memory_walk_index_counted` (Definition); `docs/api/analyses.md`.
- `audit_memory_walk_index_source_work` (Definition); `docs/api/analyses.md`.
- `audit_walk_predecessor_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_walk_index_input_budget` (Definition); `docs/api/analyses.md`.
- `audit_memory_walk_index_erases_statement` (Definition); `docs/api/analyses.md`.
- `audit_memory_walk_index_whole_input_bound_statement` (Definition); `docs/api/analyses.md`.

Future proof module: `AnalysesAuditMemoryWalkIndexAdequacy`.

- `audit_memory_walk_index_erases`: `audit_memory_walk_index_erases_statement`; owner AUD-MW-SEARCH.
- `audit_memory_walk_index_whole_input_bound`:
  `audit_memory_walk_index_whole_input_bound_statement`; owner AUD-MW-SEARCH.

## CollectionsAuditAdapted

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_uf_whole_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_whole_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_list_whole_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_branches_whole_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.
- `audit_pair_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.
- `audit_list_input_bound_adapted_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditAdaptedENCAdequacy`.

- `audit_pair_input_bound_adapted`: `audit_pair_input_bound_adapted_statement`; owner AUD-CL-ENC.
- `audit_list_input_bound_adapted`: `audit_list_input_bound_adapted_statement`; owner AUD-CL-ENC.

Future proof module: `CollectionsAuditAdaptedUFAdequacy`.

- `audit_uf_whole_input_bound_adapted`: `audit_uf_whole_input_bound_adapted_statement`; owner
  AUD-CL-UF.
- `audit_uf_pair_whole_input_bound_adapted`: `audit_uf_pair_whole_input_bound_adapted_statement`;
  owner AUD-CL-UF.
- `audit_uf_list_whole_input_bound_adapted`: `audit_uf_list_whole_input_bound_adapted_statement`;
  owner AUD-CL-UF.
- `audit_uf_branches_whole_input_bound_adapted`:
  `audit_uf_branches_whole_input_bound_adapted_statement`; owner AUD-CL-UF.

## CollectionsAuditCallback

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_external_callback_adapter` (Record); `docs/api/collections.md`.
- `audit_external_callback_source` (field); `docs/api/collections.md`.
- `audit_external_callback_input_bound` (field); `docs/api/collections.md`.
- `audit_external_callback_observed_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditCallbackAdequacy`.

- `audit_external_callback_observed`: `audit_external_callback_observed_statement`; owner
  AUD-CL-ENC.

## CollectionsAuditCompare

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_positive_compare_event` (Inductive); `docs/api/collections.md`.
- `AuditPositiveCompare` (constructor); `docs/api/collections.md`.
- `audit_positive_compare_cont` (Fixpoint); `docs/api/collections.md`.
- `audit_positive_compare` (Definition); `docs/api/collections.md`.
- `audit_positive_ltb` (Definition); `docs/api/collections.md`.
- `audit_positive_leb` (Definition); `docs/api/collections.md`.
- `audit_positive_compare_source_work` (Definition); `docs/api/collections.md`.
- `audit_positive_order_source_work` (Definition); `docs/api/collections.md`.
- `audit_positive_compare_cont_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_compare_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_order_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_compare_different_tags` (Example); `docs/api/collections.md`.

Future proof module: `CollectionsAuditCompareAdequacy`.

- `audit_positive_compare_cont`: `audit_positive_compare_cont_statement`; owner AUD-CL-TRIE.
- `audit_positive_compare`: `audit_positive_compare_statement`; owner AUD-CL-TRIE.
- `audit_positive_order`: `audit_positive_order_statement`; owner AUD-CL-TRIE.

## CollectionsAuditComposite

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `CompositeCosts` (constructor); `docs/api/collections.md`.
- `composite_costs` (Record); `docs/api/collections.md`.
- `composite_left_encode` (field); `docs/api/collections.md`.
- `composite_right_encode` (field); `docs/api/collections.md`.
- `composite_cost_laws` (Record); `docs/api/collections.md`.
- `composite_left_bound` (field); `docs/api/collections.md`.
- `composite_right_bound` (field); `docs/api/collections.md`.
- `CompositePairWork` (constructor); `docs/api/collections.md`.
- `composite_pair_work` (Record); `docs/api/collections.md`.
- `composite_left_bits` (field); `docs/api/collections.md`.
- `composite_right_bits` (field); `docs/api/collections.md`.
- `composite_emitted_bits` (field); `docs/api/collections.md`.
- `composite_stream_nodes` (field); `docs/api/collections.md`.
- `composite_callback_work` (field); `docs/api/collections.md`.
- `prepared_pair_work` (Definition); `docs/api/collections.md`.
- `prepared_pair_work_statement` (Definition); `docs/api/collections.md`.
- `CompositeListCosts` (constructor); `docs/api/collections.md`.
- `composite_list_costs` (Record); `docs/api/collections.md`.
- `composite_element_encode` (field); `docs/api/collections.md`.
- `composite_list_cost_laws` (Record); `docs/api/collections.md`.
- `composite_element_bound` (field); `docs/api/collections.md`.
- `CompositeListWork` (constructor); `docs/api/collections.md`.
- `composite_list_work` (Record); `docs/api/collections.md`.
- `composite_list_elements` (field); `docs/api/collections.md`.
- `composite_list_input_bits` (field); `docs/api/collections.md`.
- `composite_list_emitted_bits` (field); `docs/api/collections.md`.
- `composite_list_stream_nodes` (field); `docs/api/collections.md`.
- `composite_list_callbacks` (field); `docs/api/collections.md`.
- `prepared_list_work` (Definition); `docs/api/collections.md`.
- `prepared_list_work_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditCompositeAdequacy`.

- `prepared_pair_work`: `prepared_pair_work_statement`; owner AUD-CL-ENC.
- `prepared_list_work`: `prepared_list_work_statement`; owner AUD-CL-ENC.

## CollectionsAuditContracts

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `prepared_key_refines_contract` (Definition); `docs/api/collections.md`.
- `dense_map_refines_contract` (Definition); `docs/api/collections.md`.
- `union_find_cost_contract` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditContractsDENSEAdequacy`.

- `prepared_key_refines_contract_holds`: `prepared_key_refines_contract`; owner AUD-CL-DENSE.
- `dense_map_refines_contract_holds`: `dense_map_refines_contract`; owner AUD-CL-DENSE.

Future proof module: `CollectionsAuditContractsUFAdequacy`.

- `union_find_cost_contract_holds`: `union_find_cost_contract`; owner AUD-CL-UF.

## CollectionsAuditDense

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_dense_numeric_event` (Inductive); `docs/api/collections.md`.
- `AuditDenseBinarySuccessor` (constructor); `docs/api/collections.md`.
- `AuditDenseLengthConversion` (constructor); `docs/api/collections.md`.
- `audit_dense_N_succ` (Definition); `docs/api/collections.md`.
- `audit_dense_N_of_nat` (Definition); `docs/api/collections.md`.
- `audit_dense_N_succ_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_N_of_nat_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_prepare_event` (Inductive); `docs/api/collections.md`.
- `AuditDenseUniqueCase` (constructor); `docs/api/collections.md`.
- `AuditDenseUniqueProbe` (constructor); `docs/api/collections.md`.
- `AuditDenseUniqueAdd` (constructor); `docs/api/collections.md`.
- `AuditDenseUniqueKeep` (constructor); `docs/api/collections.md`.
- `AuditDenseNumberCase` (constructor); `docs/api/collections.md`.
- `AuditDenseNumberNext` (constructor); `docs/api/collections.md`.
- `AuditDenseNumberStore` (constructor); `docs/api/collections.md`.
- `AuditDenseLength` (constructor); `docs/api/collections.md`.
- `audit_dense_unique` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_number` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_prepare` (Definition); `docs/api/collections.md`.
- `audit_dense_unique_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_number_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_prepare_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_prepare_work` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_unique_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_number_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_prepare_budget` (Definition); `docs/api/collections.md`.
- `audit_dense_prepare_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditDenseAdequacy`.

- `audit_dense_N_succ_erases`: `audit_dense_N_succ_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_N_of_nat_erases`: `audit_dense_N_of_nat_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_unique_erases`: `audit_dense_unique_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_number_erases`: `audit_dense_number_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_prepare_erases`: `audit_dense_prepare_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_prepare_source_bound`: `audit_dense_prepare_source_bound_statement`; owner
  AUD-CL-DENSE.

## CollectionsAuditDenseInput

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_dense_unique_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_number_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_prepare_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_key_get_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_index_get_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_index_update_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_update_input_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_elements_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_of_map_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_bindings_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_prepare_slots_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_read_slots_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_dense_prepare_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_update_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_remove_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_elements_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_of_map_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_to_map_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_prepare_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_read_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slot_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_read_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slots_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_read_slots_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_key_whole_input_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditDenseInputAdequacy`.

- `audit_dense_prepare_whole_input_bound`: `audit_dense_prepare_whole_input_bound_statement`;
  owner AUD-CL-DENSE.
- `audit_slot_lookup_whole_input_bound`: `audit_slot_lookup_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_update_whole_input_bound`: `audit_slot_update_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_remove_whole_input_bound`: `audit_slot_remove_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_elements_whole_input_bound`: `audit_slot_elements_whole_input_bound_statement`;
  owner AUD-CL-DENSE.
- `audit_slot_of_map_whole_input_bound`: `audit_slot_of_map_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_to_map_whole_input_bound`: `audit_slot_to_map_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_dense_token_prepare_whole_input_bound`:
  `audit_dense_token_prepare_whole_input_bound_statement`; owner AUD-CL-DENSE.
- `audit_dense_token_read_whole_input_bound`:
  `audit_dense_token_read_whole_input_bound_statement`; owner AUD-CL-DENSE.
- `audit_prepare_slot_whole_input_bound`: `audit_prepare_slot_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_read_whole_input_bound`: `audit_slot_read_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepare_slots_whole_input_bound`: `audit_prepare_slots_whole_input_bound_statement`;
  owner AUD-CL-DENSE.
- `audit_read_slots_whole_input_bound`: `audit_read_slots_whole_input_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepare_key_whole_input_bound`: `audit_prepare_key_whole_input_bound_statement`; owner
  AUD-CL-DENSE.

## CollectionsAuditDenseSlots

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_slot_event` (Inductive); `docs/api/collections.md`.
- `AuditSlotUniverseGet` (constructor); `docs/api/collections.md`.
- `AuditSlotAbstractGet` (constructor); `docs/api/collections.md`.
- `AuditSlotRead` (constructor); `docs/api/collections.md`.
- `AuditSlotWrite` (constructor); `docs/api/collections.md`.
- `AuditSlotRemove` (constructor); `docs/api/collections.md`.
- `AuditSlotMapWrite` (constructor); `docs/api/collections.md`.
- `AuditSlotCase` (constructor); `docs/api/collections.md`.
- `AuditSlotBatchIndex` (constructor); `docs/api/collections.md`.
- `AuditSlotEmit` (constructor); `docs/api/collections.md`.
- `audit_prepare_slot` (Definition); `docs/api/collections.md`.
- `audit_slot_read` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup` (Definition); `docs/api/collections.md`.
- `audit_slot_update` (Definition); `docs/api/collections.md`.
- `audit_slot_remove` (Definition); `docs/api/collections.md`.
- `audit_slot_elements_from` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_elements` (Definition); `docs/api/collections.md`.
- `audit_prepare_slots` (Fixpoint); `docs/api/collections.md`.
- `audit_read_slots` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_of_map_from` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_of_map` (Definition); `docs/api/collections.md`.
- `audit_slot_bindings_to_map` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_to_map` (Definition); `docs/api/collections.md`.
- `audit_dense_token_prepare` (Definition); `docs/api/collections.md`.
- `audit_dense_token_read` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slot_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_read_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slots_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_read_slots_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_update_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_remove_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_elements_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_of_map_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_to_map_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_prepare_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_read_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_key_get_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_index_get_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_index_update_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_update_budget` (Definition); `docs/api/collections.md`.
- `audit_slot_lookup_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_update_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_remove_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_elements_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_elements_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_of_map_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_of_map_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_bindings_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_to_map_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_prepare_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_dense_token_read_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slot_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_read_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepare_slots_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_read_slots_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_prepare_slots_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_read_slots_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_slot_read_calls` (Fixpoint); `docs/api/collections.md`.
- `audit_slot_read_key_bits` (Fixpoint); `docs/api/collections.md`.
- `audit_read_slots_observation_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditDenseSlotsAdequacy`.

- `audit_slot_lookup_erases`: `audit_slot_lookup_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepare_slot_erases`: `audit_prepare_slot_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_read_erases`: `audit_slot_read_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepare_slots_erases`: `audit_prepare_slots_erases_statement`; owner AUD-CL-DENSE.
- `audit_read_slots_erases`: `audit_read_slots_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_update_erases`: `audit_slot_update_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_remove_erases`: `audit_slot_remove_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_elements_erases`: `audit_slot_elements_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_of_map_erases`: `audit_slot_of_map_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_to_map_erases`: `audit_slot_to_map_erases_statement`; owner AUD-CL-DENSE.
- `audit_dense_token_prepare_erases`: `audit_dense_token_prepare_erases_statement`; owner
  AUD-CL-DENSE.
- `audit_dense_token_read_erases`: `audit_dense_token_read_erases_statement`; owner AUD-CL-DENSE.
- `audit_slot_lookup_source_bound`: `audit_slot_lookup_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_slot_update_source_bound`: `audit_slot_update_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_slot_remove_source_bound`: `audit_slot_remove_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_slot_elements_source_bound`: `audit_slot_elements_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_of_map_source_bound`: `audit_slot_of_map_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_slot_to_map_source_bound`: `audit_slot_to_map_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_dense_token_prepare_source_bound`: `audit_dense_token_prepare_source_bound_statement`;
  owner AUD-CL-DENSE.
- `audit_dense_token_read_source_bound`: `audit_dense_token_read_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepare_slot_source_bound`: `audit_prepare_slot_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_slot_read_source_bound`: `audit_slot_read_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_prepare_slots_source_bound`: `audit_prepare_slots_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_read_slots_source_bound`: `audit_read_slots_source_bound_statement`; owner AUD-CL-DENSE.
- `audit_read_slots_observation`: `audit_read_slots_observation_statement`; owner AUD-CL-DENSE.

## CollectionsAuditElements

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_elements_event` (Inductive); `docs/api/collections.md`.
- `AuditElementsNode` (constructor); `docs/api/collections.md`.
- `AuditElementsEmit` (constructor); `docs/api/collections.md`.
- `AuditElementsReverse` (constructor); `docs/api/collections.md`.
- `AuditElementsMap` (constructor); `docs/api/collections.md`.
- `audit_elements_fold_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_elements_reverse` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_elements` (Definition); `docs/api/collections.md`.
- `audit_elements_values` (Fixpoint); `docs/api/collections.md`.
- `audit_map_elements` (Definition); `docs/api/collections.md`.
- `audit_set_elements_event` (Inductive); `docs/api/collections.md`.
- `AuditSetElementsTrie` (constructor); `docs/api/collections.md`.
- `AuditSetElementsProject` (constructor); `docs/api/collections.md`.
- `audit_set_elements_project` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_elements` (Definition); `docs/api/collections.md`.
- `audit_elements_nodes` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_elements_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_elements_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_elements_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_elements_fold_count_statement` (Definition); `docs/api/collections.md`.
- `audit_elements_bits` (Fixpoint); `docs/api/collections.md`.
- `audit_elements_frame_work` (Definition); `docs/api/collections.md`.
- `audit_elements_work` (Fixpoint); `docs/api/collections.md`.
- `audit_set_elements_work` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_nodes` (Definition); `docs/api/collections.md`.
- `audit_trie_output_bits` (Definition); `docs/api/collections.md`.
- `audit_trie_elements_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_elements_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_elements_work_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditElementsAdequacy`.

- `audit_trie_elements_erases`: `audit_trie_elements_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_elements_erases`: `audit_map_elements_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_elements_erases`: `audit_finset_elements_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_elements_fold_count`: `audit_elements_fold_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_trie_elements_work_bound`: `audit_trie_elements_work_bound_statement`; owner
  AUD-CL-TRAVERSE.
- `audit_map_elements_work_bound`: `audit_map_elements_work_bound_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_elements_work_bound`: `audit_finset_elements_work_bound_statement`; owner
  AUD-CL-TRAVERSE.

## CollectionsAuditEncoderBudget

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `AuditEncoderAdapter` (constructor); `docs/api/collections.md`.
- `audit_encoder_adapter` (Record); `docs/api/collections.md`.
- `audit_encoder_run` (field); `docs/api/collections.md`.
- `audit_encoder_work` (field); `docs/api/collections.md`.
- `audit_encoder_budget` (field); `docs/api/collections.md`.
- `audit_encoder_source` (field); `docs/api/collections.md`.
- `audit_encoder_adapter_laws` (Record); `docs/api/collections.md`.
- `audit_encoder_source_total` (field); `docs/api/collections.md`.
- `audit_encoder_source_agrees` (field); `docs/api/collections.md`.
- `audit_encoder_code_agrees` (field); `docs/api/collections.md`.
- `audit_encoder_input_bound` (field); `docs/api/collections.md`.
- `audit_nat_input_budget` (Definition); `docs/api/collections.md`.
- `audit_N_input_budget` (Definition); `docs/api/collections.md`.
- `audit_pair_input_budget` (Definition); `docs/api/collections.md`.
- `audit_child_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_list_input_budget` (Definition); `docs/api/collections.md`.
- `audit_option_input_budget` (Definition); `docs/api/collections.md`.
- `audit_sum_input_budget` (Definition); `docs/api/collections.md`.
- `audit_base_encoder_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_pair_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_list_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_sum_option_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_pair_budget_retains_width` (Example); `docs/api/collections.md`.
- `audit_list_budget_retains_occurrences` (Example); `docs/api/collections.md`.

Future proof module: `CollectionsAuditEncoderBudgetAdequacy`.

- `audit_base_encoder_input_bound`: `audit_base_encoder_input_bound_statement`; owner AUD-CL-ENC.
- `audit_pair_input_bound`: `audit_pair_input_bound_statement`; owner AUD-CL-ENC.
- `audit_list_input_bound`: `audit_list_input_bound_statement`; owner AUD-CL-ENC.
- `audit_sum_option_input_bound`: `audit_sum_option_input_bound_statement`; owner AUD-CL-ENC.

## CollectionsAuditEncoding

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_nat_encoding_event` (Inductive); `docs/api/collections.md`.
- `AuditNatFrame` (constructor); `docs/api/collections.md`.
- `AuditPositiveSuccFrame` (constructor); `docs/api/collections.md`.
- `audit_positive_succ` (Fixpoint); `docs/api/collections.md`.
- `audit_nat_encode` (Fixpoint); `docs/api/collections.md`.
- `audit_positive_succ_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_nat_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_succ_count_statement` (Definition); `docs/api/collections.md`.
- `audit_nat_encode_count_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_succ_run` (Inductive); `docs/api/collections.md`.
- `AuditSuccOne` (constructor); `docs/api/collections.md`.
- `AuditSuccZero` (constructor); `docs/api/collections.md`.
- `AuditSuccCarry` (constructor); `docs/api/collections.md`.
- `audit_positive_succ_run_correct_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_succ_run_total_statement` (Definition); `docs/api/collections.md`.
- `audit_nat_encode_run` (Inductive); `docs/api/collections.md`.
- `AuditNatZero` (constructor); `docs/api/collections.md`.
- `AuditNatSuccessor` (constructor); `docs/api/collections.md`.
- `audit_nat_encode_run_correct_statement` (Definition); `docs/api/collections.md`.
- `audit_nat_encode_run_total_statement` (Definition); `docs/api/collections.md`.
- `audit_basic_encoding_event` (Inductive); `docs/api/collections.md`.
- `AuditBasicEncoding` (constructor); `docs/api/collections.md`.
- `audit_positive_encode` (Definition); `docs/api/collections.md`.
- `audit_bool_encode` (Definition); `docs/api/collections.md`.
- `audit_unit_encode` (Definition); `docs/api/collections.md`.
- `audit_z_encode` (Definition); `docs/api/collections.md`.
- `audit_n_encoding_event` (Inductive); `docs/api/collections.md`.
- `AuditNEncoding` (constructor); `docs/api/collections.md`.
- `AuditNSucc` (constructor); `docs/api/collections.md`.
- `audit_N_encode` (Definition); `docs/api/collections.md`.
- `audit_N_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_bool_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_unit_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_z_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_encoding_frame` (Inductive); `docs/api/collections.md`.
- `AuditEmitCode` (constructor); `docs/api/collections.md`.
- `AuditStreamPositive` (constructor); `docs/api/collections.md`.
- `audit_emit_code` (Fixpoint); `docs/api/collections.md`.
- `audit_stream_positive` (Fixpoint); `docs/api/collections.md`.
- `audit_emit_code_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_stream_positive_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_pair_event` (Inductive); `docs/api/collections.md`.
- `AuditPairFirst` (constructor); `docs/api/collections.md`.
- `AuditPairSecond` (constructor); `docs/api/collections.md`.
- `AuditPairFrame` (constructor); `docs/api/collections.md`.
- `audit_pair_encode` (Definition); `docs/api/collections.md`.
- `audit_pair_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_list_event` (Inductive); `docs/api/collections.md`.
- `AuditListCase` (constructor); `docs/api/collections.md`.
- `AuditListComponent` (constructor); `docs/api/collections.md`.
- `AuditListFrame` (constructor); `docs/api/collections.md`.
- `audit_emit_list` (Fixpoint); `docs/api/collections.md`.
- `audit_list_encode` (Definition); `docs/api/collections.md`.
- `audit_emit_list_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_list_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_sum_event` (Inductive); `docs/api/collections.md`.
- `AuditSumLeft` (constructor); `docs/api/collections.md`.
- `AuditSumRight` (constructor); `docs/api/collections.md`.
- `audit_sum_encode` (Definition); `docs/api/collections.md`.
- `audit_sum_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_option_event` (Inductive); `docs/api/collections.md`.
- `AuditOptionNone` (constructor); `docs/api/collections.md`.
- `AuditOptionSome` (constructor); `docs/api/collections.md`.
- `audit_option_encode` (Definition); `docs/api/collections.md`.
- `audit_option_encode_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_encoding_frame_charge` (Definition); `docs/api/collections.md`.
- `audit_encoding_frames_work` (Fixpoint); `docs/api/collections.md`.
- `audit_nat_events_work` (Definition); `docs/api/collections.md`.
- `audit_basic_encoding_work` (Definition); `docs/api/collections.md`.
- `audit_N_encoding_work` (Definition); `docs/api/collections.md`.
- `audit_pair_events_work` (Fixpoint); `docs/api/collections.md`.
- `audit_list_events_work` (Fixpoint); `docs/api/collections.md`.
- `audit_sum_events_work` (Fixpoint); `docs/api/collections.md`.
- `audit_option_events_work` (Fixpoint); `docs/api/collections.md`.
- `audit_encoded_bits` (Fixpoint); `docs/api/collections.md`.
- `audit_emit_code_count_statement` (Definition); `docs/api/collections.md`.
- `audit_stream_positive_count_statement` (Definition); `docs/api/collections.md`.
- `audit_emit_list_count_statement` (Definition); `docs/api/collections.md`.
- `audit_list_encode_count_statement` (Definition); `docs/api/collections.md`.
- `audit_pair_encode_count_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditEncodingAdequacy`.

- `audit_positive_succ_erases`: `audit_positive_succ_erases_statement`; owner AUD-CL-ENC.
- `audit_nat_encode_erases`: `audit_nat_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_positive_succ_count`: `audit_positive_succ_count_statement`; owner AUD-CL-ENC.
- `audit_nat_encode_count`: `audit_nat_encode_count_statement`; owner AUD-CL-ENC.
- `audit_positive_succ_run_correct`: `audit_positive_succ_run_correct_statement`; owner AUD-CL-ENC.
- `audit_positive_succ_run_total`: `audit_positive_succ_run_total_statement`; owner AUD-CL-ENC.
- `audit_nat_encode_run_correct`: `audit_nat_encode_run_correct_statement`; owner AUD-CL-ENC.
- `audit_nat_encode_run_total`: `audit_nat_encode_run_total_statement`; owner AUD-CL-ENC.
- `audit_N_encode_erases`: `audit_N_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_positive_encode_erases`: `audit_positive_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_bool_encode_erases`: `audit_bool_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_unit_encode_erases`: `audit_unit_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_z_encode_erases`: `audit_z_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_emit_code_erases`: `audit_emit_code_erases_statement`; owner AUD-CL-ENC.
- `audit_stream_positive_erases`: `audit_stream_positive_erases_statement`; owner AUD-CL-ENC.
- `audit_pair_encode_erases`: `audit_pair_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_emit_list_erases`: `audit_emit_list_erases_statement`; owner AUD-CL-ENC.
- `audit_list_encode_erases`: `audit_list_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_sum_encode_erases`: `audit_sum_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_option_encode_erases`: `audit_option_encode_erases_statement`; owner AUD-CL-ENC.
- `audit_emit_code_count`: `audit_emit_code_count_statement`; owner AUD-CL-ENC.
- `audit_stream_positive_count`: `audit_stream_positive_count_statement`; owner AUD-CL-ENC.
- `audit_emit_list_count`: `audit_emit_list_count_statement`; owner AUD-CL-ENC.
- `audit_list_encode_count`: `audit_list_encode_count_statement`; owner AUD-CL-ENC.
- `audit_pair_encode_count`: `audit_pair_encode_count_statement`; owner AUD-CL-ENC.

## CollectionsAuditFamilyClosure

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_cl_primitive_erasure_closure_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_source_work_closure_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_composite_union_find_closure_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_full_source_contract_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_literal_body_closure_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_whole_input_closure_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_complete_source_contract_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_adapted_source_contract_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_dense_whole_source_contract_statement` (Definition); `docs/api/collections.md`.
- `audit_cl_public_source_contract_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditFamilyClosureAdequacy`.

- `audit_cl_primitive_erasure_closure`: `audit_cl_primitive_erasure_closure_statement`; owner
  AUD-CL.
- `audit_cl_source_work_closure`: `audit_cl_source_work_closure_statement`; owner AUD-CL.
- `audit_cl_composite_union_find_closure`: `audit_cl_composite_union_find_closure_statement`;
  owner AUD-CL.
- `audit_cl_full_source_contract`: `audit_cl_full_source_contract_statement`; owner AUD-CL.
- `audit_cl_literal_body_closure`: `audit_cl_literal_body_closure_statement`; owner AUD-CL.
- `audit_cl_whole_input_closure`: `audit_cl_whole_input_closure_statement`; owner AUD-CL.
- `audit_cl_complete_source_contract`: `audit_cl_complete_source_contract_statement`; owner AUD-CL.
- `audit_cl_adapted_source_contract`: `audit_cl_adapted_source_contract_statement`; owner AUD-CL.
- `audit_cl_dense_whole_source_contract`: `audit_cl_dense_whole_source_contract_statement`; owner
  AUD-CL.
- `audit_cl_public_source_contract`: `audit_cl_public_source_contract_statement`; owner AUD-CL.

## CollectionsAuditFinSet

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_set_event` (Inductive); `docs/api/collections.md`.
- `AuditSetAdd` (constructor); `docs/api/collections.md`.
- `AuditSetMem` (constructor); `docs/api/collections.md`.
- `AuditSetRemove` (constructor); `docs/api/collections.md`.
- `AuditSetFold` (constructor); `docs/api/collections.md`.
- `audit_finset_add` (Definition); `docs/api/collections.md`.
- `audit_finset_mem` (Definition); `docs/api/collections.md`.
- `audit_finset_remove` (Definition); `docs/api/collections.md`.
- `audit_finset_fold` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_of_list` (Definition); `docs/api/collections.md`.
- `audit_finset_of_list_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_of_list_count_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_add_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_mem_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_remove_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_of_list_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_of_list_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditFinSetAdequacy`.

- `audit_finset_of_list_erases`: `audit_finset_of_list_erases_statement`; owner AUD-CL-TRIE.
- `audit_finset_of_list_count`: `audit_finset_of_list_count_statement`; owner AUD-CL-TRIE.
- `audit_finset_add_erases`: `audit_finset_add_erases_statement`; owner AUD-CL-TRIE.
- `audit_finset_mem_erases`: `audit_finset_mem_erases_statement`; owner AUD-CL-TRIE.
- `audit_finset_remove_erases`: `audit_finset_remove_erases_statement`; owner AUD-CL-TRIE.
- `audit_finset_of_list_source_bound`: `audit_finset_of_list_source_bound_statement`; owner
  AUD-CL-TRIE.

## CollectionsAuditHistorical

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `SlotBatchWork` (constructor); `docs/api/collections.md`.
- `slot_batch_work` (Record); `docs/api/collections.md`.
- `slot_reads` (field); `docs/api/collections.md`.
- `slot_key_bits` (field); `docs/api/collections.md`.
- `read_slots_counted` (Fixpoint); `docs/api/collections.md`.
- `slot_batch_cost_statement` (Definition); `docs/api/collections.md`.
- `union_action` (Inductive); `docs/api/collections.md`.
- `FindAction` (constructor); `docs/api/collections.md`.
- `UnionAction` (constructor); `docs/api/collections.md`.
- `action_step` (Definition); `docs/api/collections.md`.
- `union_event` (Inductive); `docs/api/collections.md`.
- `UFFuelCheck` (constructor); `docs/api/collections.md`.
- `UFParentGet` (constructor); `docs/api/collections.md`.
- `UFParentSet` (constructor); `docs/api/collections.md`.
- `UFRankGet` (constructor); `docs/api/collections.md`.
- `UFRankSet` (constructor); `docs/api/collections.md`.
- `UFKeyCompare` (constructor); `docs/api/collections.md`.
- `UFRankCompare` (constructor); `docs/api/collections.md`.
- `UFRankSuccessor` (constructor); `docs/api/collections.md`.
- `UFRankMax` (constructor); `docs/api/collections.md`.
- `trace_find_fuel` (Fixpoint); `docs/api/collections.md`.
- `trace_find` (Definition); `docs/api/collections.md`.
- `trace_union` (Definition); `docs/api/collections.md`.
- `trace_find_result_statement` (Definition); `docs/api/collections.md`.
- `trace_union_result_statement` (Definition); `docs/api/collections.md`.
- `event_keys` (Definition); `docs/api/collections.md`.
- `event_key_bits` (Definition); `docs/api/collections.md`.
- `UnionCallbackCosts` (constructor); `docs/api/collections.md`.
- `union_callback_costs` (Record); `docs/api/collections.md`.
- `union_encode_work` (field); `docs/api/collections.md`.
- `event_encode_work` (Definition); `docs/api/collections.md`.
- `event_unary_work` (Definition); `docs/api/collections.md`.
- `event_unary_total` (Definition); `docs/api/collections.md`.
- `trace_action` (Definition); `docs/api/collections.md`.
- `trace_actions` (Fixpoint); `docs/api/collections.md`.
- `trace_actions_result_statement` (Definition); `docs/api/collections.md`.
- `trace_branches` (Definition); `docs/api/collections.md`.
- `trace_branch_sum_statement` (Definition); `docs/api/collections.md`.
- `union_callback_cost_laws` (Record); `docs/api/collections.md`.
- `union_encode_bound` (field); `docs/api/collections.md`.
- `union_map_gets` (Definition); `docs/api/collections.md`.
- `union_map_sets` (Definition); `docs/api/collections.md`.
- `union_comparisons` (Definition); `docs/api/collections.md`.
- `union_fuel_checks` (Definition); `docs/api/collections.md`.
- `union_trie_read_bits` (Definition); `docs/api/collections.md`.
- `union_trie_write_bits` (Definition); `docs/api/collections.md`.
- `union_key_compare_bits` (Definition); `docs/api/collections.md`.
- `UnionSourceWork` (constructor); `docs/api/collections.md`.
- `union_source_work` (Record); `docs/api/collections.md`.
- `union_work_gets` (field); `docs/api/collections.md`.
- `union_work_sets` (field); `docs/api/collections.md`.
- `union_work_fuel_checks` (field); `docs/api/collections.md`.
- `union_work_key_comparisons` (field); `docs/api/collections.md`.
- `union_work_read_bits` (field); `docs/api/collections.md`.
- `union_work_write_bits` (field); `docs/api/collections.md`.
- `union_work_compare_bits` (field); `docs/api/collections.md`.
- `union_work_encoder` (field); `docs/api/collections.md`.
- `union_work_unary` (field); `docs/api/collections.md`.
- `union_work_event_count` (field); `docs/api/collections.md`.
- `union_work_actions` (field); `docs/api/collections.md`.
- `union_trace_work` (Definition); `docs/api/collections.md`.
- `union_source_work_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditHistoricalDENSEAdequacy`.

- `slot_batch_cost`: `slot_batch_cost_statement`; owner AUD-CL-DENSE.

Future proof module: `CollectionsAuditHistoricalUFAdequacy`.

- `trace_find_result`: `trace_find_result_statement`; owner AUD-CL-UF.
- `trace_union_result`: `trace_union_result_statement`; owner AUD-CL-UF.
- `trace_actions_result`: `trace_actions_result_statement`; owner AUD-CL-UF.
- `trace_branch_sum`: `trace_branch_sum_statement`; owner AUD-CL-UF.
- `union_source_work`: `union_source_work_statement`; owner AUD-CL-UF.

## CollectionsAuditInter

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_inter_event` (Inductive); `docs/api/collections.md`.
- `AuditInterRoot` (constructor); `docs/api/collections.md`.
- `AuditInterMerge` (constructor); `docs/api/collections.md`.
- `AuditInterDrop` (constructor); `docs/api/collections.md`.
- `AuditInterDiscard` (constructor); `docs/api/collections.md`.
- `AuditInterValue` (constructor); `docs/api/collections.md`.
- `AuditInterNode` (constructor); `docs/api/collections.md`.
- `audit_inter_drop_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_inter_drop` (Definition); `docs/api/collections.md`.
- `audit_inter_value` (Definition); `docs/api/collections.md`.
- `audit_inter_merge_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_inter` (Definition); `docs/api/collections.md`.
- `audit_finset_inter_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_inter_count_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_inter_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_inter_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditInterAdequacy`.

- `audit_finset_inter_erases`: `audit_finset_inter_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_inter_count`: `audit_finset_inter_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_inter_source_bound`: `audit_finset_inter_source_bound_statement`; owner
  AUD-CL-TRAVERSE.

## CollectionsAuditMap

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_map_event` (Inductive); `docs/api/collections.md`.
- `AuditMapGet` (constructor); `docs/api/collections.md`.
- `AuditMapSet` (constructor); `docs/api/collections.md`.
- `AuditMapRemove` (constructor); `docs/api/collections.md`.
- `audit_map_get` (Definition); `docs/api/collections.md`.
- `audit_map_set` (Definition); `docs/api/collections.md`.
- `audit_map_remove` (Definition); `docs/api/collections.md`.
- `audit_map_get_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_set_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_remove_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_get_source_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_set_source_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_remove_source_work_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditMapAdequacy`.

- `audit_map_get_erases`: `audit_map_get_erases_statement`; owner AUD-CL-TRIE.
- `audit_map_set_erases`: `audit_map_set_erases_statement`; owner AUD-CL-TRIE.
- `audit_map_remove_erases`: `audit_map_remove_erases_statement`; owner AUD-CL-TRIE.
- `audit_map_get_source_work_bound`: `audit_map_get_source_work_bound_statement`; owner AUD-CL-TRIE.
- `audit_map_set_source_work_bound`: `audit_map_set_source_work_bound_statement`; owner AUD-CL-TRIE.
- `audit_map_remove_source_work_bound`: `audit_map_remove_source_work_bound_statement`; owner
  AUD-CL-TRIE.

## CollectionsAuditMapFold

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_map_fold_event` (Inductive); `docs/api/collections.md`.
- `AuditMapFoldNode` (constructor); `docs/api/collections.md`.
- `AuditMapFoldCall` (constructor); `docs/api/collections.md`.
- `audit_map_fold_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_map_fold` (Definition); `docs/api/collections.md`.
- `audit_map_fold_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_fold_count_statement` (Definition); `docs/api/collections.md`.
- `audit_map_fold_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_fold_child_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_fold_source_work_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditMapFoldAdequacy`.

- `audit_map_fold_erases`: `audit_map_fold_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_fold_count`: `audit_map_fold_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_fold_source_work_bound`: `audit_map_fold_source_work_bound_statement`; owner
  AUD-CL-TRAVERSE.

## CollectionsAuditMapTraverse

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_map_transform_event` (Inductive); `docs/api/collections.md`.
- `AuditMapTransformNode` (constructor); `docs/api/collections.md`.
- `AuditMapTransformCall` (constructor); `docs/api/collections.md`.
- `AuditMapTransformBuilt` (constructor); `docs/api/collections.md`.
- `audit_map_transform_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_map_transform` (Definition); `docs/api/collections.md`.
- `audit_map_transform_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_transform_count_statement` (Definition); `docs/api/collections.md`.
- `audit_map_union_event` (Inductive); `docs/api/collections.md`.
- `AuditMapUnionEnter` (constructor); `docs/api/collections.md`.
- `AuditMapUnionCall` (constructor); `docs/api/collections.md`.
- `AuditMapUnionBuilt` (constructor); `docs/api/collections.md`.
- `AuditMapUnionRoot` (constructor); `docs/api/collections.md`.
- `audit_map_union_value` (Definition); `docs/api/collections.md`.
- `audit_map_union_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_map_union` (Definition); `docs/api/collections.md`.
- `audit_map_union_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_union_count_statement` (Definition); `docs/api/collections.md`.
- `audit_map_transform_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_transform_child_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_transform_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_union_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_union_child_work` (Fixpoint); `docs/api/collections.md`.
- `audit_map_union_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditMapTraverseAdequacy`.

- `audit_map_transform_erases`: `audit_map_transform_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_transform_count`: `audit_map_transform_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_union_erases`: `audit_map_union_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_union_count`: `audit_map_union_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_map_transform_source_bound`: `audit_map_transform_source_bound_statement`; owner
  AUD-CL-TRAVERSE.
- `audit_map_union_source_bound`: `audit_map_union_source_bound_statement`; owner AUD-CL-TRAVERSE.

## CollectionsAuditPrepared

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_prepared_event` (Inductive); `docs/api/collections.md`.
- `AuditPreparedEncode` (constructor); `docs/api/collections.md`.
- `AuditPreparedRead` (constructor); `docs/api/collections.md`.
- `AuditPreparedWrite` (constructor); `docs/api/collections.md`.
- `AuditPreparedRemove` (constructor); `docs/api/collections.md`.
- `audit_prepare_key` (Definition); `docs/api/collections.md`.
- `audit_prepared_lookup` (Definition); `docs/api/collections.md`.
- `audit_prepared_update` (Definition); `docs/api/collections.md`.
- `audit_prepared_remove` (Definition); `docs/api/collections.md`.
- `audit_prepare_key_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_lookup_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_update_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_remove_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_prepared_lookup_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_update_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_remove_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_prepared_encoder_calls` (Fixpoint); `docs/api/collections.md`.
- `audit_prepared_encoder_reuse_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditPreparedAdequacy`.

- `audit_prepare_key_erases`: `audit_prepare_key_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepared_lookup_erases`: `audit_prepared_lookup_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepared_update_erases`: `audit_prepared_update_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepared_remove_erases`: `audit_prepared_remove_erases_statement`; owner AUD-CL-DENSE.
- `audit_prepared_lookup_source_bound`: `audit_prepared_lookup_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepared_update_source_bound`: `audit_prepared_update_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepared_remove_source_bound`: `audit_prepared_remove_source_bound_statement`; owner
  AUD-CL-DENSE.
- `audit_prepared_encoder_reuse`: `audit_prepared_encoder_reuse_statement`; owner AUD-CL-DENSE.

## CollectionsAuditPrimitive

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_trie_left_source` (Definition); `docs/api/collections.md`.
- `audit_trie_right_source` (Definition); `docs/api/collections.md`.
- `audit_trie_value_source` (Definition); `docs/api/collections.md`.
- `audit_trie_left_source_adequate_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_right_source_adequate_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_value_source_adequate_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_node_source` (Definition); `docs/api/collections.md`.
- `audit_trie_node_source_adequate_statement` (Definition); `docs/api/collections.md`.
- `audit_map_code_get_run` (Inductive); `docs/api/collections.md`.
- `AuditMapCodeGet` (constructor); `docs/api/collections.md`.
- `audit_map_code_get_run_total_statement` (Definition); `docs/api/collections.md`.
- `audit_map_code_get_run_correct_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_access_source_clauses_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_eqb_event` (Inductive); `docs/api/collections.md`.
- `AuditPositiveEqb` (constructor); `docs/api/collections.md`.
- `audit_positive_eqb` (Fixpoint); `docs/api/collections.md`.
- `audit_positive_eqb_source_work` (Definition); `docs/api/collections.md`.
- `audit_positive_eqb_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_positive_eqb_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditPrimitiveAdequacy`.

- `audit_trie_left_source_adequate`: `audit_trie_left_source_adequate_statement`; owner AUD-CL-TRIE.
- `audit_trie_right_source_adequate`: `audit_trie_right_source_adequate_statement`; owner
  AUD-CL-TRIE.
- `audit_trie_value_source_adequate`: `audit_trie_value_source_adequate_statement`; owner
  AUD-CL-TRIE.
- `audit_trie_node_source_adequate`: `audit_trie_node_source_adequate_statement`; owner AUD-CL-TRIE.
- `audit_map_code_get_run_total`: `audit_map_code_get_run_total_statement`; owner AUD-CL-TRIE.
- `audit_map_code_get_run_correct`: `audit_map_code_get_run_correct_statement`; owner AUD-CL-TRIE.
- `audit_trie_access_source_clauses`: `audit_trie_access_source_clauses_statement`; owner
  AUD-CL-TRIE.
- `audit_positive_eqb_erases`: `audit_positive_eqb_erases_statement`; owner AUD-CL-TRIE.
- `audit_positive_eqb_source_bound`: `audit_positive_eqb_source_bound_statement`; owner AUD-CL-TRIE.

## CollectionsAuditState

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `PreparedKey` (constructor); `docs/api/collections.md`.
- `prepared_key` (Record); `docs/api/collections.md`.
- `key_value` (field); `docs/api/collections.md`.
- `key_code` (field); `docs/api/collections.md`.
- `key_valid` (Definition); `docs/api/collections.md`.
- `prepare_key` (Definition); `docs/api/collections.md`.
- `prepare_key_valid_statement` (Definition); `docs/api/collections.md`.
- `prepared_lookup` (Definition); `docs/api/collections.md`.
- `prepared_update` (Definition); `docs/api/collections.md`.
- `prepared_remove` (Definition); `docs/api/collections.md`.
- `prepared_key_refinement_statement` (Definition); `docs/api/collections.md`.
- `prepared_key_injection_statement` (Definition); `docs/api/collections.md`.
- `prepared_key_update_statement` (Definition); `docs/api/collections.md`.
- `prepared_pair_statement` (Definition); `docs/api/collections.md`.
- `prepared_key_bits` (Definition); `docs/api/collections.md`.
- `prepared_list_injection_statement` (Definition); `docs/api/collections.md`.
- `prepared_pair_bits_statement` (Definition); `docs/api/collections.md`.
- `prepared_list_bits_statement` (Definition); `docs/api/collections.md`.
- `slot_map` (Definition); `docs/api/collections.md`.
- `slot_valid` (Definition); `docs/api/collections.md`.
- `prepare_slot` (Definition); `docs/api/collections.md`.
- `slot_read` (Definition); `docs/api/collections.md`.
- `slot_lookup` (Definition); `docs/api/collections.md`.
- `slot_update` (Definition); `docs/api/collections.md`.
- `slot_elements` (Definition); `docs/api/collections.md`.
- `slot_to_map` (Definition); `docs/api/collections.md`.
- `dense_map_refines` (Definition); `docs/api/collections.md`.
- `slot_of_map` (Definition); `docs/api/collections.md`.
- `slot_update_statement` (Definition); `docs/api/collections.md`.
- `slot_elements_statement` (Definition); `docs/api/collections.md`.
- `slot_canonical_statement` (Definition); `docs/api/collections.md`.
- `slot_to_map_statement` (Definition); `docs/api/collections.md`.
- `slot_of_map_statement` (Definition); `docs/api/collections.md`.
- `slot_prepare_statement` (Definition); `docs/api/collections.md`.
- `slot_outside_statement` (Definition); `docs/api/collections.md`.
- `slot_empty_statement` (Definition); `docs/api/collections.md`.
- `slot_present_update_statement` (Definition); `docs/api/collections.md`.
- `prepare_slots` (Definition); `docs/api/collections.md`.
- `read_slots` (Definition); `docs/api/collections.md`.
- `slot_batch_refinement_statement` (Definition); `docs/api/collections.md`.
- `slot_remove` (Definition); `docs/api/collections.md`.
- `slot_update_refines_statement` (Definition); `docs/api/collections.md`.
- `slot_remove_refines_statement` (Definition); `docs/api/collections.md`.
- `slot_remove_frame_statement` (Definition); `docs/api/collections.md`.
- `slot_remove_outside_statement` (Definition); `docs/api/collections.md`.
- `slot_elements_refines_statement` (Definition); `docs/api/collections.md`.
- `DenseSlotToken` (constructor); `docs/api/collections.md`.
- `dense_slot_token` (Record); `docs/api/collections.md`.
- `dense_token_key` (field); `docs/api/collections.md`.
- `dense_token_index` (field); `docs/api/collections.md`.
- `dense_token_valid` (Definition); `docs/api/collections.md`.
- `dense_token_prepare` (Definition); `docs/api/collections.md`.
- `dense_token_read` (Definition); `docs/api/collections.md`.
- `dense_token_prepare_statement` (Definition); `docs/api/collections.md`.
- `dense_token_read_statement` (Definition); `docs/api/collections.md`.
- `dense_token_scope_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditStateDENSEAdequacy`.

- `prepared_key_refinement`: `prepared_key_refinement_statement`; owner AUD-CL-DENSE.
- `prepared_key_update`: `prepared_key_update_statement`; owner AUD-CL-DENSE.
- `slot_update`: `slot_update_statement`; owner AUD-CL-DENSE.
- `slot_elements`: `slot_elements_statement`; owner AUD-CL-DENSE.
- `slot_canonical`: `slot_canonical_statement`; owner AUD-CL-DENSE.
- `slot_to_map`: `slot_to_map_statement`; owner AUD-CL-DENSE.
- `slot_of_map`: `slot_of_map_statement`; owner AUD-CL-DENSE.
- `slot_prepare`: `slot_prepare_statement`; owner AUD-CL-DENSE.
- `slot_outside`: `slot_outside_statement`; owner AUD-CL-DENSE.
- `slot_empty`: `slot_empty_statement`; owner AUD-CL-DENSE.
- `slot_present_update`: `slot_present_update_statement`; owner AUD-CL-DENSE.
- `slot_batch_refinement`: `slot_batch_refinement_statement`; owner AUD-CL-DENSE.
- `slot_update_refines`: `slot_update_refines_statement`; owner AUD-CL-DENSE.
- `slot_remove_refines`: `slot_remove_refines_statement`; owner AUD-CL-DENSE.
- `slot_remove_frame`: `slot_remove_frame_statement`; owner AUD-CL-DENSE.
- `slot_remove_outside`: `slot_remove_outside_statement`; owner AUD-CL-DENSE.
- `slot_elements_refines`: `slot_elements_refines_statement`; owner AUD-CL-DENSE.
- `dense_token_prepare`: `dense_token_prepare_statement`; owner AUD-CL-DENSE.
- `dense_token_read`: `dense_token_read_statement`; owner AUD-CL-DENSE.
- `dense_token_scope`: `dense_token_scope_statement`; owner AUD-CL-DENSE.

Future proof module: `CollectionsAuditStateENCAdequacy`.

- `prepare_key_valid`: `prepare_key_valid_statement`; owner AUD-CL-ENC.
- `prepared_key_injection`: `prepared_key_injection_statement`; owner AUD-CL-ENC.
- `prepared_pair`: `prepared_pair_statement`; owner AUD-CL-ENC.
- `prepared_list_injection`: `prepared_list_injection_statement`; owner AUD-CL-ENC.
- `prepared_pair_bits`: `prepared_pair_bits_statement`; owner AUD-CL-ENC.
- `prepared_list_bits`: `prepared_list_bits_statement`; owner AUD-CL-ENC.

## CollectionsAuditTraversalBudget

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_map_transform_calls_source` (Definition); `docs/api/collections.md`.
- `audit_map_union_calls_source` (Definition); `docs/api/collections.md`.
- `audit_map_fold_calls_source` (Definition); `docs/api/collections.md`.
- `audit_map_transform_input_budget` (Definition); `docs/api/collections.md`.
- `audit_map_union_input_budget` (Definition); `docs/api/collections.md`.
- `audit_map_fold_input_budget_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_map_fold_input_budget` (Definition); `docs/api/collections.md`.
- `audit_map_transform_adapted_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_union_adapted_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_map_fold_adapted_input_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditTraversalBudgetAdequacy`.

- `audit_map_transform_adapted_input_bound`: `audit_map_transform_adapted_input_bound_statement`;
  owner AUD-CL-TRAVERSE.
- `audit_map_union_adapted_input_bound`: `audit_map_union_adapted_input_bound_statement`; owner
  AUD-CL-TRAVERSE.
- `audit_map_fold_adapted_input_bound`: `audit_map_fold_adapted_input_bound_statement`; owner
  AUD-CL-TRAVERSE.

## CollectionsAuditTrie

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_trie_call` (Inductive); `docs/api/collections.md`.
- `AuditTrieKey` (constructor); `docs/api/collections.md`.
- `AuditTrieLeft` (constructor); `docs/api/collections.md`.
- `AuditTrieRight` (constructor); `docs/api/collections.md`.
- `AuditTrieValue` (constructor); `docs/api/collections.md`.
- `AuditTrieNode` (constructor); `docs/api/collections.md`.
- `audit_trie_get` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_update` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_set` (Definition); `docs/api/collections.md`.
- `audit_trie_remove` (Definition); `docs/api/collections.md`.
- `audit_map_code_get` (Definition); `docs/api/collections.md`.
- `audit_trie_get_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_set_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_remove_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_map_code_get_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_get_events_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_update_events_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_accessor_work` (Definition); `docs/api/collections.md`.
- `audit_trie_node_work` (Definition); `docs/api/collections.md`.
- `audit_trie_get_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_update_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_get_source_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_update_source_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_get_run` (Inductive); `docs/api/collections.md`.
- `AuditGetHere` (constructor); `docs/api/collections.md`.
- `AuditGetLeft` (constructor); `docs/api/collections.md`.
- `AuditGetRight` (constructor); `docs/api/collections.md`.
- `audit_trie_get_run_correct_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_get_run_total_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_update_run` (Inductive); `docs/api/collections.md`.
- `AuditUpdateHere` (constructor); `docs/api/collections.md`.
- `AuditUpdateLeft` (constructor); `docs/api/collections.md`.
- `AuditUpdateRight` (constructor); `docs/api/collections.md`.
- `audit_trie_update_run_correct_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_update_run_total_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_get_trace_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_update_trace_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_trie_get_trace_adequate_statement` (Definition); `docs/api/collections.md`.
- `audit_trie_update_trace_adequate_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditTrieAdequacy`.

- `audit_trie_get_erases`: `audit_trie_get_erases_statement`; owner AUD-CL-TRIE.
- `audit_trie_set_erases`: `audit_trie_set_erases_statement`; owner AUD-CL-TRIE.
- `audit_trie_remove_erases`: `audit_trie_remove_erases_statement`; owner AUD-CL-TRIE.
- `audit_map_code_get_erases`: `audit_map_code_get_erases_statement`; owner AUD-CL-TRIE.
- `audit_trie_get_events_bound`: `audit_trie_get_events_bound_statement`; owner AUD-CL-TRIE.
- `audit_trie_update_events_bound`: `audit_trie_update_events_bound_statement`; owner AUD-CL-TRIE.
- `audit_trie_get_source_work_bound`: `audit_trie_get_source_work_bound_statement`; owner
  AUD-CL-TRIE.
- `audit_trie_update_source_work_bound`: `audit_trie_update_source_work_bound_statement`; owner
  AUD-CL-TRIE.
- `audit_trie_get_run_correct`: `audit_trie_get_run_correct_statement`; owner AUD-CL-TRIE.
- `audit_trie_get_run_total`: `audit_trie_get_run_total_statement`; owner AUD-CL-TRIE.
- `audit_trie_update_run_correct`: `audit_trie_update_run_correct_statement`; owner AUD-CL-TRIE.
- `audit_trie_update_run_total`: `audit_trie_update_run_total_statement`; owner AUD-CL-TRIE.
- `audit_trie_get_trace_adequate`: `audit_trie_get_trace_adequate_statement`; owner AUD-CL-TRIE.
- `audit_trie_update_trace_adequate`: `audit_trie_update_trace_adequate_statement`; owner
  AUD-CL-TRIE.

## CollectionsAuditUnion

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_union_event` (Inductive); `docs/api/collections.md`.
- `AuditUnionEnter` (constructor); `docs/api/collections.md`.
- `AuditUnionNode` (constructor); `docs/api/collections.md`.
- `AuditUnionRoot` (constructor); `docs/api/collections.md`.
- `audit_set_union_value` (Definition); `docs/api/collections.md`.
- `audit_set_union_ne` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_union` (Definition); `docs/api/collections.md`.
- `audit_finset_union_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_union_count_statement` (Definition); `docs/api/collections.md`.
- `audit_finset_union_source_work` (Fixpoint); `docs/api/collections.md`.
- `audit_finset_union_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditUnionAdequacy`.

- `audit_finset_union_erases`: `audit_finset_union_erases_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_union_count`: `audit_finset_union_count_statement`; owner AUD-CL-TRAVERSE.
- `audit_finset_union_source_bound`: `audit_finset_union_source_bound_statement`; owner
  AUD-CL-TRAVERSE.

## CollectionsAuditUnionFind

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_uf_event` (Inductive); `docs/api/collections.md`.
- `AuditUFFindCase` (constructor); `docs/api/collections.md`.
- `AuditUFParentRead` (constructor); `docs/api/collections.md`.
- `AuditUFParentWrite` (constructor); `docs/api/collections.md`.
- `AuditUFRankRead` (constructor); `docs/api/collections.md`.
- `AuditUFRankWrite` (constructor); `docs/api/collections.md`.
- `AuditUFEncode` (constructor); `docs/api/collections.md`.
- `AuditUFEqual` (constructor); `docs/api/collections.md`.
- `AuditUFRankCompare` (constructor); `docs/api/collections.md`.
- `AuditUFRankMax` (constructor); `docs/api/collections.md`.
- `AuditUFKeysParents` (constructor); `docs/api/collections.md`.
- `AuditUFKeysRanks` (constructor); `docs/api/collections.md`.
- `AuditUFKeysUnion` (constructor); `docs/api/collections.md`.
- `AuditUFKeysElements` (constructor); `docs/api/collections.md`.
- `AuditUFHistoryCase` (constructor); `docs/api/collections.md`.
- `audit_uf_find_fuel` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_find` (Definition); `docs/api/collections.md`.
- `audit_uf_rank_of` (Definition); `docs/api/collections.md`.
- `audit_uf_touch` (Definition); `docs/api/collections.md`.
- `audit_uf_link` (Definition); `docs/api/collections.md`.
- `audit_uf_union` (Definition); `docs/api/collections.md`.
- `audit_uf_equivb` (Definition); `docs/api/collections.md`.
- `audit_uf_keys` (Definition); `docs/api/collections.md`.
- `audit_uf_find_fuel_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_find_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_union_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_equivb_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_keys_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_unary_compare_work` (Definition); `docs/api/collections.md`.
- `audit_uf_primitive_work` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_source_work` (Definition); `docs/api/collections.md`.
- `audit_uf_find_fuel_count_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_union_count_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_equivb_count_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_find_fuel_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_union_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_equivb_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_keys_work_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_keys_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_action` (Inductive); `docs/api/collections.md`.
- `AuditUFFind` (constructor); `docs/api/collections.md`.
- `AuditUFUnion` (constructor); `docs/api/collections.md`.
- `audit_uf_action_run` (Definition); `docs/api/collections.md`.
- `audit_uf_original_action` (Definition); `docs/api/collections.md`.
- `audit_uf_history` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_history_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_of_unions` (Definition); `docs/api/collections.md`.
- `audit_uf_of_unions_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_history_frame_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_history_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_of_unions_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_branches` (Definition); `docs/api/collections.md`.
- `audit_uf_branches_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditUnionFindAdequacy`.

- `audit_uf_find_fuel_erases`: `audit_uf_find_fuel_erases_statement`; owner AUD-CL-UF.
- `audit_uf_find_erases`: `audit_uf_find_erases_statement`; owner AUD-CL-UF.
- `audit_uf_union_erases`: `audit_uf_union_erases_statement`; owner AUD-CL-UF.
- `audit_uf_equivb_erases`: `audit_uf_equivb_erases_statement`; owner AUD-CL-UF.
- `audit_uf_keys_erases`: `audit_uf_keys_erases_statement`; owner AUD-CL-UF.
- `audit_uf_find_fuel_count`: `audit_uf_find_fuel_count_statement`; owner AUD-CL-UF.
- `audit_uf_union_count`: `audit_uf_union_count_statement`; owner AUD-CL-UF.
- `audit_uf_equivb_count`: `audit_uf_equivb_count_statement`; owner AUD-CL-UF.
- `audit_uf_find_fuel_work_bound`: `audit_uf_find_fuel_work_bound_statement`; owner AUD-CL-UF.
- `audit_uf_union_work_bound`: `audit_uf_union_work_bound_statement`; owner AUD-CL-UF.
- `audit_uf_equivb_work_bound`: `audit_uf_equivb_work_bound_statement`; owner AUD-CL-UF.
- `audit_uf_keys_work_bound`: `audit_uf_keys_work_bound_statement`; owner AUD-CL-UF.
- `audit_uf_keys_input_bound`: `audit_uf_keys_input_bound_statement`; owner AUD-CL-UF.
- `audit_uf_history_erases`: `audit_uf_history_erases_statement`; owner AUD-CL-UF.
- `audit_uf_of_unions_erases`: `audit_uf_of_unions_erases_statement`; owner AUD-CL-UF.
- `audit_uf_history_bound`: `audit_uf_history_bound_statement`; owner AUD-CL-UF.
- `audit_uf_of_unions_source_bound`: `audit_uf_of_unions_source_bound_statement`; owner AUD-CL-UF.
- `audit_uf_branches_bound`: `audit_uf_branches_bound_statement`; owner AUD-CL-UF.

## CollectionsAuditUnionFindAdapters

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_uf_pair_encode` (Definition); `docs/api/collections.md`.
- `audit_uf_list_encode` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_of_unions` (Definition); `docs/api/collections.md`.
- `audit_uf_list_of_unions` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_of_unions_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_list_of_unions_erases_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_encoder_work` (Definition); `docs/api/collections.md`.
- `audit_uf_list_encoder_work` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_of_unions_source_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_list_of_unions_source_bound_statement` (Definition); `docs/api/collections.md`.

Future proof module: `CollectionsAuditUnionFindAdaptersAdequacy`.

- `audit_uf_pair_of_unions_erases`: `audit_uf_pair_of_unions_erases_statement`; owner AUD-CL-UF.
- `audit_uf_list_of_unions_erases`: `audit_uf_list_of_unions_erases_statement`; owner AUD-CL-UF.
- `audit_uf_pair_of_unions_source_bound`: `audit_uf_pair_of_unions_source_bound_statement`; owner
  AUD-CL-UF.
- `audit_uf_list_of_unions_source_bound`: `audit_uf_list_of_unions_source_bound_statement`; owner
  AUD-CL-UF.

## CollectionsAuditUnionFindWhole

Public package: `Galois.Collections`.

Card: AUD-CL-MODELS

- `audit_uf_read_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_write_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_find_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_touch_input_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_link_input_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_union_input_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_equivb_input_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_action_input_budget` (Definition); `docs/api/collections.md`.
- `audit_uf_history_input_budget` (Fixpoint); `docs/api/collections.md`.
- `audit_uf_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_pair_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_list_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_branches_whole_input_bound_statement` (Definition); `docs/api/collections.md`.
- `audit_uf_initial_find_whole_budget` (Example); `docs/api/collections.md`.

Future proof module: `CollectionsAuditUnionFindWholeAdequacy`.

- `audit_uf_whole_input_bound`: `audit_uf_whole_input_bound_statement`; owner AUD-CL-UF.
- `audit_uf_pair_whole_input_bound`: `audit_uf_pair_whole_input_bound_statement`; owner AUD-CL-UF.
- `audit_uf_list_whole_input_bound`: `audit_uf_list_whole_input_bound_statement`; owner AUD-CL-UF.
- `audit_uf_branches_whole_input_bound`: `audit_uf_branches_whole_input_bound_statement`; owner
  AUD-CL-UF.

## AnalysesAuditMemoryPhiFacade

Public package: `Galois.Analyses`.
Card: AUD-MP

- `memory_prune_with_map`: `memory_prune_with_map_type`; library WF proof packing.
- `memory_prune`: `memory_prune_type`; graph projection of the same packed result.

<!-- AUD-API-CL-MEM-NAMES-END -->

<!-- AUD-API-GR-SQ-NAMES-BEGIN -->

# Graph and SSA audit names

## AnalysesAuditPortfolioCost

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `analyses_portfolio_source_contract_statement` (def).

Future proof module: `AnalysesAuditPortfolioCostAdequacy`.

- `analyses_portfolio_source_contract_holds`:
  `AnalysesAuditPortfolioCost.analyses_portfolio_source_contract_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSeg

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_strict_event` (ind).
- `AuditSegGen` (constr).
- `AuditSegKill` (constr).
- `AuditSegEncode` (constr).
- `AuditSegEqual` (constr).
- `audit_seg_strict_mentions` (Fixpoint).
- `audit_seg_strict_transfer` (def).
- `audit_seg_mentions_execution` (ind).
- `AuditSegMentionsNil` (constr).
- `AuditSegMentionsCons` (constr).
- `audit_seg_transfer_execution` (ind).
- `AuditSegTransferRun` (constr).
- `audit_seg_transfer_execution_exists_statement` (def).
- `audit_seg_strict_transfer_statement` (def).
- `audit_seg_model_event` (def).
- `audit_seg_model_work` (def).
- `audit_seg_model_expected` (def).
- `audit_seg_model_statement` (def).
- `audit_seg_reconstruct_call` (ind).
- `AuditSegReconCase` (constr).
- `AuditSegReconAdd` (constr).
- `AuditSegReconMem` (constr).
- `AuditSegReconInterior` (constr).
- `AuditSegReconPath` (constr).
- `AuditSegReconSource` (constr).
- `AuditSegReconTarget` (constr).
- `AuditSegReconCut` (constr).
- `AuditSegReconTransfer` (constr).
- `audit_seg_recon_setup` (Fixpoint).
- `audit_seg_firstn` (Fixpoint).
- `audit_seg_skipn` (Fixpoint).
- `audit_seg_forward_fold` (Fixpoint).
- `audit_seg_backward_fold` (Fixpoint).
- `audit_seg_recon_probe` (def).
- `audit_seg_recon_counted` (def).
- `audit_seg_recon_event_work` (def).
- `audit_seg_recon_work` (def).
- `audit_seg_recon_path` (def).
- `audit_seg_recon_event_bound` (def).
- `audit_seg_recon_width` (def).
- `audit_seg_recon_budget` (def).
- `audit_seg_recon_statement` (def).

Future proof module: `AnalysesAuditSegAdequacy`.

- `audit_seg_transfer_execution_exists_holds`:
  `AnalysesAuditSeg.audit_seg_transfer_execution_exists_statement`; owner AUD-SQ-SEG.
- `audit_seg_strict_transfer_holds`: `AnalysesAuditSeg.audit_seg_strict_transfer_statement`; owner
  AUD-SQ-SEG.
- `audit_seg_model_holds`: `AnalysesAuditSeg.audit_seg_model_statement`; owner AUD-SQ-SEG.
- `audit_seg_recon_correct`: `AnalysesAuditSeg.audit_seg_recon_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegBatch

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_sparse_batch_probes` (Fixpoint).
- `audit_seg_sparse_setup_budget` (def).
- `audit_seg_sparse_batch_input_budget` (def).
- `audit_seg_sparse_batch_adapted_statement` (def).

Future proof module: `AnalysesAuditSegBatchAdequacy`.

- `audit_seg_sparse_batch_adapted_holds`:
  `AnalysesAuditSegBatch.audit_seg_sparse_batch_adapted_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegBuilder

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_transfer_source_event` (ind).
- `SegTransferCase` (constr).
- `SegTransferGen` (constr).
- `SegTransferKill` (constr).
- `SegTransferEncode` (constr).
- `SegTransferEqual` (constr).
- `audit_seg_transfer_source_mentions` (Fixpoint).
- `audit_seg_transfer_source_operands` (def).
- `audit_seg_event_source_counted` (def).
- `audit_seg_transfer_source_counted` (def).
- `audit_seg_transfer_source_event_work` (def).
- `audit_seg_transfer_source_event_external` (def).
- `audit_seg_transfer_source_work` (def).
- `audit_seg_transfer_source_external` (def).
- `audit_seg_transfer_source_budget` (def).
- `audit_seg_transfer_source_statement` (def).
- `audit_seg_transfer_source_event_budget` (def).
- `audit_seg_transfer_source_adapted_statement` (def).
- `audit_seg_transfer_source_contract_statement` (def).
- `audit_seg_build_callbacks` (rec).
- `seg_build_node_encode` (proj).
- `seg_build_edge_encode` (proj).
- `seg_build_expr_encode` (proj).
- `seg_build_out` (proj).
- `seg_build_target` (proj).
- `seg_build_source` (proj).
- `seg_build_gen` (proj).
- `seg_build_kill` (proj).
- `audit_seg_build_event` (ind).
- `SegBuildCase` (constr).
- `SegBuildPrepare` (constr).
- `SegBuildOut` (constr).
- `SegBuildTarget` (constr).
- `SegBuildSource` (constr).
- `SegBuildTransfer` (constr).
- `SegBuildSet` (constr).
- `SegBuildAdj` (constr).
- `SegBuildNodeMap` (constr).
- `SegBuildArcMap` (constr).
- `SegBuildOutput` (constr).
- `audit_seg_build_edges` (Fixpoint).
- `audit_seg_build_points` (Fixpoint).
- `audit_seg_build_candidates` (Fixpoint).
- `audit_seg_build_incoming` (Fixpoint).
- `audit_seg_build_arcs` (Fixpoint).
- `audit_seg_build_initial` (def).
- `audit_seg_splice_event` (ind).
- `SegSpliceCase` (constr).
- `SegSpliceSet` (constr).
- `SegSpliceNodeMap` (constr).
- `SegSpliceArcMap` (constr).
- `SegSpliceEncode` (constr).
- `SegSpliceEqual` (constr).
- `audit_seg_splice_compose` (def).
- `audit_seg_splice_join` (def).
- `audit_seg_splice_merge` (def).
- `audit_seg_splice_source_counted` (def).
- `audit_seg_splice_source_erasure_statement` (def).
- `audit_seg_splice_event_work` (def).
- `audit_seg_splice_event_external` (def).
- `audit_seg_splice_source_work` (def).
- `audit_seg_splice_source_external` (def).
- `audit_seg_splice_source_budget` (def).
- `audit_seg_splice_source_statement` (def).
- `audit_seg_splice_event_budget` (def).
- `audit_seg_splice_source_adapted_statement` (def).
- `audit_seg_splice_source_contract_statement` (def).
- `audit_seg_rope_event` (ind).
- `SegRopeLeaf` (constr).
- `SegRopeAppend` (constr).
- `audit_seg_rope_onto` (Fixpoint).
- `audit_seg_finish_event` (ind).
- `SegFinishCase` (constr).
- `SegFinishRopeMap` (constr).
- `SegFinishSummary` (constr).
- `SegFinishElements` (constr).
- `SegFinishTarget` (constr).
- `SegFinishSet` (constr).
- `SegFinishInterior` (constr).
- `SegFinishList` (constr).
- `audit_seg_removelast` (Fixpoint).
- `audit_seg_finish_positions` (Fixpoint).
- `audit_seg_finish_path_rows` (Fixpoint).
- `audit_seg_finish_interior` (Fixpoint).
- `audit_seg_finish_nodes` (Fixpoint).
- `audit_seg_finish_source_counted` (def).
- `audit_seg_finish_source_erasure_statement` (def).
- `audit_seg_graph_body` (ind).
- `SegGraphSet` (constr).
- `SegGraphAdj` (constr).
- `SegGraphArc` (constr).
- `SegGraphTarget` (constr).
- `SegGraphSource` (constr).
- `SegGraphNodeEncode` (constr).
- `SegGraphEdgeEncode` (constr).
- `SegGraphCase` (constr).
- `audit_seg_graph_out` (def).
- `audit_seg_graph_target` (def).
- `audit_seg_graph_source` (def).
- `audit_seg_graph_node_encode` (def).
- `audit_seg_graph_edge_encode` (def).
- `audit_seg_graph_callbacks_erasure_statement` (def).
- `audit_seg_rope_source_work` (def).
- `audit_seg_finish_event_work` (def).
- `audit_seg_finish_event_external` (def).
- `audit_seg_finish_source_work` (def).
- `audit_seg_finish_source_external` (def).
- `audit_seg_rope_input_size` (Fixpoint).
- `audit_seg_finish_source_budget` (def).
- `audit_seg_finish_source_statement` (def).
- `audit_seg_graph_body_work` (def).
- `audit_seg_graph_body_external` (def).
- `audit_seg_graph_body_budget` (def).
- `audit_seg_finish_event_budget` (def).
- `audit_seg_finish_source_adapted_statement` (def).
- `audit_seg_graph_call_budget` (def).
- `audit_seg_graph_callbacks_source_statement` (def).
- `audit_seg_graph_callbacks_adapted_statement` (def).
- `audit_seg_finish_source_contract_statement` (def).
- `audit_seg_graph_encoders_source_statement` (def).
- `audit_seg_graph_encoders_adapted_statement` (def).
- `audit_seg_graph_encoders_contract_statement` (def).
- `audit_seg_full_event` (ind).
- `SegFullBuild` (constr).
- `SegFullSplice` (constr).
- `SegFullFinish` (constr).
- `SegFullCase` (constr).
- `audit_seg_full_splices` (Fixpoint).
- `audit_seg_full_receipt` (rec).
- `audit_seg_full_index` (proj).
- `audit_seg_full_work_state` (proj).
- `audit_seg_full_result` (proj).
- `audit_seg_full_events` (proj).
- `audit_seg_full_source_counted` (def).
- `audit_seg_full_callbacks_erase` (def).
- `audit_seg_full_source_erasure_statement` (def).
- `audit_seg_build_event_work` (def).
- `audit_seg_build_event_external` (def).
- `audit_seg_full_event_work` (def).
- `audit_seg_full_event_external` (def).
- `audit_seg_full_source_work` (def).
- `audit_seg_full_source_external` (def).
- `audit_seg_full_input_scale` (def).
- `audit_seg_full_input_budget` (def).
- `audit_seg_full_intermediate_budget` (def).
- `audit_seg_full_source_statement` (def).
- `audit_seg_build_event_budget` (def).
- `audit_seg_full_event_budget` (def).
- `audit_seg_full_source_adapted_statement` (def).
- `audit_seg_full_source_contract_statement` (def).
- `audit_seg_builder_contract_statement` (def).
- `SegBuildCallbacks` (record-constructor).

Future proof module: `AnalysesAuditSegBuilderAdequacy`.

- `audit_seg_transfer_source_holds`: `AnalysesAuditSegBuilder.audit_seg_transfer_source_statement`;
  owner AUD-SQ-SEG.
- `audit_seg_transfer_source_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_transfer_source_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_transfer_source_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_transfer_source_contract_statement`; owner AUD-SQ-SEG.
- `audit_seg_splice_source_erasure_holds`:
  `AnalysesAuditSegBuilder.audit_seg_splice_source_erasure_statement`; owner AUD-SQ-SEG.
- `audit_seg_splice_source_holds`: `AnalysesAuditSegBuilder.audit_seg_splice_source_statement`;
  owner AUD-SQ-SEG.
- `audit_seg_splice_source_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_splice_source_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_splice_source_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_splice_source_contract_statement`; owner AUD-SQ-SEG.
- `audit_seg_finish_source_erasure_holds`:
  `AnalysesAuditSegBuilder.audit_seg_finish_source_erasure_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_callbacks_erasure_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_callbacks_erasure_statement`; owner AUD-SQ-SEG.
- `audit_seg_finish_source_holds`: `AnalysesAuditSegBuilder.audit_seg_finish_source_statement`;
  owner AUD-SQ-SEG.
- `audit_seg_finish_source_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_finish_source_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_callbacks_source_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_callbacks_source_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_callbacks_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_callbacks_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_finish_source_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_finish_source_contract_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_encoders_source_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_encoders_source_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_encoders_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_encoders_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_graph_encoders_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_graph_encoders_contract_statement`; owner AUD-SQ-SEG.
- `audit_seg_full_source_erasure_holds`:
  `AnalysesAuditSegBuilder.audit_seg_full_source_erasure_statement`; owner AUD-SQ-SEG.
- `audit_seg_full_source_holds`: `AnalysesAuditSegBuilder.audit_seg_full_source_statement`; owner
  AUD-SQ-SEG.
- `audit_seg_full_source_adapted_holds`:
  `AnalysesAuditSegBuilder.audit_seg_full_source_adapted_statement`; owner AUD-SQ-SEG.
- `audit_seg_full_source_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_full_source_contract_statement`; owner AUD-SQ-SEG.
- `audit_seg_builder_contract_holds`:
  `AnalysesAuditSegBuilder.audit_seg_builder_contract_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseAnnotated

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_annotated_engine` (ind).
- `DenseAnnotatedStop` (constr).
- `DenseAnnotatedContinue` (constr).
- `audit_dense_annotated_total` (ind).
- `DenseAnnotatedTotal` (constr).
- `audit_dense_annotated_total_erasure_statement` (def).

Future proof module: `AnalysesAuditSegDenseAnnotatedAdequacy`.

- `audit_dense_annotated_total_erasure`:
  `AnalysesAuditSegDenseAnnotated.audit_dense_annotated_total_erasure_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseBatch

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_probe_client_source` (def).
- `audit_dense_batch_budget` (def).
- `audit_dense_batch_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseBatchAdequacy`.

- `audit_dense_batch_source`: `AnalysesAuditSegDenseBatch.audit_dense_batch_source_statement`; owner
  AUD-SQ-SEG.

## AnalysesAuditSegDenseBudget

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_client_budget` (rec).
- `dense_node_budget` (proj).
- `dense_edge_budget` (proj).
- `dense_expr_budget` (proj).
- `dense_out_budget` (proj).
- `dense_target_budget` (proj).
- `dense_source_budget` (proj).
- `dense_gen_budget` (proj).
- `dense_kill_budget` (proj).
- `audit_dense_universe_external_budget` (def).
- `audit_dense_transfer_external_budget` (def).
- `audit_dense_seed_budget` (def).
- `audit_dense_continuation_budget` (def).
- `audit_dense_declared_budget` (def).
- `audit_dense_callback_instantiation_statement` (def).
- `AuditDenseClientBudget` (record-constructor).

Future proof module: `AnalysesAuditSegDenseBudgetAdequacy`.

- `audit_dense_callback_instantiation`:
  `AnalysesAuditSegDenseBudget.audit_dense_callback_instantiation_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseCallbacks

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_seed` (def).
- `audit_dense_rhs_source` (def).
- `audit_dense_continuation_source` (def).
- `audit_dense_priority` (def).
- `audit_dense_widening` (def).
- `audit_dense_declared_source` (def).

## AnalysesAuditSegDenseClient

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_client_source` (rec).
- `dense_node_source` (proj).
- `dense_edge_source` (proj).
- `dense_expr_source` (proj).
- `dense_out_source` (proj).
- `dense_target_source` (proj).
- `dense_source_source` (proj).
- `dense_gen_source` (proj).
- `dense_kill_source` (proj).
- `audit_dense_client_laws` (def).
- `audit_dense_client_body_work` (def).
- `audit_dense_expr_set_source` (def).
- `audit_dense_universe_client_source` (def).
- `audit_dense_transfer_client_source` (def).
- `audit_dense_fx_client_source` (def).
- `audit_dense_index_set_client_source` (def).
- `audit_dense_index_client_source` (def).
- `AuditDenseClientSource` (record-constructor).

## AnalysesAuditSegDenseInit

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_initial` (def).
- `audit_dense_initial_work` (def).
- `audit_dense_initial_budget` (def).
- `audit_dense_initial_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseInitAdequacy`.

- `audit_dense_initial_source`: `AnalysesAuditSegDenseInit.audit_dense_initial_source_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegDensePortfolio

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_portfolio_input_budget` (def).
- `audit_dense_portfolio_answers_statement` (def).
- `audit_dense_portfolio_budget_statement` (def).
- `audit_dense_portfolio_selected_source_statement` (def).
- `audit_dense_portfolio_contract_statement` (def).

Future proof module: `AnalysesAuditSegDensePortfolioAdequacy`.

- `audit_dense_portfolio_answers`:
  `AnalysesAuditSegDensePortfolio.audit_dense_portfolio_answers_statement`; owner AUD-SQ-SEG.
- `audit_dense_portfolio_budget`:
  `AnalysesAuditSegDensePortfolio.audit_dense_portfolio_budget_statement`; owner AUD-SQ-SEG.
- `audit_dense_portfolio_selected_source`:
  `AnalysesAuditSegDensePortfolio.audit_dense_portfolio_selected_source_statement`; owner
  AUD-SQ-SEG.
- `audit_dense_portfolio_contract`:
  `AnalysesAuditSegDensePortfolio.audit_dense_portfolio_contract_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseQuery

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_probe_event` (ind).
- `DenseProbeMap` (constr).
- `DenseProbeSet` (constr).
- `DenseProbeCase` (constr).
- `audit_dense_probe` (def).
- `audit_dense_probe_work` (def).
- `audit_dense_probe_budget` (def).
- `audit_dense_probe_event_budget` (def).
- `audit_dense_probe_source_statement` (def).
- `audit_dense_probe_batch` (Fixpoint).
- `audit_dense_probe_batch_budget` (def).
- `audit_dense_probe_batch_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseQueryAdequacy`.

- `audit_dense_probe_source`: `AnalysesAuditSegDenseQuery.audit_dense_probe_source_statement`; owner
  AUD-SQ-SEG.
- `audit_dense_probe_batch_source`:
  `AnalysesAuditSegDenseQuery.audit_dense_probe_batch_source_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseSets

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_subset_event` (ind).
- `DenseSubsetNode` (constr).
- `DenseSubsetValue` (constr).
- `audit_dense_subset_value` (def).
- `audit_dense_subset_ne` (Fixpoint).
- `audit_dense_subset` (def).
- `audit_dense_subset_work` (def).
- `audit_dense_subset_budget` (def).
- `audit_dense_subset_statement` (def).
- `audit_dense_inter` (def).
- `audit_dense_union` (def).
- `audit_dense_merge_statement` (def).

Future proof module: `AnalysesAuditSegDenseSetsAdequacy`.

- `audit_dense_subset_correct`: `AnalysesAuditSegDenseSets.audit_dense_subset_statement`; owner
  AUD-SQ-SEG.
- `audit_dense_merge`: `AnalysesAuditSegDenseSets.audit_dense_merge_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegDenseSolver

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_solution` (def).
- `audit_dense_solve_budget` (def).
- `audit_dense_solver_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseSolverAdequacy`.

- `audit_dense_solver_source`: `AnalysesAuditSegDenseSolver.audit_dense_solver_source_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegDenseSystem

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_fx_system` (def).
- `audit_dense_fx_static` (def).
- `audit_dense_fx_event` (ind).
- `DenseFxNodeEncode` (constr).
- `DenseFxEdgeEncode` (constr).
- `DenseFxOut` (constr).
- `DenseFxTarget` (constr).
- `DenseFxSource` (constr).
- `DenseFxUniverse` (constr).
- `DenseFxTransfer` (constr).
- `DenseFxSubset` (constr).
- `DenseFxInter` (constr).
- `DenseFxNodeMap` (constr).
- `DenseFxNodeSet` (constr).
- `DenseFxCase` (constr).
- `audit_dense_constraint_encode` (def).
- `audit_dense_node_encode` (def).
- `audit_dense_target` (def).
- `audit_dense_deps` (def).
- `audit_dense_index_model` (def).
- `audit_dense_index_source` (def).
- `audit_dense_constraints` (def).
- `audit_dense_constraints_budget` (def).
- `audit_dense_constraints_source_statement` (def).
- `audit_dense_fx_event_work` (def).
- `audit_dense_fx_index_budget` (def).
- `audit_dense_fx_index_statement` (def).

Future proof module: `AnalysesAuditSegDenseSystemAdequacy`.

- `audit_dense_constraints_source`:
  `AnalysesAuditSegDenseSystem.audit_dense_constraints_source_statement`; owner AUD-SQ-SEG.
- `audit_dense_fx_index`: `AnalysesAuditSegDenseSystem.audit_dense_fx_index_statement`; owner
  AUD-SQ-SEG.

## AnalysesAuditSegDenseTransfer

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_transfer_event` (ind).
- `DenseTransferUniverse` (constr).
- `DenseTransferElements` (constr).
- `DenseTransferSet` (constr).
- `DenseTransferUnion` (constr).
- `DenseTransferGen` (constr).
- `DenseTransferKill` (constr).
- `DenseTransferCase` (constr).
- `audit_dense_survivors` (Fixpoint).
- `audit_dense_clamp_filter` (Fixpoint).
- `audit_dense_clamp` (def).
- `audit_dense_transfer` (def).
- `audit_dense_transfer_event_work` (def).
- `audit_dense_transfer_work` (def).
- `audit_dense_transfer_budget` (def).
- `audit_dense_transfer_event_budget` (def).
- `audit_dense_transfer_source_statement` (def).
- `audit_dense_clamp_budget` (def).
- `audit_dense_clamp_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseTransferAdequacy`.

- `audit_dense_transfer_source`:
  `AnalysesAuditSegDenseTransfer.audit_dense_transfer_source_statement`; owner AUD-SQ-SEG.
- `audit_dense_clamp_source`: `AnalysesAuditSegDenseTransfer.audit_dense_clamp_source_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegDenseUniverse

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_dense_universe` (def).
- `audit_dense_universe_budget` (def).
- `audit_dense_universe_source_statement` (def).

Future proof module: `AnalysesAuditSegDenseUniverseAdequacy`.

- `audit_dense_universe_source`:
  `AnalysesAuditSegDenseUniverse.audit_dense_universe_source_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegFixpoint

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_fx_system` (def).
- `audit_seg_fx_static` (def).
- `audit_seg_fx_event` (ind).
- `SegFxCase` (constr).
- `SegFxGraph` (constr).
- `SegFxNodeEncode` (constr).
- `SegFxEdgeEncode` (constr).
- `SegFxNodeMap` (constr).
- `SegFxNodeSet` (constr).
- `SegFxSummary` (constr).
- `SegFxBool` (constr).
- `audit_seg_fx_constraint_encode` (def).
- `audit_seg_fx_node_encode` (def).
- `audit_seg_fx_target` (def).
- `audit_seg_fx_deps` (def).
- `audit_seg_fx_index_model` (def).
- `audit_seg_fx_index_source` (def).
- `audit_seg_fx_summary` (def).
- `audit_seg_fx_rhs` (def).
- `audit_seg_fx_priority` (def).
- `audit_seg_fx_widening` (def).
- `audit_seg_fx_declared_source` (def).
- `audit_seg_fx_event_work` (def).
- `audit_seg_fx_event_external` (def).
- `audit_seg_fx_event_external_budget` (def).
- `audit_seg_fx_node_budget` (def).
- `audit_seg_fx_edge_budget` (def).
- `audit_seg_fx_index_budget` (def).
- `audit_seg_fx_continuation_budget` (def).
- `audit_seg_fx_declared_budget` (def).
- `audit_seg_fx_instantiation_statement` (def).

Future proof module: `AnalysesAuditSegFixpointAdequacy`.

- `audit_seg_fx_instantiation_holds`:
  `AnalysesAuditSegFixpoint.audit_seg_fx_instantiation_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegQuery

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_query_expected` (def).
- `audit_seg_query_producer_budget` (def).
- `audit_seg_query_input_budget` (def).
- `audit_seg_query_adapted_statement` (def).
- `audit_seg_query_contract_statement` (def).

Future proof module: `AnalysesAuditSegQueryAdequacy`.

- `audit_seg_query_adapted_holds`: `AnalysesAuditSegQuery.audit_seg_query_adapted_statement`; owner
  AUD-SQ-SEG.
- `audit_seg_query_contract_holds`: `AnalysesAuditSegQuery.audit_seg_query_contract_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegReconstruct

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_reconstruct_event` (ind).
- `ReconCase` (constr).
- `ReconSet` (constr).
- `ReconInterior` (constr).
- `ReconPath` (constr).
- `ReconAssignment` (constr).
- `ReconGraph` (constr).
- `ReconTransfer` (constr).
- `audit_seg_reconstruct_cut` (def).
- `audit_seg_reconstruct_first` (Fixpoint).
- `audit_seg_reconstruct_skip` (Fixpoint).
- `audit_seg_reconstruct_forward` (Fixpoint).
- `audit_seg_reconstruct_backward` (Fixpoint).
- `audit_seg_reconstruct_probe` (def).
- `audit_seg_reconstruct_setup` (def).
- `audit_seg_reconstruct_counted` (def).
- `audit_seg_reconstruct_event_work` (def).
- `audit_seg_reconstruct_work` (def).
- `audit_seg_reconstruct_event_budget` (def).
- `audit_seg_reconstruct_input_scale` (def).
- `audit_seg_reconstruct_input_budget` (def).
- `audit_seg_reconstruct_adapted_statement` (def).

Future proof module: `AnalysesAuditSegReconstructAdequacy`.

- `audit_seg_reconstruct_adapted_holds`:
  `AnalysesAuditSegReconstruct.audit_seg_reconstruct_adapted_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSegSolver

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_solver_height` (def).
- `audit_seg_solver_adapted_statement` (def).
- `audit_seg_solver_contract_statement` (def).

Future proof module: `AnalysesAuditSegSolverAdequacy`.

- `audit_seg_solver_adapted_holds`: `AnalysesAuditSegSolver.audit_seg_solver_adapted_statement`;
  owner AUD-SQ-SEG.
- `audit_seg_solver_contract_holds`: `AnalysesAuditSegSolver.audit_seg_solver_contract_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegSystem

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_system_event` (ind).
- `SegSystemCase` (constr).
- `SegSystemGraph` (constr).
- `SegSystemAppend` (constr).
- `audit_seg_system_edges` (Fixpoint).
- `audit_seg_system_constraints` (def).
- `audit_seg_system_event_work` (def).
- `audit_seg_system_work` (def).
- `audit_seg_system_input_budget` (def).
- `audit_seg_system_event_budget` (def).
- `audit_seg_system_adapted_statement` (def).

Future proof module: `AnalysesAuditSegSystemAdequacy`.

- `audit_seg_system_adapted_holds`: `AnalysesAuditSegSystem.audit_seg_system_adapted_statement`;
  owner AUD-SQ-SEG.

## AnalysesAuditSegUniverse

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_seg_universe_event` (ind).
- `SegUniverseCase` (constr).
- `SegUniverseOut` (constr).
- `SegUniverseGen` (constr).
- `SegUniverseSet` (constr).
- `SegUniverseElements` (constr).
- `SegUniverseAppend` (constr).
- `audit_seg_universe_edges` (Fixpoint).
- `audit_seg_universe_gen` (Fixpoint).
- `audit_seg_universe_counted` (def).
- `audit_seg_universe_event_work` (def).
- `audit_seg_universe_work` (def).
- `audit_seg_universe_event_budget` (def).
- `audit_seg_universe_input_budget` (def).
- `audit_seg_universe_adapted_statement` (def).

Future proof module: `AnalysesAuditSegUniverseAdequacy`.

- `audit_seg_universe_adapted_holds`:
  `AnalysesAuditSegUniverse.audit_seg_universe_adapted_statement`; owner AUD-SQ-SEG.

## AnalysesAuditSsaFacts

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_fact_event` (ind).
- `LiveFactCase` (constr).
- `LiveFactList` (constr).
- `LiveFactOut` (constr).
- `LiveFactTarget` (constr).
- `LiveFactUse` (constr).
- `LiveFactDef` (constr).
- `LiveFactExit` (constr).
- `LiveFactNode` (constr).
- `LiveFactEdge` (constr).
- `LiveFactValue` (constr).
- `audit_live_fact_edges` (Fixpoint).
- `audit_live_fact_edge_values` (Fixpoint).
- `audit_live_fact_rows` (Fixpoint).
- `audit_live_fact_succ_edges` (Fixpoint).
- `audit_live_fact_succ_nodes` (Fixpoint).
- `audit_live_fact_exit_values` (Fixpoint).
- `audit_live_fact_exit_nodes` (Fixpoint).
- `audit_live_facts_counted` (def).
- `audit_live_fact_event_work` (def).
- `audit_live_facts_work` (def).
- `audit_live_fact_event_budget` (def).
- `audit_live_facts_adapted_statement` (def).

Future proof module: `AnalysesAuditSsaFactsAdequacy`.

- `audit_live_facts_adapted_holds`: `AnalysesAuditSsaFacts.audit_live_facts_adapted_statement`;
  owner AUD-SQ-PREP.

## AnalysesAuditSsaGeneral

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_predicate_code` (def).
- `audit_live_predicate_arity` (def).
- `audit_live_predicate_source` (def).
- `audit_live_predicate_source_statement` (def).
- `audit_live_general_source_adapted_statement` (def).
- `audit_live_general_contract_statement` (def).

Future proof module: `AnalysesAuditSsaGeneralAdequacy`.

- `audit_live_predicate_source_holds`:
  `AnalysesAuditSsaGeneral.audit_live_predicate_source_statement`; owner AUD-SQ-PREP.
- `audit_live_general_source_adapted_holds`:
  `AnalysesAuditSsaGeneral.audit_live_general_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_live_general_contract_holds`:
  `AnalysesAuditSsaGeneral.audit_live_general_contract_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaOneShot

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_one_callbacks` (rec).
- `live_one_node_encode` (proj).
- `live_one_value_encode` (proj).
- `live_one_out` (proj).
- `live_one_target` (proj).
- `live_one_def` (proj).
- `live_one_exit` (proj).
- `live_one_use` (proj).
- `audit_live_one_event` (ind).
- `LiveOneCase` (constr).
- `LiveOneNode` (constr).
- `LiveOneValue` (constr).
- `LiveOneOut` (constr).
- `LiveOneTarget` (constr).
- `LiveOneDef` (constr).
- `LiveOneExit` (constr).
- `LiveOneUse` (constr).
- `LiveOneEqual` (constr).
- `audit_live_one_has` (Fixpoint).
- `audit_live_one_filter` (Fixpoint).
- `audit_live_one_surviving_out` (def).
- `audit_live_one_edge_uses` (Fixpoint).
- `audit_live_one_use_at` (def).
- `audit_live_one_search_uses` (Fixpoint).
- `audit_live_one_node` (def).
- `audit_live_one_target` (def).
- `audit_live_one_counted` (def).
- `audit_live_one_event_work` (def).
- `audit_live_one_event_budget` (def).
- `audit_live_one_input_scale` (def).
- `audit_live_one_input_budget` (def).
- `audit_live_one_callbacks_erase` (def).
- `audit_live_one_source_adapted_statement` (def).
- `AuditLiveOneCallbacks` (record-constructor).

Future proof module: `AnalysesAuditSsaOneShotAdequacy`.

- `audit_live_one_source_adapted_holds`:
  `AnalysesAuditSsaOneShot.audit_live_one_source_adapted_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaPortfolio

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_sparse_query_adapted_statement` (def).
- `audit_live_portfolio_choice_source` (def).
- `audit_live_portfolio_contract_statement` (def).

Future proof module: `AnalysesAuditSsaPortfolioAdequacy`.

- `audit_live_sparse_query_adapted_holds`:
  `AnalysesAuditSsaPortfolio.audit_live_sparse_query_adapted_statement`; owner AUD-SQ-PREP.
- `audit_live_portfolio_contract_holds`:
  `AnalysesAuditSsaPortfolio.audit_live_portfolio_contract_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaPrepared

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_sq_prepare_graph_callbacks` (def).
- `audit_sq_prepared_source_statement` (def).
- `audit_sq_prepared_contract_statement` (def).

Future proof module: `AnalysesAuditSsaPreparedAdequacy`.

- `audit_sq_prepared_source_holds`: `AnalysesAuditSsaPrepared.audit_sq_prepared_source_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_prepared_contract_holds`:
  `AnalysesAuditSsaPrepared.audit_sq_prepared_contract_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaQuery

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_sq_values_call` (ind).
- `AuditSqValuesCase` (constr).
- `AuditSqValuesPrepare` (constr).
- `AuditSqValuesDfs` (constr).
- `AuditSqExit` (constr).
- `AuditSqOut` (constr).
- `AuditSqEdgeUse` (constr).
- `AuditSqUseGet` (constr).
- `AuditSqUseAdd` (constr).
- `AuditSqUseSet` (constr).
- `AuditSqUsesElements` (constr).
- `AuditSqDefinitionCall` (constr).
- `AuditSqDefinitionSet` (constr).
- `AuditSqValuesOutput` (constr).
- `audit_sq_flat_uses` (Fixpoint).
- `audit_sq_point_uses` (def).
- `audit_sq_add_uses` (Fixpoint).
- `audit_sq_uses_counted` (Fixpoint).
- `audit_sq_defs_counted` (Fixpoint).
- `audit_sq_values_counted` (def).
- `audit_sq_values_event_work` (def).
- `audit_sq_values_model_work` (def).
- `audit_sq_values_input_rows` (def).
- `audit_sq_values_input_list` (def).
- `audit_sq_values_input_event_bound` (def).
- `audit_sq_values_input_width` (def).
- `audit_sq_values_input_budget` (def).
- `audit_sq_values_counted_statement` (def).
- `audit_sq_reduced_call` (ind).
- `AuditSqReducedCase` (constr).
- `AuditSqReducedTarget` (constr).
- `AuditSqReducedSource` (constr).
- `AuditSqReducedDom` (constr).
- `AuditSqReducedOut` (constr).
- `AuditSqReducedGet` (constr).
- `AuditSqReducedAdd` (constr).
- `AuditSqReducedUnion` (constr).
- `AuditSqReducedSet` (constr).
- `audit_sq_back_counted` (def).
- `audit_sq_r_edges_counted` (Fixpoint).
- `audit_sq_r_rows_counted` (Fixpoint).
- `audit_sq_reduced_event_work` (def).
- `audit_sq_reduced_work` (def).
- `audit_sq_reduced_input_edges` (def).
- `audit_sq_reduced_width` (def).
- `audit_sq_reduced_event_bound` (def).
- `audit_sq_reduced_budget` (def).
- `audit_sq_reduced_statement` (def).
- `audit_sq_t_call` (ind).
- `AuditSqTCase` (constr).
- `AuditSqTReduced` (constr).
- `AuditSqTGet` (constr).
- `AuditSqTOut` (constr).
- `AuditSqTElements` (constr).
- `AuditSqTTarget` (constr).
- `AuditSqTMember` (constr).
- `AuditSqTAdd` (constr).
- `AuditSqTSet` (constr).
- `AuditSqTOutput` (constr).
- `audit_sq_t_filter` (Fixpoint).
- `audit_sq_t_targets` (Fixpoint).
- `audit_sq_t_vertices` (Fixpoint).
- `audit_sq_t_set_counted` (Fixpoint).
- `audit_sq_t_edges_counted` (def).
- `audit_sq_t_rows_counted` (Fixpoint).
- `audit_sq_t_graph_with_rows` (def).
- `audit_sq_t_graph_counted` (def).
- `audit_sq_t_event_work` (def).
- `audit_sq_t_work` (def).
- `audit_sq_t_input_vertices` (def).
- `audit_sq_t_input_scale` (def).
- `audit_sq_t_event_bound` (def).
- `audit_sq_t_budget` (def).
- `audit_sq_t_graph_statement` (def).
- `audit_sq_tbody` (ind).
- `AuditSqTBodyOut` (constr).
- `AuditSqTBodyTarget` (constr).
- `AuditSqTBodyEncode` (constr).
- `audit_sq_tbody_out` (def).
- `audit_sq_tbody_target` (def).
- `audit_sq_tbody_encode` (def).
- `audit_sq_t_prepare_callbacks` (def).
- `audit_sq_t_dfs_callbacks` (def).
- `audit_sq_tclosure_call` (ind).
- `AuditSqTCClosureCase` (constr).
- `AuditSqTCClosureDfs` (constr).
- `AuditSqTCClosureAdd` (constr).
- `AuditSqTCClosureSet` (constr).
- `audit_sq_tclosure_set` (Fixpoint).
- `audit_sq_tclosure_rows` (Fixpoint).
- `audit_sq_tbody_work` (def).
- `audit_sq_tclosure_event_work` (def).
- `audit_sq_tclosure_work` (def).
- `audit_sq_tclosure_event_bound` (def).
- `audit_sq_tclosure_budget` (def).
- `audit_sq_tclosure_statement` (def).
- `audit_sq_graph_trace` (rec).
- `audit_sq_graph_prepare_events` (proj).
- `audit_sq_graph_initial_dfs_events` (proj).
- `audit_sq_graph_reduced_events` (proj).
- `audit_sq_graph_t_events` (proj).
- `audit_sq_graph_t_prepare_events` (proj).
- `audit_sq_graph_dom_events` (proj).
- `audit_sq_graph_closure_events` (proj).
- `audit_sq_graph_run` (def).
- `audit_sq_graph_erasure_statement` (def).
- `audit_sq_dom_call` (ind).
- `AuditSqDomGet` (constr).
- `AuditSqDomLe` (constr).
- `audit_sq_dom_counted` (def).
- `audit_sq_query_call` (ind).
- `AuditSqDefinition` (constr).
- `AuditSqUses` (constr).
- `AuditSqClosure` (constr).
- `AuditSqCompare` (constr).
- `AuditSqDominates` (constr).
- `AuditSqReduced` (constr).
- `AuditSqMember` (constr).
- `audit_sq_members_counted` (Fixpoint).
- `audit_sq_rows_counted` (Fixpoint).
- `audit_sq_query_counted` (def).
- `audit_sq_dom_event_work` (def).
- `audit_sq_query_event_work` (def).
- `audit_sq_query_model_work` (def).
- `audit_sq_query_event_bound` (def).
- `audit_sq_query_input_width` (def).
- `audit_sq_query_input_budget` (def).
- `audit_sq_dom_counted_statement` (def).
- `audit_sq_query_counted_statement` (def).
- `AuditSqGraphTrace` (record-constructor).

Future proof module: `AnalysesAuditSsaQueryAdequacy`.

- `audit_sq_values_counted_correct`: `AnalysesAuditSsaQuery.audit_sq_values_counted_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_reduced_correct`: `AnalysesAuditSsaQuery.audit_sq_reduced_statement`; owner AUD-SQ-PREP.
- `audit_sq_t_graph_correct`: `AnalysesAuditSsaQuery.audit_sq_t_graph_statement`; owner AUD-SQ-PREP.
- `audit_sq_tclosure_correct`: `AnalysesAuditSsaQuery.audit_sq_tclosure_statement`; owner
  AUD-SQ-PREP.
- `audit_sq_graph_erasure`: `AnalysesAuditSsaQuery.audit_sq_graph_erasure_statement`; owner
  AUD-SQ-PREP.
- `audit_sq_dom_counted_correct`: `AnalysesAuditSsaQuery.audit_sq_dom_counted_statement`; owner
  AUD-SQ-PREP.
- `audit_sq_query_counted_correct`: `AnalysesAuditSsaQuery.audit_sq_query_counted_statement`; owner
  AUD-SQ-PREP.

## AnalysesAuditSsaQueryBase

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_list_has` (def).
- `audit_live_surviving_graph` (def).
- `audit_live_use_at` (def).
- `audit_live_one_shot` (def).
- `audit_live_one_shot_exact_statement` (def).
- `audit_live_values_from_graph` (def).
- `audit_live_values_reuse_statement` (def).
- `audit_live_values_refresh_statement` (def).
- `audit_live_refresh_query_exact_statement` (def).
- `audit_live_prepared` (rec).
- `audit_live_graph_index` (proj).
- `audit_live_value_index` (proj).
- `audit_live_prepare` (def).
- `audit_live_prepared_query` (def).
- `audit_live_prepared_agrees_statement` (def).
- `audit_live_prepared_batch` (def).
- `audit_live_prepared_batch_statement` (def).
- `audit_live_use_occurrences` (def).
- `audit_live_occurrence_count_statement` (def).
- `audit_live_choice` (ind).
- `AuditLiveGeneral` (constr).
- `AuditLiveOneShot` (constr).
- `AuditLivePrepared` (constr).
- `AuditLiveSparse` (constr).
- `audit_live_select` (def).
- `audit_live_select_exact_statement` (def).
- `audit_live_all_points_agrees_statement` (def).
- `audit_live_all_points_three_statement` (def).
- `audit_universe_nodup` (def).
- `audit_dense_available` (def).
- `audit_dense_busy` (def).
- `audit_dense_least_statement` (def).
- `audit_dense_seg_agrees_statement` (def).
- `audit_seg_direction` (ind).
- `AuditAvailable` (constr).
- `AuditBusy` (constr).
- `audit_seg_choice` (ind).
- `AuditSparse` (constr).
- `AuditDense` (constr).
- `audit_seg_dense_query` (def).
- `audit_seg_select` (def).
- `audit_seg_choice_agrees_statement` (def).
- `liveness_portfolio_agrees` (def).
- `seg_portfolio_agrees` (def).
- `AuditLiveIndexes` (record-constructor).

Future proof module: `AnalysesAuditSsaQueryBaseAdequacy`.

- `audit_live_one_shot_exact_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_one_shot_exact_statement`; owner AUD-SQ-BASE.
- `audit_live_values_reuse_holds`: `AnalysesAuditSsaQueryBase.audit_live_values_reuse_statement`;
  owner AUD-SQ-BASE.
- `audit_live_values_refresh_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_values_refresh_statement`; owner AUD-SQ-BASE.
- `audit_live_refresh_query_exact_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_refresh_query_exact_statement`; owner AUD-SQ-BASE.
- `audit_live_prepared_agrees_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_prepared_agrees_statement`; owner AUD-SQ-BASE.
- `audit_live_prepared_batch_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_prepared_batch_statement`; owner AUD-SQ-BASE.
- `audit_live_occurrence_count_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_occurrence_count_statement`; owner AUD-SQ-BASE.
- `audit_live_select_exact_holds`: `AnalysesAuditSsaQueryBase.audit_live_select_exact_statement`;
  owner AUD-SQ-BASE.
- `audit_live_all_points_agrees_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_all_points_agrees_statement`; owner AUD-SQ-BASE.
- `audit_live_all_points_three_holds`:
  `AnalysesAuditSsaQueryBase.audit_live_all_points_three_statement`; owner AUD-SQ-BASE.
- `audit_dense_least_holds`: `AnalysesAuditSsaQueryBase.audit_dense_least_statement`; owner
  AUD-SQ-BASE.
- `audit_dense_seg_agrees_holds`: `AnalysesAuditSsaQueryBase.audit_dense_seg_agrees_statement`;
  owner AUD-SQ-BASE.
- `audit_seg_choice_agrees_holds`: `AnalysesAuditSsaQueryBase.audit_seg_choice_agrees_statement`;
  owner AUD-SQ-BASE.
- `liveness_portfolio_agrees_holds`: `AnalysesAuditSsaQueryBase.liveness_portfolio_agrees`; owner
  AUD-SQ-BASE.
- `seg_portfolio_agrees_holds`: `AnalysesAuditSsaQueryBase.seg_portfolio_agrees`; owner AUD-SQ-BASE.

## AnalysesAuditSsaQueryGraph

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_sq_graph_prepare_callbacks` (def).
- `audit_sq_graph_dfs_callbacks` (def).
- `audit_sq_graph_input_scale` (def).
- `audit_sq_graph_input_budget` (def).
- `audit_sq_graph_virtual_call_budget` (def).
- `audit_sq_graph_erase_budget` (def).
- `audit_sq_graph_dom_body_budget` (def).
- `audit_sq_graph_dom_budget` (def).
- `audit_sq_graph_full_source_statement` (def).
- `audit_sq_graph_full_source_contract_statement` (def).

Future proof module: `AnalysesAuditSsaQueryGraphAdequacy`.

- `audit_sq_graph_full_source_holds`:
  `AnalysesAuditSsaQueryGraph.audit_sq_graph_full_source_statement`; owner AUD-SQ-PREP.
- `audit_sq_graph_full_source_contract_holds`:
  `AnalysesAuditSsaQueryGraph.audit_sq_graph_full_source_contract_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaQuerySource

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_sq_query_source_event` (ind).
- `SqQueryCase` (constr).
- `SqQueryDef` (constr).
- `SqQueryUses` (constr).
- `SqQueryRows` (constr).
- `SqQueryElements` (constr).
- `SqQueryEncode` (constr).
- `SqQueryEqual` (constr).
- `SqQueryDom` (constr).
- `SqQueryMem` (constr).
- `audit_sq_query_source_members` (Fixpoint).
- `audit_sq_query_source_rows` (Fixpoint).
- `audit_sq_query_source_counted` (def).
- `audit_sq_query_source_event_work` (def).
- `audit_sq_query_source_event_external` (def).
- `audit_sq_query_source_work` (def).
- `audit_sq_query_source_external` (def).
- `audit_sq_query_source_input_scale` (def).
- `audit_sq_query_source_input_budget` (def).
- `audit_sq_query_source_statement` (def).
- `audit_sq_query_source_event_budget` (def).
- `audit_sq_query_source_adapted_statement` (def).
- `audit_sq_query_source_contract_statement` (def).
- `audit_sq_values_callbacks` (rec).
- `sq_values_node_encode` (proj).
- `sq_values_value_encode` (proj).
- `sq_values_out` (proj).
- `sq_values_target` (proj).
- `sq_values_exit` (proj).
- `sq_values_edge` (proj).
- `sq_values_home` (proj).
- `audit_sq_values_source_event` (ind).
- `SqValuesCase` (constr).
- `SqValuesPrepare` (constr).
- `SqValuesDfs` (constr).
- `SqValuesOut` (constr).
- `SqValuesExit` (constr).
- `SqValuesEdge` (constr).
- `SqValuesHome` (constr).
- `SqValuesUseMap` (constr).
- `SqValuesDefMap` (constr).
- `SqValuesSet` (constr).
- `SqValuesElements` (constr).
- `SqValuesOutput` (constr).
- `audit_sq_values_source_edges` (Fixpoint).
- `audit_sq_values_source_point` (def).
- `audit_sq_values_source_add` (Fixpoint).
- `audit_sq_values_source_uses` (Fixpoint).
- `audit_sq_values_source_defs` (Fixpoint).
- `audit_sq_values_source_counted` (def).
- `audit_sq_values_callbacks_erase` (def).
- `audit_sq_values_source_event_work` (def).
- `audit_sq_values_source_event_external` (def).
- `audit_sq_values_source_work` (def).
- `audit_sq_values_source_external` (def).
- `audit_sq_values_input_nodes` (def).
- `audit_sq_values_source_input_scale` (def).
- `audit_sq_values_source_input_budget` (def).
- `audit_sq_values_source_statement` (def).
- `audit_sq_values_capture_budget` (def).
- `audit_sq_values_source_event_budget` (def).
- `audit_sq_values_source_adapted_statement` (def).
- `audit_sq_values_source_contract_statement` (def).
- `audit_sq_reduced_source_event` (ind).
- `SqReducedCase` (constr).
- `SqReducedTarget` (constr).
- `SqReducedSource` (constr).
- `SqReducedDom` (constr).
- `SqReducedEdges` (constr).
- `SqReducedRows` (constr).
- `SqReducedSet` (constr).
- `SqReducedUnion` (constr).
- `audit_sq_reduced_source_back` (def).
- `audit_sq_reduced_source_edges` (Fixpoint).
- `audit_sq_reduced_source_rows` (Fixpoint).
- `audit_sq_reduced_source_event_work` (def).
- `audit_sq_reduced_source_event_external` (def).
- `audit_sq_reduced_source_work` (def).
- `audit_sq_reduced_source_external` (def).
- `audit_sq_reduced_source_budget` (def).
- `audit_sq_reduced_source_statement` (def).
- `audit_sq_reduced_source_event_budget` (def).
- `audit_sq_reduced_source_adapted_statement` (def).
- `audit_sq_reduced_source_contract_statement` (def).
- `audit_sq_t_source_event` (ind).
- `SqTCase` (constr).
- `SqTReduced` (constr).
- `SqTSetMap` (constr).
- `SqTOutMap` (constr).
- `SqTRowMap` (constr).
- `SqTElements` (constr).
- `SqTTarget` (constr).
- `SqTSet` (constr).
- `SqTOutput` (constr).
- `audit_sq_t_source_filter` (Fixpoint).
- `audit_sq_t_source_targets` (Fixpoint).
- `audit_sq_t_source_vertices` (Fixpoint).
- `audit_sq_t_source_edges` (def).
- `audit_sq_t_source_rows` (Fixpoint).
- `audit_sq_t_source_counted` (def).
- `audit_sq_t_source_event_work` (def).
- `audit_sq_t_source_event_external` (def).
- `audit_sq_t_source_work` (def).
- `audit_sq_t_source_external` (def).
- `audit_sq_t_source_input_scale` (def).
- `audit_sq_t_source_budget` (def).
- `audit_sq_t_source_statement` (def).
- `audit_sq_t_source_event_budget` (def).
- `audit_sq_t_source_adapted_statement` (def).
- `audit_sq_t_source_contract_statement` (def).
- `audit_sq_t_internal` (ind).
- `SqTInternalMap` (constr).
- `SqTInternalTarget` (constr).
- `SqTInternalEncode` (constr).
- `audit_sq_t_internal_out` (def).
- `audit_sq_t_internal_target` (def).
- `audit_sq_t_internal_encode` (def).
- `audit_sq_t_internal_prepare_callbacks` (def).
- `audit_sq_t_internal_dfs_callbacks` (def).
- `audit_sq_closure_source_event` (ind).
- `SqClosureCase` (constr).
- `SqClosureDfs` (constr).
- `SqClosureSet` (constr).
- `SqClosureRow` (constr).
- `audit_sq_closure_source_rows` (Fixpoint).
- `audit_sq_t_internal_work` (def).
- `audit_sq_t_internal_external` (def).
- `audit_sq_closure_source_event_work` (def).
- `audit_sq_closure_source_event_external` (def).
- `audit_sq_closure_source_work` (def).
- `audit_sq_closure_source_external` (def).
- `audit_sq_closure_source_budget` (def).
- `audit_sq_closure_source_statement` (def).
- `audit_sq_t_internal_budget` (def).
- `audit_sq_closure_source_event_budget` (def).
- `audit_sq_closure_source_adapted_statement` (def).
- `audit_sq_closure_source_contract_statement` (def).
- `SqValuesCallbacks` (record-constructor).

Future proof module: `AnalysesAuditSsaQuerySourceAdequacy`.

- `audit_sq_query_source_holds`: `AnalysesAuditSsaQuerySource.audit_sq_query_source_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_query_source_adapted_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_query_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_query_source_contract_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_query_source_contract_statement`; owner AUD-SQ-PREP.
- `audit_sq_values_source_holds`: `AnalysesAuditSsaQuerySource.audit_sq_values_source_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_values_source_adapted_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_values_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_values_source_contract_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_values_source_contract_statement`; owner AUD-SQ-PREP.
- `audit_sq_reduced_source_holds`: `AnalysesAuditSsaQuerySource.audit_sq_reduced_source_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_reduced_source_adapted_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_reduced_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_reduced_source_contract_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_reduced_source_contract_statement`; owner AUD-SQ-PREP.
- `audit_sq_t_source_holds`: `AnalysesAuditSsaQuerySource.audit_sq_t_source_statement`; owner
  AUD-SQ-PREP.
- `audit_sq_t_source_adapted_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_t_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_t_source_contract_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_t_source_contract_statement`; owner AUD-SQ-PREP.
- `audit_sq_closure_source_holds`: `AnalysesAuditSsaQuerySource.audit_sq_closure_source_statement`;
  owner AUD-SQ-PREP.
- `audit_sq_closure_source_adapted_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_closure_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_closure_source_contract_holds`:
  `AnalysesAuditSsaQuerySource.audit_sq_closure_source_contract_statement`; owner AUD-SQ-PREP.

## AnalysesAuditSsaReuse

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_sq_reuse_values_counted` (def).
- `audit_sq_reuse_values_adapted_statement` (def).
- `audit_sq_batch_counted` (Fixpoint).
- `audit_sq_batch_input_budget` (def).
- `audit_sq_batch_adapted_statement` (def).
- `audit_sq_reuse_contract_statement` (def).

Future proof module: `AnalysesAuditSsaReuseAdequacy`.

- `audit_sq_reuse_values_adapted_holds`:
  `AnalysesAuditSsaReuse.audit_sq_reuse_values_adapted_statement`; owner AUD-SQ-PREP.
- `audit_sq_batch_adapted_holds`: `AnalysesAuditSsaReuse.audit_sq_batch_adapted_statement`; owner
  AUD-SQ-PREP.
- `audit_sq_reuse_contract_holds`: `AnalysesAuditSsaReuse.audit_sq_reuse_contract_statement`; owner
  AUD-SQ-PREP.

## AnalysesAuditSsaSparse

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_sparse_callbacks` (rec).
- `sl_node_encode` (proj).
- `sl_edge_encode` (proj).
- `sl_value_encode` (proj).
- `sl_out` (proj).
- `sl_target` (proj).
- `sl_source` (proj).
- `sl_def` (proj).
- `sl_exit` (proj).
- `sl_use` (proj).
- `audit_live_sparse_event` (ind).
- `SlCase` (constr).
- `SlList` (constr).
- `SlOut` (constr).
- `SlSource` (constr).
- `SlDef` (constr).
- `SlExit` (constr).
- `SlUse` (constr).
- `SlPred` (constr).
- `SlRows` (constr).
- `SlDefs` (constr).
- `SlSet` (constr).
- `SlEncodeNat` (constr).
- `SlMultiply` (constr).
- `SlAdd` (constr).
- `audit_live_sparse_mul` (Fixpoint).
- `audit_live_sparse_mul_statement` (def).
- `audit_live_sparse_edges` (Fixpoint).
- `audit_live_sparse_uses` (Fixpoint).
- `audit_live_sparse_seeds` (Fixpoint).
- `audit_live_sparse_defs` (Fixpoint).
- `audit_live_sparse_state` (def).
- `audit_live_sparse_add` (def).
- `audit_live_sparse_adds` (Fixpoint).
- `audit_live_sparse_filter_edges` (Fixpoint).
- `audit_live_sparse_back_sources` (Fixpoint).
- `audit_live_sparse_step` (def).
- `audit_live_sparse_run` (Fixpoint).
- `audit_live_sparse_counted` (def).
- `audit_live_sparse_event_work` (def).
- `audit_live_sparse_work` (def).
- `audit_live_sparse_event_budget` (def).
- `audit_live_sparse_input_scale` (def).
- `audit_live_sparse_input_budget` (def).
- `audit_live_sparse_callbacks_erase` (def).
- `audit_live_sparse_source_adapted_statement` (def).
- `audit_live_sparse_probe` (def).
- `audit_live_sparse_probe_statement` (def).
- `AuditLiveSparseCallbacks` (record-constructor).

Future proof module: `AnalysesAuditSsaSparseAdequacy`.

- `audit_live_sparse_mul_holds`: `AnalysesAuditSsaSparse.audit_live_sparse_mul_statement`; owner
  AUD-SQ-PREP.
- `audit_live_sparse_source_adapted_holds`:
  `AnalysesAuditSsaSparse.audit_live_sparse_source_adapted_statement`; owner AUD-SQ-PREP.
- `audit_live_sparse_probe_holds`: `AnalysesAuditSsaSparse.audit_live_sparse_probe_statement`; owner
  AUD-SQ-PREP.

## AnalysesAuditSsaTabulate

Public package: `Galois.Analyses`.

Card: AUD-SQ-MODELS

- `audit_live_tab_event` (ind).
- `LiveTabCase` (constr).
- `LiveTabList` (constr).
- `LiveTabSparse` (constr).
- `LiveTabSet` (constr).
- `LiveTabElements` (constr).
- `LiveTabRows` (constr).
- `LiveTabDb` (constr).
- `LiveTabTuple` (constr).
- `LiveTabNode` (constr).
- `LiveTabValue` (constr).
- `audit_live_tab_edge_values` (Fixpoint).
- `audit_live_tab_exits` (Fixpoint).
- `audit_live_tab_universe` (def).
- `audit_live_tab_db_holds` (def).
- `audit_live_tab_filter_db` (Fixpoint).
- `audit_live_tab_filter_set` (Fixpoint).
- `audit_live_tab_node` (def).
- `audit_live_tab_nodes` (Fixpoint).
- `audit_live_tab_probe` (def).
- `audit_live_tab_event_work` (def).
- `audit_live_tab_work` (def).
- `audit_live_tab_event_budget` (def).
- `audit_live_tab_input_scale` (def).
- `audit_live_tab_input_budget` (def).
- `audit_live_tab_adapted_statement` (def).

Future proof module: `AnalysesAuditSsaTabulateAdequacy`.

- `audit_live_tab_adapted_holds`: `AnalysesAuditSsaTabulate.audit_live_tab_adapted_statement`; owner
  AUD-SQ-PREP.

## CollectionsAuditNAdd

Public package: `Galois.Collections`.

Card: AUD-GR-MODELS

- `audit_idf_nadd_event` (ind).
- `IdfNaddFrame` (constr).
- `IdfNaddSucc` (constr).
- `IdfNaddZero` (constr).
- `audit_idf_positive_add` (Fixpoint).
- `audit_idf_nadd_counted` (def).
- `audit_idf_nadd_width` (def).
- `audit_idf_nadd_budget` (def).
- `audit_idf_nadd_source_statement` (def).

Future proof module: `CollectionsAuditNAddAdequacy`.

- `audit_idf_nadd_source_holds`: `CollectionsAuditNAdd.audit_idf_nadd_source_statement`; owner
  AUD-GR-IDF.

## CollectionsAuditPositiveSub

Public package: `Galois.Collections`.

Card: AUD-GR-MODELS

- `audit_idf_sub_event` (ind).
- `IdfSubFrame` (constr).
- `IdfSubPredFrame` (constr).
- `IdfSubFinish` (constr).
- `audit_idf_pred_double` (Fixpoint).
- `audit_idf_double_pred` (def).
- `audit_idf_sub_mask` (Fixpoint).
- `audit_idf_sub_counted` (def).
- `audit_idf_sub_budget` (def).
- `audit_idf_sub_source_statement` (def).

Future proof module: `CollectionsAuditPositiveSubAdequacy`.

- `audit_idf_sub_source_holds`: `CollectionsAuditPositiveSub.audit_idf_sub_source_statement`; owner
  AUD-GR-IDF.

## CollectionsAuditQueue

Public package: `Galois.Collections`.

Card: AUD-GR-MODELS

- `queue_event` (ind).
- `QInsertSlot` (constr).
- `QMeldSlot` (constr).
- `QSelectSlot` (constr).
- `QLink` (constr).
- `QEntryCompare` (constr).
- `QPriorityLt` (constr).
- `QPriorityEq` (constr).
- `QGet` (constr).
- `QSet` (constr).
- `QRemove` (constr).
- `QEncode` (constr).
- `QChildren` (constr).
- `QExamined` (constr).
- `QStale` (constr).
- `QAccepted` (constr).
- `QFuelStep` (constr).
- `queue_link` (def).
- `queue_insert` (Fixpoint).
- `queue_meld` (Fixpoint).
- `queue_select` (Fixpoint).
- `queue_remove_min` (def).
- `queue_push` (def).
- `queue_pop_fuel` (Fixpoint).
- `queue_pop` (def).
- `queue_push_execution` (ind).
- `QueuePushNew` (constr).
- `QueuePushLower` (constr).
- `QueuePushUnchanged` (constr).
- `queue_pop_fuel_execution` (ind).
- `QueuePopZero` (constr).
- `QueuePopEmpty` (constr).
- `QueuePopAccepted` (constr).
- `QueuePopStale` (constr).
- `QueuePopMissing` (constr).
- `queue_outer_execution_statement` (def).
- `queue_projection_laws` (def).
- `queue_event_keys` (def).
- `queue_key_calls` (def).
- `queue_key_bits` (def).
- `queue_entry_compare_args` (def).
- `queue_comparisons` (def).
- `queue_compare_calls` (def).
- `queue_compare_operand_bits` (def).
- `queue_child_cells` (def).
- `queue_child_calls` (def).
- `queue_stale_count` (def).
- `queue_examined_count` (def).
- `queue_remove_nodes` (Fixpoint).
- `queue_trie_visits` (def).
- `queue_trie_nodes` (def).
- `queue_total_trie_visits` (def).
- `queue_total_trie_nodes` (def).
- `queue_slot_steps` (def).
- `queue_link_count` (def).
- `queue_fuel_steps` (def).
- `queue_comparison_model` (def).
- `queue_event_primitive_model` (def).
- `queue_model_budget` (def).
- `queue_model_work` (def).
- `queue_model_equation_statement` (def).
- `queue_insert_counted_statement` (def).
- `queue_select_counted_statement` (def).
- `queue_meld_counted_statement` (def).
- `queue_remove_min_counted_statement` (def).
- `queue_pop_fuel_counted_statement` (def).
- `queue_push_counted_statement` (def).
- `queue_pop_counted_statement` (def).
- `queue_zero_fuel_is_charged` (Example).
- `queue_strict_comparison_all_operands` (Example).
- `audit_queue_input_width` (def).
- `audit_queue_input_scale` (def).
- `audit_queue_input_event_bound` (def).
- `audit_queue_input_budget` (def).
- `audit_queue_push_input_statement` (def).
- `audit_queue_pop_fuel_input_statement` (def).
- `audit_queue_pop_input_statement` (def).
- `audit_queue_encoder_model` (def).
- `audit_queue_encoder_erases` (def).
- `audit_queue_nested_event` (def).
- `audit_queue_push_nested` (def).
- `audit_queue_pop_fuel_nested` (Fixpoint).
- `audit_queue_pop_nested` (def).
- `audit_queue_nested_body_work` (def).
- `audit_queue_nested_total_work` (def).
- `audit_queue_push_nested_statement` (def).
- `audit_queue_pop_fuel_nested_statement` (def).
- `audit_queue_pop_nested_statement` (def).
- `audit_queue_capture_encoder` (def).
- `audit_queue_recorded_push` (def).
- `audit_queue_recorded_pop` (def).
- `audit_queue_recorded_pop_fuel` (def).
- `audit_queue_recorded_body_work` (def).
- `audit_queue_recorded_codes` (def).
- `audit_queue_recorded_statement` (def).
- `audit_queue_family_statement` (def).
- `audit_queue_ltb_source_work` (def).
- `audit_queue_leb_source_work` (def).
- `audit_queue_eq_source_work` (def).
- `audit_queue_recorded_source_event` (def).
- `audit_queue_recorded_internal_source_work` (def).
- `audit_queue_recorded_full_source_work` (def).
- `audit_queue_full_input_budget` (def).
- `audit_queue_recorded_full_push_statement` (def).
- `audit_queue_recorded_full_pop_statement` (def).
- `audit_queue_recorded_full_pop_fuel_statement` (def).
- `audit_queue_full_source_contract_statement` (def).
- `audit_queue_external_encoder_adapter` (rec).
- `audit_queue_external_encoder_value` (proj).
- `audit_queue_external_encoder_source` (proj).
- `audit_queue_recorded_encoder_budget_event` (def).
- `audit_queue_recorded_encoder_budget` (def).
- `audit_queue_external_encoder_push_statement` (def).
- `audit_queue_external_encoder_pop_statement` (def).
- `audit_queue_external_encoder_pop_fuel_statement` (def).

Future proof module: `CollectionsAuditQueueAdequacy`.

- `queue_outer_execution_holds`: `CollectionsAuditQueue.queue_outer_execution_statement`; owner
  AUD-GR-QUEUE.
- `queue_model_equation_holds`: `CollectionsAuditQueue.queue_model_equation_statement`; owner
  AUD-GR-QUEUE.
- `queue_insert_counted_holds`: `CollectionsAuditQueue.queue_insert_counted_statement`; owner
  AUD-GR-QUEUE.
- `queue_select_counted_holds`: `CollectionsAuditQueue.queue_select_counted_statement`; owner
  AUD-GR-QUEUE.
- `queue_meld_counted_holds`: `CollectionsAuditQueue.queue_meld_counted_statement`; owner
  AUD-GR-QUEUE.
- `queue_remove_min_counted_holds`: `CollectionsAuditQueue.queue_remove_min_counted_statement`;
  owner AUD-GR-QUEUE.
- `queue_pop_fuel_counted_holds`: `CollectionsAuditQueue.queue_pop_fuel_counted_statement`; owner
  AUD-GR-QUEUE.
- `queue_push_counted_holds`: `CollectionsAuditQueue.queue_push_counted_statement`; owner
  AUD-GR-QUEUE.
- `queue_pop_counted_holds`: `CollectionsAuditQueue.queue_pop_counted_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_push_input_holds`: `CollectionsAuditQueue.audit_queue_push_input_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_pop_fuel_input_holds`: `CollectionsAuditQueue.audit_queue_pop_fuel_input_statement`;
  owner AUD-GR-QUEUE.
- `audit_queue_pop_input_holds`: `CollectionsAuditQueue.audit_queue_pop_input_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_push_nested_holds`: `CollectionsAuditQueue.audit_queue_push_nested_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_pop_fuel_nested_holds`:
  `CollectionsAuditQueue.audit_queue_pop_fuel_nested_statement`; owner AUD-GR-QUEUE.
- `audit_queue_pop_nested_holds`: `CollectionsAuditQueue.audit_queue_pop_nested_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_recorded_holds`: `CollectionsAuditQueue.audit_queue_recorded_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_family_holds`: `CollectionsAuditQueue.audit_queue_family_statement`; owner
  AUD-GR-QUEUE.
- `audit_queue_recorded_full_push_correct`:
  `CollectionsAuditQueue.audit_queue_recorded_full_push_statement`; owner AUD-GR-QUEUE.
- `audit_queue_recorded_full_pop_correct`:
  `CollectionsAuditQueue.audit_queue_recorded_full_pop_statement`; owner AUD-GR-QUEUE.
- `audit_queue_recorded_full_pop_fuel_correct`:
  `CollectionsAuditQueue.audit_queue_recorded_full_pop_fuel_statement`; owner AUD-GR-QUEUE.
- `audit_queue_full_source_contract`:
  `CollectionsAuditQueue.audit_queue_full_source_contract_statement`; owner AUD-GR-QUEUE.
- `audit_queue_external_encoder_push_correct`:
  `CollectionsAuditQueue.audit_queue_external_encoder_push_statement`; owner AUD-GR-QUEUE.
- `audit_queue_external_encoder_pop_correct`:
  `CollectionsAuditQueue.audit_queue_external_encoder_pop_statement`; owner AUD-GR-QUEUE.
- `audit_queue_external_encoder_pop_fuel_correct`:
  `CollectionsAuditQueue.audit_queue_external_encoder_pop_fuel_statement`; owner AUD-GR-QUEUE.

## GraphAuditBase

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_graph_prepare_map_site` (ind).
- `AuditGraphOutSet` (constr).
- `AuditGraphIncomingGet` (constr).
- `AuditGraphIncomingSet` (constr).
- `audit_graph_prepare_call` (ind).
- `AuditPrepareOutCall` (constr).
- `AuditPrepareTargetCall` (constr).
- `AuditPrepareEncodeCall` (constr).
- `audit_graph_prepare_calls` (def).
- `audit_graph_prepare_callback_count` (def).
- `audit_graph_prepare_out_execution` (ind).
- `AuditGraphOutNil` (constr).
- `AuditGraphOutCons` (constr).
- `audit_graph_prepare_edges_execution` (ind).
- `AuditGraphEdgesNil` (constr).
- `AuditGraphEdgesCons` (constr).
- `audit_graph_prepare_in_execution` (ind).
- `AuditGraphInNil` (constr).
- `AuditGraphInCons` (constr).
- `audit_graph_prepare_execution` (ind).
- `AuditGraphPrepareRun` (constr).
- `audit_graph_prepare_out_counted` (Fixpoint).
- `audit_graph_prepare_edges_counted` (Fixpoint).
- `audit_graph_prepare_in_counted` (Fixpoint).
- `audit_graph_edge_count_counted` (Fixpoint).
- `audit_graph_prepare_counted` (def).
- `audit_graph_prepare_execution_exists_statement` (def).
- `audit_graph_prepare_callbacks_statement` (def).
- `audit_graph_prepare_map_model_event` (def).
- `audit_graph_prepare_map_model_work` (def).
- `audit_graph_prepare_map_model_expected` (def).
- `audit_graph_prepare_map_model_statement` (def).
- `audit_graph_prepare_emission_event` (def).
- `audit_graph_prepare_emission_work` (def).
- `audit_graph_prepare_emission_expected` (def).
- `audit_graph_prepare_emission_statement` (def).
- `audit_graph_prepare_input_width` (def).
- `audit_graph_prepare_input_budget` (def).
- `audit_graph_prepare_model_statement` (def).
- `audit_graph_full_call` (ind).
- `AuditGraphFullCase` (constr).
- `AuditGraphFullCall` (constr).
- `AuditGraphFullLength` (constr).
- `AuditGraphFullNodesLength` (constr).
- `AuditGraphFullFuel` (constr).
- `audit_graph_full_out` (Fixpoint).
- `audit_graph_full_edges` (Fixpoint).
- `audit_graph_full_in` (Fixpoint).
- `audit_graph_full_edge_count` (Fixpoint).
- `audit_graph_prepare_full_counted` (def).
- `audit_graph_full_event_work` (def).
- `audit_graph_prepare_full_work` (def).
- `audit_graph_prepare_full_event_bound` (def).
- `audit_graph_prepare_full_budget` (def).
- `audit_graph_prepare_full_statement` (def).
- `audit_prepare_callback_model` (rec).
- `audit_prepare_out_model` (proj).
- `audit_prepare_target_model` (proj).
- `audit_prepare_encode_model` (proj).
- `audit_prepare_callbacks_erase` (def).
- `audit_prepare_nested_event` (def).
- `audit_prepare_nested_out` (Fixpoint).
- `audit_prepare_nested_edges` (Fixpoint).
- `audit_prepare_nested_in` (Fixpoint).
- `audit_prepare_nested_edge_count` (Fixpoint).
- `audit_graph_prepare_nested_counted` (def).
- `audit_prepare_nested_body_work` (def).
- `audit_graph_prepare_nested_statement` (def).
- `audit_graph_prepare_nested_total_work` (def).
- `audit_comb_event` (ind).
- `AuditCombCase` (constr).
- `AuditCombBody` (constr).
- `audit_comb_call_count` (def).
- `audit_pos_iter` (Fixpoint).
- `audit_n_iter` (def).
- `audit_fold_left` (Fixpoint).
- `audit_fold_right` (Fixpoint).
- `audit_map` (Fixpoint).
- `audit_filter` (Fixpoint).
- `audit_existsb_strict` (Fixpoint).
- `audit_pos_iter_statement` (def).
- `audit_n_iter_statement` (def).
- `audit_fold_statement` (def).
- `audit_list_map_filter_exists_statement` (def).
- `audit_graph_reverse_work` (Fixpoint).
- `audit_graph_reverse_run` (ind).
- `GraphReverseNil` (constr).
- `GraphReverseCons` (constr).
- `audit_graph_reverse_run_statement` (def).
- `audit_graph_reverse_fast_work` (def).
- `audit_graph_reverse_fast_counted` (Fixpoint).
- `audit_graph_reverse_fast_run` (ind).
- `GraphReverseFastNil` (constr).
- `GraphReverseFastCons` (constr).
- `audit_graph_reverse_fast_run_statement` (def).
- `audit_graph_reverse_fast_counted_statement` (def).
- `audit_graph_external_callback_adapter` (rec).
- `audit_graph_external_callback_source` (proj).
- `audit_prepare_source_event` (ind).
- `PrepareSourceCase` (constr).
- `PrepareSourceOut` (constr).
- `PrepareSourceTarget` (constr).
- `PrepareSourceMap` (constr).
- `PrepareSourceLength` (constr).
- `PrepareSourceFuel` (constr).
- `audit_prepare_source_out` (Fixpoint).
- `audit_prepare_source_edges` (Fixpoint).
- `audit_prepare_source_in` (Fixpoint).
- `audit_prepare_source_edge_count` (Fixpoint).
- `audit_prepare_source_counted` (def).
- `audit_prepare_source_event_work` (def).
- `audit_prepare_source_body_event_work` (def).
- `audit_prepare_source_work` (def).
- `audit_prepare_source_body_work` (def).
- `audit_prepare_source_budget` (def).
- `audit_prepare_source_statement` (def).
- `audit_prepare_source_event_budget` (def).
- `audit_prepare_source_adapted_statement` (def).
- `audit_prepare_source_contract_statement` (def).
- `AuditPrepareCallbackModel` (record-constructor).

Future proof module: `GraphAuditBaseAdequacy`.

- `audit_graph_prepare_execution_exists_holds`:
  `GraphAuditBase.audit_graph_prepare_execution_exists_statement`; owner AUD-GR-BASE.
- `audit_graph_prepare_map_model_holds`: `GraphAuditBase.audit_graph_prepare_map_model_statement`;
  owner AUD-GR-BASE.
- `audit_graph_prepare_emission_holds`: `GraphAuditBase.audit_graph_prepare_emission_statement`;
  owner AUD-GR-BASE.
- `audit_graph_prepare_model_holds`: `GraphAuditBase.audit_graph_prepare_model_statement`; owner
  AUD-GR-BASE.
- `audit_graph_prepare_full_correct`: `GraphAuditBase.audit_graph_prepare_full_statement`; owner
  AUD-GR-BASE.
- `audit_graph_prepare_nested_correct`: `GraphAuditBase.audit_graph_prepare_nested_statement`; owner
  AUD-GR-BASE.
- `audit_pos_iter_holds`: `GraphAuditBase.audit_pos_iter_statement`; owner AUD-GR-BASE.
- `audit_n_iter_holds`: `GraphAuditBase.audit_n_iter_statement`; owner AUD-GR-BASE.
- `audit_fold_holds`: `GraphAuditBase.audit_fold_statement`; owner AUD-GR-BASE.
- `audit_list_map_filter_exists_holds`: `GraphAuditBase.audit_list_map_filter_exists_statement`;
  owner AUD-GR-BASE.
- `audit_graph_reverse_run_holds`: `GraphAuditBase.audit_graph_reverse_run_statement`; owner
  AUD-GR-BASE.
- `audit_graph_reverse_fast_run_holds`: `GraphAuditBase.audit_graph_reverse_fast_run_statement`;
  owner AUD-GR-BASE.
- `audit_graph_reverse_fast_counted_holds`:
  `GraphAuditBase.audit_graph_reverse_fast_counted_statement`; owner AUD-GR-BASE.
- `audit_prepare_source_correct`: `GraphAuditBase.audit_prepare_source_statement`; owner
  AUD-GR-BASE.
- `audit_prepare_source_adapted_holds`: `GraphAuditBase.audit_prepare_source_adapted_statement`;
  owner AUD-GR-BASE.
- `audit_prepare_source_contract_holds`: `GraphAuditBase.audit_prepare_source_contract_statement`;
  owner AUD-GR-BASE.

## GraphAuditCost

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `graph_audit_source_contract_statement` (def).

Future proof module: `GraphAuditCostAdequacy`.

- `graph_audit_source_contract_holds`: `GraphAuditCost.graph_audit_source_contract_statement`; owner
  AUD-GR.

## GraphAuditDfs

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_dfs_call` (ind).
- `AuditDfsCase` (constr).
- `AuditDfsTarget` (constr).
- `AuditDfsMember` (constr).
- `AuditDfsSuccessors` (constr).
- `AuditDfsDiscover` (constr).
- `AuditDfsFinish` (constr).
- `audit_dfs_step_counted` (def).
- `audit_dfs_run_counted` (Fixpoint).
- `audit_dfs_root_counted` (def).
- `audit_dfs_roots_counted` (Fixpoint).
- `audit_dfs_counted` (def).
- `audit_dfs_model_event` (def).
- `audit_dfs_model_work` (def).
- `audit_dfs_input_width` (def).
- `audit_dfs_input_event_bound` (def).
- `audit_dfs_input_budget` (def).
- `audit_dfs_counted_statement` (def).
- `audit_dfs_detail` (ind).
- `AuditDfsParentSet` (constr).
- `AuditDfsNumSet` (constr).
- `AuditDfsSeenAdd` (constr).
- `AuditDfsClock` (constr).
- `audit_dfs_discover_counted` (def).
- `audit_dfs_finish_counted` (def).
- `audit_dfs_detail_work` (def).
- `audit_dfs_helpers_statement` (def).
- `audit_dfs_full_call` (ind).
- `AuditDfsFullCase` (constr).
- `AuditDfsFullTarget` (constr).
- `AuditDfsFullMember` (constr).
- `AuditDfsFullSuccessors` (constr).
- `AuditDfsFullDiscover` (constr).
- `AuditDfsFullFinish` (constr).
- `AuditDfsFullDetail` (constr).
- `AuditDfsFullOutput` (constr).
- `audit_dfs_full_step_counted` (def).
- `audit_dfs_full_run_counted` (Fixpoint).
- `audit_dfs_full_root_counted` (def).
- `audit_dfs_full_roots_counted` (Fixpoint).
- `audit_dfs_full_counted` (def).
- `audit_dfs_full_model_event` (def).
- `audit_dfs_full_model_work` (def).
- `audit_dfs_full_input_width` (def).
- `audit_dfs_full_input_event_bound` (def).
- `audit_dfs_full_input_budget` (def).
- `audit_dfs_full_counted_statement` (def).
- `audit_dfs_callback_model` (rec).
- `audit_dfs_target_model` (proj).
- `audit_dfs_encode_model` (proj).
- `audit_dfs_callbacks_erase` (def).
- `audit_dfs_nested_event` (def).
- `audit_dfs_nested_get` (def).
- `audit_dfs_nested_set` (def).
- `audit_dfs_nested_discover` (def).
- `audit_dfs_nested_finish` (def).
- `audit_dfs_nested_step` (def).
- `audit_dfs_nested_run` (Fixpoint).
- `audit_dfs_nested_root` (def).
- `audit_dfs_nested_roots` (Fixpoint).
- `audit_dfs_nested_counted` (def).
- `audit_dfs_nested_body_work` (def).
- `audit_dfs_nested_statement` (def).
- `audit_dfs_nested_total_work` (def).
- `audit_graph_callback_capture` (ind).
- `AuditGraphTargetCapture` (constr).
- `AuditGraphEncodeCapture` (constr).
- `audit_graph_capture_callbacks` (def).
- `audit_graph_capture_callbacks_erases_statement` (def).
- `audit_graph_capture_work` (def).
- `audit_dfs_source_counted` (def).
- `audit_dfs_source_code` (def).
- `audit_dfs_source_event_work` (def).
- `audit_dfs_source_body_work` (def).
- `audit_dfs_source_work` (def).
- `audit_dfs_source_event_wellformed` (def).
- `audit_dfs_source_budget` (def).
- `audit_dfs_source_statement` (def).
- `audit_dfs_source_reverse_obligations` (def).
- `audit_dfs_source_successor_event` (def).
- `audit_dfs_source_successor_correspondence_statement` (def).
- `audit_dfs_source_successor_obligations` (def).
- `audit_dfs_capture_budget` (def).
- `audit_dfs_source_external_budget` (def).
- `audit_dfs_source_adapted_statement` (def).
- `audit_dfs_source_contract_statement` (def).
- `AuditDfsCallbackModel` (record-constructor).

Future proof module: `GraphAuditDfsAdequacy`.

- `audit_dfs_counted_correct`: `GraphAuditDfs.audit_dfs_counted_statement`; owner AUD-GR-DFS.
- `audit_dfs_helpers_correct`: `GraphAuditDfs.audit_dfs_helpers_statement`; owner AUD-GR-DFS.
- `audit_dfs_full_counted_correct`: `GraphAuditDfs.audit_dfs_full_counted_statement`; owner
  AUD-GR-DFS.
- `audit_dfs_nested_correct`: `GraphAuditDfs.audit_dfs_nested_statement`; owner AUD-GR-DFS.
- `audit_graph_capture_callbacks_erases_holds`:
  `GraphAuditDfs.audit_graph_capture_callbacks_erases_statement`; owner AUD-GR-DFS.
- `audit_dfs_source_correct`: `GraphAuditDfs.audit_dfs_source_statement`; owner AUD-GR-DFS.
- `audit_dfs_source_successor_correspondence_holds`:
  `GraphAuditDfs.audit_dfs_source_successor_correspondence_statement`; owner AUD-GR-DFS.
- `audit_dfs_source_adapted_holds`: `GraphAuditDfs.audit_dfs_source_adapted_statement`; owner
  AUD-GR-DFS.
- `audit_dfs_source_contract_holds`: `GraphAuditDfs.audit_dfs_source_contract_statement`; owner
  AUD-GR-DFS.

## GraphAuditDominatorSelect

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_nca_backend_trace` (rec).
- `audit_nca_backend_prepare` (proj).
- `audit_nca_backend_dfs` (proj).
- `audit_nca_backend_semi` (proj).
- `audit_nca_backend_core` (proj).
- `audit_nca_backend_erase` (proj).
- `audit_nca_backend_run` (def).
- `audit_nca_backend_selected_work` (def).
- `audit_nca_backend_erasure_statement` (def).
- `audit_dom_backend_trace` (ind).
- `AuditDomLtTrace` (constr).
- `AuditDomNcaTrace` (constr).
- `audit_dom_tree_with_run` (ind).
- `AuditDomWithLt` (constr).
- `AuditDomWithNca` (constr).
- `audit_dom_tree_with_erasure_statement` (def).
- `audit_dom_tree_default_erasure_statement` (def).
- `audit_flat_source_event` (ind).
- `FlatSourceCase` (constr).
- `FlatSourceCompare` (constr).
- `FlatSourceDfs` (constr).
- `FlatSourceMap` (constr).
- `audit_flat_source_compare` (def).
- `audit_flat_source_entries` (Fixpoint).
- `audit_flat_source_fold` (Fixpoint).
- `audit_flat_source_counted` (def).
- `audit_flat_source_event_work` (def).
- `audit_flat_source_event_external` (def).
- `audit_flat_source_work` (def).
- `audit_flat_source_external` (def).
- `audit_flat_source_budget` (def).
- `audit_flat_source_statement` (def).
- `audit_check_idom_event` (ind).
- `CheckIdomCase` (constr).
- `CheckIdomDfs` (constr).
- `CheckIdomDom` (constr).
- `CheckIdomElements` (constr).
- `CheckIdomSet` (constr).
- `CheckIdomMap` (constr).
- `CheckIdomCompare` (constr).
- `audit_check_idom_bindings` (Fixpoint).
- `audit_check_idom_dominates` (def).
- `audit_check_idom_nodes` (Fixpoint).
- `audit_check_idom_candidates` (Fixpoint).
- `audit_check_idom_source_counted` (def).
- `audit_check_idom_event_work` (def).
- `audit_check_idom_event_external` (def).
- `audit_check_idom_source_work` (def).
- `audit_check_idom_source_external` (def).
- `audit_check_idom_input_scale` (def).
- `audit_check_idom_source_budget` (def).
- `audit_check_idom_source_statement` (def).
- `audit_virtual_nca_stage_work` (def).
- `audit_virtual_nca_external_work` (def).
- `audit_virtual_nca_input_scale` (def).
- `audit_virtual_nca_input_budget` (def).
- `audit_dom_select_trace` (ind).
- `DomSelectLt` (constr).
- `DomSelectNca` (constr).
- `audit_dom_select_backend_work` (def).
- `audit_dom_select_backend_external` (def).
- `audit_dom_select_source_budget` (def).
- `audit_dom_select_input_budget` (def).
- `audit_dom_select_single_backend` (def).
- `audit_dom_select_single_run_statement` (def).
- `audit_virtual_nca_single_run_statement` (def).
- `audit_flat_check_capture_budget` (def).
- `audit_flat_source_event_budget` (def).
- `audit_flat_source_adapted_statement` (def).
- `audit_flat_source_contract_statement` (def).
- `audit_dom_source_body_budget` (def).
- `audit_dom_source_event_budget` (def).
- `audit_check_idom_event_budget` (def).
- `audit_check_idom_source_adapted_statement` (def).
- `audit_check_idom_source_contract_statement` (def).
- `audit_virtual_call_budget` (def).
- `audit_erase_nested_event_budget` (def).
- `audit_dom_select_backend_budget` (def).
- `audit_dom_select_single_adapted_statement` (def).
- `audit_dom_select_source_contract_statement` (def).
- `audit_virtual_nca_single_adapted_statement` (def).
- `audit_virtual_nca_source_contract_statement` (def).
- `audit_flat_source_full_contract_statement` (def).
- `audit_check_idom_source_full_contract_statement` (def).
- `audit_virtual_nca_source_full_contract_statement` (def).
- `audit_dom_select_source_full_contract_statement` (def).
- `AuditNcaBackendTrace` (record-constructor).

Future proof module: `GraphAuditDominatorSelectAdequacy`.

- `audit_nca_backend_erasure`: `GraphAuditDominatorSelect.audit_nca_backend_erasure_statement`;
  owner AUD-GR-DOM-SELECT.
- `audit_dom_tree_with_erasure`: `GraphAuditDominatorSelect.audit_dom_tree_with_erasure_statement`;
  owner AUD-GR-DOM-SELECT.
- `audit_dom_tree_default_erasure_holds`:
  `GraphAuditDominatorSelect.audit_dom_tree_default_erasure_statement`; owner AUD-GR-DOM-SELECT.
- `audit_flat_source_holds`: `GraphAuditDominatorSelect.audit_flat_source_statement`; owner
  AUD-GR-DOM-SELECT.
- `audit_check_idom_source_holds`: `GraphAuditDominatorSelect.audit_check_idom_source_statement`;
  owner AUD-GR-DOM-SELECT.
- `audit_dom_select_single_run_holds`:
  `GraphAuditDominatorSelect.audit_dom_select_single_run_statement`; owner AUD-GR-DOM-SELECT.
- `audit_virtual_nca_single_run_holds`:
  `GraphAuditDominatorSelect.audit_virtual_nca_single_run_statement`; owner AUD-GR-DOM-SELECT.
- `audit_flat_source_adapted_holds`:
  `GraphAuditDominatorSelect.audit_flat_source_adapted_statement`; owner AUD-GR-DOM-SELECT.
- `audit_flat_source_contract_holds`:
  `GraphAuditDominatorSelect.audit_flat_source_contract_statement`; owner AUD-GR-DOM-SELECT.
- `audit_check_idom_source_adapted_holds`:
  `GraphAuditDominatorSelect.audit_check_idom_source_adapted_statement`; owner AUD-GR-DOM-SELECT.
- `audit_check_idom_source_contract_holds`:
  `GraphAuditDominatorSelect.audit_check_idom_source_contract_statement`; owner AUD-GR-DOM-SELECT.
- `audit_dom_select_single_adapted_holds`:
  `GraphAuditDominatorSelect.audit_dom_select_single_adapted_statement`; owner AUD-GR-DOM-SELECT.
- `audit_dom_select_source_contract_holds`:
  `GraphAuditDominatorSelect.audit_dom_select_source_contract_statement`; owner AUD-GR-DOM-SELECT.
- `audit_virtual_nca_single_adapted_holds`:
  `GraphAuditDominatorSelect.audit_virtual_nca_single_adapted_statement`; owner AUD-GR-DOM-SELECT.
- `audit_virtual_nca_source_contract_holds`:
  `GraphAuditDominatorSelect.audit_virtual_nca_source_contract_statement`; owner AUD-GR-DOM-SELECT.
- `audit_flat_source_full_contract_holds`:
  `GraphAuditDominatorSelect.audit_flat_source_full_contract_statement`; owner AUD-GR-DOM-SELECT.
- `audit_check_idom_source_full_contract_holds`:
  `GraphAuditDominatorSelect.audit_check_idom_source_full_contract_statement`; owner
  AUD-GR-DOM-SELECT.
- `audit_virtual_nca_source_full_contract_holds`:
  `GraphAuditDominatorSelect.audit_virtual_nca_source_full_contract_statement`; owner
  AUD-GR-DOM-SELECT.
- `audit_dom_select_source_full_contract_holds`:
  `GraphAuditDominatorSelect.audit_dom_select_source_full_contract_statement`; owner
  AUD-GR-DOM-SELECT.

## GraphAuditDominators

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_lt_backend_trace` (rec).
- `audit_lt_backend_prepare` (proj).
- `audit_lt_backend_dfs` (proj).
- `audit_lt_backend_semi` (proj).
- `audit_lt_backend_core` (proj).
- `audit_lt_backend_erase` (proj).
- `audit_lt_backend_run` (def).
- `audit_lt_backend_selected_work` (def).
- `audit_lt_backend_erasure_statement` (def).
- `audit_dom_body` (ind).
- `AuditDomBodyRead` (constr).
- `AuditDomBodyTarget` (constr).
- `AuditDomBodyEncode` (constr).
- `audit_dom_call` (ind).
- `AuditDomInitialDfs` (constr).
- `AuditDomCase` (constr).
- `AuditDomElements` (constr).
- `AuditDomChildRead` (constr).
- `AuditDomChildSet` (constr).
- `AuditDomRootGet` (constr).
- `AuditDomPrepare` (constr).
- `AuditDomDfs` (constr).
- `AuditDomOutput` (constr).
- `audit_dom_children_counted` (Fixpoint).
- `audit_dom_roots_counted` (Fixpoint).
- `audit_dom_out_counted` (def).
- `audit_dom_target_counted` (def).
- `audit_dom_encode_counted` (def).
- `audit_dom_prepare_callbacks` (def).
- `audit_dom_dfs_callbacks` (def).
- `audit_dom_tree_counted` (def).
- `audit_dom_body_work` (def).
- `audit_dom_event_work` (def).
- `audit_dom_model_work` (def).
- `audit_dom_input_scale` (def).
- `audit_dom_input_event_bound` (def).
- `audit_dom_input_width` (def).
- `audit_dom_input_budget` (def).
- `audit_dom_tree_counted_statement` (def).
- `audit_dom_source_body` (ind).
- `DomSourceBodyMap` (constr).
- `DomSourceBodyTarget` (constr).
- `DomSourceBodyEncode` (constr).
- `audit_dom_source_event` (ind).
- `DomSourceCase` (constr).
- `DomSourceInitialDfs` (constr).
- `DomSourceElements` (constr).
- `DomSourceChild` (constr).
- `DomSourceParent` (constr).
- `DomSourcePrepare` (constr).
- `DomSourceDfs` (constr).
- `audit_dom_source_children` (Fixpoint).
- `audit_dom_source_roots` (Fixpoint).
- `audit_dom_source_out` (def).
- `audit_dom_source_target` (def).
- `audit_dom_source_encode` (def).
- `audit_dom_source_receipt` (rec).
- `audit_dom_source_forest` (proj).
- `audit_dom_source_index` (proj).
- `audit_dom_source_result` (proj).
- `audit_dom_source_events` (proj).
- `audit_dom_search_source_counted` (def).
- `audit_dom_source_body_work` (def).
- `audit_dom_source_body_external` (def).
- `audit_dom_source_event_work` (def).
- `audit_dom_source_event_external` (def).
- `audit_dom_source_work` (def).
- `audit_dom_source_external_work` (def).
- `audit_dom_search_source_budget` (def).
- `audit_dom_search_source_statement` (def).
- `audit_default_dom_single_run_statement` (def).
- `AuditLtBackendTrace` (record-constructor).
- `AuditDomSourceReceipt` (record-constructor).

Future proof module: `GraphAuditDominatorsAdequacy`.

- `audit_lt_backend_erasure`: `GraphAuditDominators.audit_lt_backend_erasure_statement`; owner
  AUD-GR-DOM.
- `audit_dom_tree_counted_correct`: `GraphAuditDominators.audit_dom_tree_counted_statement`; owner
  AUD-GR-DOM.
- `audit_dom_search_source_correct`: `GraphAuditDominators.audit_dom_search_source_statement`; owner
  AUD-GR-DOM.
- `audit_default_dom_single_run_holds`:
  `GraphAuditDominators.audit_default_dom_single_run_statement`; owner AUD-GR-DOM.

## GraphAuditDominatorsAdapter

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_default_virtual_event_budget` (def).
- `audit_default_erase_event_budget` (def).
- `audit_default_forest_body_budget` (def).
- `audit_default_dom_event_budget` (def).
- `audit_default_dom_input_budget` (def).
- `audit_default_dom_single_adapted_statement` (def).

Future proof module: `GraphAuditDominatorsAdapterAdequacy`.

- `audit_default_dom_single_adapted_holds`:
  `GraphAuditDominatorsAdapter.audit_default_dom_single_adapted_statement`; owner AUD-GR-DOM.

## GraphAuditFrontier

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_frontier_dom_call` (ind).
- `AuditFrontierDomGet` (constr).
- `AuditFrontierDomLe` (constr).
- `audit_frontier_dom_counted` (def).
- `audit_frontier_dom_event_work` (def).
- `audit_frontier_dom_statement` (def).
- `audit_frontier_call` (ind).
- `AuditFrontierCase` (constr).
- `AuditFrontierDom` (constr).
- `AuditFrontierParent` (constr).
- `AuditFrontierDfs` (constr).
- `AuditFrontierSource` (constr).
- `AuditFrontierTarget` (constr).
- `AuditFrontierPred` (constr).
- `AuditFrontierMem` (constr).
- `AuditFrontierGet` (constr).
- `AuditFrontierSetMember` (constr).
- `AuditFrontierSetRow` (constr).
- `AuditFrontierOutput` (constr).
- `audit_frontier_step_counted` (def).
- `audit_frontier_run_counted` (Fixpoint).
- `audit_frontier_runner_counted` (def).
- `audit_frontier_event_work` (def).
- `audit_frontier_model_work` (def).
- `audit_frontier_runner_width` (def).
- `audit_frontier_runner_event_bound` (def).
- `audit_frontier_runner_budget` (def).
- `audit_frontier_runner_statement` (def).
- `audit_frontier_collect_pred` (Fixpoint).
- `audit_frontier_live_filter` (Fixpoint).
- `audit_frontier_targets` (Fixpoint).
- `audit_frontier_edge_events` (Fixpoint).
- `audit_frontier_rows_counted` (Fixpoint).
- `audit_frontier_counted` (def).
- `audit_frontier_input_edges` (def).
- `audit_frontier_input_width` (def).
- `audit_frontier_input_event_bound` (def).
- `audit_frontier_input_budget` (def).
- `audit_frontier_counted_statement` (def).
- `audit_ifrontier_body` (ind).
- `AuditIfCase` (constr).
- `AuditIfGet` (constr).
- `AuditIfElements` (constr).
- `AuditIfMap` (constr).
- `AuditIfTarget` (constr).
- `AuditIfEncode` (constr).
- `audit_ifrontier_successors_counted` (def).
- `audit_ifrontier_entries_counted` (Fixpoint).
- `audit_ifrontier_out_counted` (def).
- `audit_ifrontier_target_counted` (def).
- `audit_ifrontier_encode_counted` (def).
- `audit_ifrontier_prepare_callbacks` (def).
- `audit_ifrontier_dfs_callbacks` (def).
- `audit_ifrontier_counted` (def).
- `audit_ifrontier_body_work` (def).
- `audit_ifrontier_work` (def).
- `audit_ifrontier_scale` (def).
- `audit_ifrontier_width` (def).
- `audit_ifrontier_budget` (def).
- `audit_ifrontier_statement` (def).
- `audit_frontier_source_callbacks` (rec).
- `audit_frontier_source_encode` (proj).
- `audit_frontier_source_source` (proj).
- `audit_frontier_source_target` (proj).
- `audit_frontier_source_event` (ind).
- `FrontierSourceCase` (constr).
- `FrontierSourceDfs` (constr).
- `FrontierSourceSource` (constr).
- `FrontierSourceTarget` (constr).
- `FrontierSourceParent` (constr).
- `FrontierSourceRank` (constr).
- `FrontierSourcePred` (constr).
- `FrontierSourceRows` (constr).
- `FrontierSourceSet` (constr).
- `FrontierSourceCompare` (constr).
- `FrontierSourceOutput` (constr).
- `audit_frontier_source_dom` (def).
- `audit_frontier_source_step` (def).
- `audit_frontier_source_walk` (Fixpoint).
- `audit_frontier_source_incoming` (Fixpoint).
- `audit_frontier_source_filter` (Fixpoint).
- `audit_frontier_source_targets` (Fixpoint).
- `audit_frontier_source_edges` (Fixpoint).
- `audit_frontier_source_rows` (Fixpoint).
- `audit_frontier_source_counted` (def).
- `audit_frontier_source_callbacks_erase` (def).
- `audit_frontier_source_event_work` (def).
- `audit_frontier_source_body_event_work` (def).
- `audit_frontier_source_work` (def).
- `audit_frontier_source_body_work` (def).
- `audit_frontier_source_input_edges` (def).
- `audit_frontier_source_input_width` (def).
- `audit_frontier_source_input_event_bound` (def).
- `audit_frontier_source_input_budget` (def).
- `audit_frontier_source_statement` (def).
- `AuditFrontierSourceCallbacks` (record-constructor).

Future proof module: `GraphAuditFrontierAdequacy`.

- `audit_frontier_dom_correct`: `GraphAuditFrontier.audit_frontier_dom_statement`; owner AUD-GR-DF.
- `audit_frontier_runner_correct`: `GraphAuditFrontier.audit_frontier_runner_statement`; owner
  AUD-GR-DF.
- `audit_frontier_counted_correct`: `GraphAuditFrontier.audit_frontier_counted_statement`; owner
  AUD-GR-DF.
- `audit_ifrontier_correct`: `GraphAuditFrontier.audit_ifrontier_statement`; owner AUD-GR-DF.
- `audit_frontier_source_correct`: `GraphAuditFrontier.audit_frontier_source_statement`; owner
  AUD-GR-DF.

## GraphAuditFrontierAdapter

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_frontier_adapter_event_budget` (def).
- `audit_frontier_source_adapted_statement` (def).

Future proof module: `GraphAuditFrontierAdapterAdequacy`.

- `audit_frontier_source_adapted_holds`:
  `GraphAuditFrontierAdapter.audit_frontier_source_adapted_statement`; owner AUD-GR-DF.

## GraphAuditIdf

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_idf_capture_budget` (def).
- `audit_idf_collect_call` (ind).
- `AuditIdfCollectCase` (constr).
- `AuditIdfCollectTarget` (constr).
- `AuditIdfCollectParent` (constr).
- `AuditIdfCollectDom` (constr).
- `AuditIdfCollectLive` (constr).
- `AuditIdfCollectOut` (constr).
- `AuditIdfCollectSucc` (constr).
- `audit_idf_join_counted` (def).
- `audit_idf_edge_counted` (def).
- `audit_idf_edges_counted` (Fixpoint).
- `audit_idf_nodes_counted` (Fixpoint).
- `audit_idf_collect_event_work` (def).
- `audit_idf_collect_work` (def).
- `audit_idf_collect_edges` (def).
- `audit_idf_collect_event_bound` (def).
- `audit_idf_collect_width` (def).
- `audit_idf_collect_budget` (def).
- `audit_idf_collect_statement` (def).
- `audit_idf_seed_call` (ind).
- `AuditIdfSeedCase` (constr).
- `AuditIdfSeedGet` (constr).
- `AuditIdfSeedSub` (constr).
- `AuditIdfSeedPush` (constr).
- `audit_idf_seed_counted` (def).
- `audit_idf_seeds_counted` (Fixpoint).
- `audit_idf_initial_counted` (def).
- `audit_idf_seed_event_work` (def).
- `audit_idf_initial_work` (def).
- `audit_idf_initial_width` (def).
- `audit_idf_initial_budget` (def).
- `audit_idf_initial_statement` (def).
- `audit_idf_work_call` (ind).
- `IdfWorkCase` (constr).
- `IdfWorkIsEmpty` (constr).
- `IdfWorkPop` (constr).
- `IdfWorkPush` (constr).
- `IdfWorkGet` (constr).
- `IdfWorkMem` (constr).
- `IdfWorkAdd` (constr).
- `IdfWorkDfs` (constr).
- `IdfWorkCollect` (constr).
- `IdfWorkSub` (constr).
- `IdfWorkArithmetic` (constr).
- `audit_idf_emit_counted` (def).
- `audit_idf_emit_list_counted` (Fixpoint).
- `audit_idf_scan_add_counted` (Fixpoint).
- `audit_idf_work_step_counted` (def).
- `audit_idf_run_counted` (Fixpoint).
- `audit_idf_work_step_statement` (def).
- `audit_idf_run_statement` (def).
- `audit_idf_producer_call` (ind).
- `IdfProducerDom` (constr).
- `IdfProducerPrepare` (constr).
- `IdfProducerDfs` (constr).
- `IdfProducerSeed` (constr).
- `IdfProducerWork` (constr).
- `IdfProducerLevelGet` (constr).
- `IdfProducerLevelRead` (constr).
- `IdfProducerLevelWrite` (constr).
- `IdfProducerCase` (constr).
- `audit_idf_levels_fold_counted` (Fixpoint).
- `audit_direct_pruned_idf_counted` (def).
- `audit_direct_pruned_idf_statement` (def).
- `audit_direct_idf_counted` (def).
- `audit_direct_idf_statement` (def).
- `audit_idf_dom_body_event_work` (def).
- `audit_idf_dom_event_work` (def).
- `audit_idf_work_event_work` (def).
- `audit_idf_producer_event_work` (def).
- `audit_idf_selected_work` (def).
- `audit_idf_input_support` (def).
- `audit_idf_input_scale` (def).
- `audit_idf_input_width` (def).
- `audit_idf_selected_input_budget` (def).
- `audit_direct_pruned_idf_selected_bound_statement` (def).
- `audit_idf_collect_source_event` (ind).
- `IdfCollectSourceCase` (constr).
- `IdfCollectSourceTarget` (constr).
- `IdfCollectSourceLive` (constr).
- `IdfCollectSourceParent` (constr).
- `IdfCollectSourceEdges` (constr).
- `IdfCollectSourceDom` (constr).
- `IdfCollectSourceSucc` (constr).
- `audit_idf_collect_source_join` (def).
- `audit_idf_collect_source_edge` (def).
- `audit_idf_collect_source_edges` (Fixpoint).
- `audit_idf_collect_source_nodes` (Fixpoint).
- `audit_idf_collect_source_erasure_statement` (def).
- `audit_idf_collect_source_event_work` (def).
- `audit_idf_collect_source_event_external` (def).
- `audit_idf_collect_source_work` (def).
- `audit_idf_collect_source_external` (def).
- `audit_idf_collect_source_budget` (def).
- `audit_idf_collect_source_bound_statement` (def).
- `audit_idf_frontier_event_budget` (def).
- `audit_idf_collect_source_event_budget` (def).
- `audit_idf_collect_source_adapted_statement` (def).
- `audit_idf_collect_source_contract_statement` (def).
- `audit_idf_queue_event` (ind).
- `IdfQueueCase` (constr).
- `IdfQueueMap` (constr).
- `IdfQueueSet` (constr).
- `IdfQueuePush` (constr).
- `IdfQueueSub` (constr).
- `IdfQueueSucc` (constr).
- `audit_idf_queue_priority` (def).
- `audit_idf_queue_seed` (def).
- `audit_idf_queue_seeds` (Fixpoint).
- `audit_idf_queue_succ` (def).
- `audit_idf_queue_emit` (def).
- `audit_idf_queue_source_erasure_statement` (def).
- `audit_idf_queue_event_work` (def).
- `audit_idf_queue_push_external` (def).
- `audit_idf_queue_event_external` (def).
- `audit_idf_queue_source_work` (def).
- `audit_idf_queue_source_external` (def).
- `audit_idf_queue_seed_budget` (def).
- `audit_idf_queue_emit_budget` (def).
- `audit_idf_queue_source_bound_statement` (def).
- `audit_idf_queue_push_budget` (def).
- `audit_idf_queue_event_budget` (def).
- `audit_idf_queue_source_adapted_statement` (def).
- `audit_idf_queue_source_contract_statement` (def).
- `audit_idf_prepare_event` (ind).
- `IdfPrepareDom` (constr).
- `IdfPrepareDfs` (constr).
- `IdfPrepareParent` (constr).
- `IdfPrepareLevel` (constr).
- `IdfPrepareSucc` (constr).
- `IdfPrepareOutput` (constr).
- `IdfPrepareCase` (constr).
- `audit_idf_prepare_level_step` (def).
- `audit_idf_prepare_levels` (Fixpoint).
- `audit_idf_prepare_receipt` (rec).
- `audit_idf_prepare_forest` (proj).
- `audit_idf_prepare_index` (proj).
- `audit_idf_prepare_values` (proj).
- `audit_idf_prepare_events` (proj).
- `audit_idf_prepare_source_counted` (def).
- `audit_idf_prepare_source_erasure_statement` (def).
- `audit_idf_prepare_index_erasure_statement` (def).
- `audit_idf_prepare_event_work` (def).
- `audit_idf_prepare_event_external` (def).
- `audit_idf_prepare_source_work` (def).
- `audit_idf_prepare_source_external` (def).
- `audit_idf_prepare_source_budget` (def).
- `audit_idf_prepare_source_statement` (def).
- `audit_idf_prepare_body_budget` (def).
- `audit_idf_prepare_dom_budget` (def).
- `audit_idf_prepare_event_budget` (def).
- `audit_idf_prepare_source_adapted_statement` (def).
- `audit_idf_prepare_source_contract_statement` (def).
- `audit_idf_full_event` (ind).
- `IdfFullCase` (constr).
- `IdfFullPrepare` (constr).
- `IdfFullQueue` (constr).
- `IdfFullPop` (constr).
- `IdfFullDfs` (constr).
- `IdfFullCollect` (constr).
- `IdfFullSet` (constr).
- `IdfFullAdd` (constr).
- `IdfFullEmpty` (constr).
- `IdfFullFuel` (constr).
- `audit_idf_full_scan` (Fixpoint).
- `audit_idf_full_emit` (Fixpoint).
- `audit_idf_full_step` (def).
- `audit_idf_full_run` (Fixpoint).
- `audit_idf_full_source_counted` (def).
- `audit_idf_full_source_erasure_statement` (def).
- `audit_idf_full_event_work` (def).
- `audit_idf_full_event_external` (def).
- `audit_idf_full_source_work` (def).
- `audit_idf_full_source_external` (def).
- `audit_idf_full_input_scale` (def).
- `audit_idf_full_input_budget` (def).
- `audit_idf_full_source_statement` (def).
- `audit_idf_full_unpruned_source_statement` (def).
- `audit_idf_full_event_budget` (def).
- `audit_idf_full_source_adapted_statement` (def).
- `audit_idf_full_unpruned_adapted_statement` (def).
- `audit_idf_full_source_contract_statement` (def).
- `IdfPrepareReceipt` (record-constructor).

Future proof module: `GraphAuditIdfAdequacy`.

- `audit_idf_collect_correct`: `GraphAuditIdf.audit_idf_collect_statement`; owner AUD-GR-IDF.
- `audit_idf_initial_correct`: `GraphAuditIdf.audit_idf_initial_statement`; owner AUD-GR-IDF.
- `audit_idf_work_step_correct`: `GraphAuditIdf.audit_idf_work_step_statement`; owner AUD-GR-IDF.
- `audit_idf_run_correct`: `GraphAuditIdf.audit_idf_run_statement`; owner AUD-GR-IDF.
- `audit_direct_pruned_idf_correct`: `GraphAuditIdf.audit_direct_pruned_idf_statement`; owner
  AUD-GR-IDF.
- `audit_direct_idf_correct`: `GraphAuditIdf.audit_direct_idf_statement`; owner AUD-GR-IDF.
- `audit_direct_pruned_idf_selected_bound`:
  `GraphAuditIdf.audit_direct_pruned_idf_selected_bound_statement`; owner AUD-GR-IDF.
- `audit_idf_collect_source_erasure_holds`:
  `GraphAuditIdf.audit_idf_collect_source_erasure_statement`; owner AUD-GR-IDF.
- `audit_idf_collect_source_bound_holds`: `GraphAuditIdf.audit_idf_collect_source_bound_statement`;
  owner AUD-GR-IDF.
- `audit_idf_collect_source_adapted_holds`:
  `GraphAuditIdf.audit_idf_collect_source_adapted_statement`; owner AUD-GR-IDF.
- `audit_idf_collect_source_contract_holds`:
  `GraphAuditIdf.audit_idf_collect_source_contract_statement`; owner AUD-GR-IDF.
- `audit_idf_queue_source_erasure_holds`: `GraphAuditIdf.audit_idf_queue_source_erasure_statement`;
  owner AUD-GR-IDF.
- `audit_idf_queue_source_bound_holds`: `GraphAuditIdf.audit_idf_queue_source_bound_statement`;
  owner AUD-GR-IDF.
- `audit_idf_queue_source_adapted_holds`: `GraphAuditIdf.audit_idf_queue_source_adapted_statement`;
  owner AUD-GR-IDF.
- `audit_idf_queue_source_contract_holds`:
  `GraphAuditIdf.audit_idf_queue_source_contract_statement`; owner AUD-GR-IDF.
- `audit_idf_prepare_source_erasure_holds`:
  `GraphAuditIdf.audit_idf_prepare_source_erasure_statement`; owner AUD-GR-IDF.
- `audit_idf_prepare_index_erasure_holds`:
  `GraphAuditIdf.audit_idf_prepare_index_erasure_statement`; owner AUD-GR-IDF.
- `audit_idf_prepare_source_holds`: `GraphAuditIdf.audit_idf_prepare_source_statement`; owner
  AUD-GR-IDF.
- `audit_idf_prepare_source_adapted_holds`:
  `GraphAuditIdf.audit_idf_prepare_source_adapted_statement`; owner AUD-GR-IDF.
- `audit_idf_prepare_source_contract_holds`:
  `GraphAuditIdf.audit_idf_prepare_source_contract_statement`; owner AUD-GR-IDF.
- `audit_idf_full_source_erasure_holds`: `GraphAuditIdf.audit_idf_full_source_erasure_statement`;
  owner AUD-GR-IDF.
- `audit_idf_full_source_holds`: `GraphAuditIdf.audit_idf_full_source_statement`; owner AUD-GR-IDF.
- `audit_idf_full_unpruned_source_holds`: `GraphAuditIdf.audit_idf_full_unpruned_source_statement`;
  owner AUD-GR-IDF.
- `audit_idf_full_source_adapted_holds`: `GraphAuditIdf.audit_idf_full_source_adapted_statement`;
  owner AUD-GR-IDF.
- `audit_idf_full_unpruned_adapted_holds`:
  `GraphAuditIdf.audit_idf_full_unpruned_adapted_statement`; owner AUD-GR-IDF.
- `audit_idf_full_source_contract_holds`: `GraphAuditIdf.audit_idf_full_source_contract_statement`;
  owner AUD-GR-IDF.

## GraphAuditLengauerTarjan

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_lt_call` (ind).
- `AuditLtCase` (constr).
- `AuditLtInner` (constr).
- `AuditLtBucketGet` (constr).
- `AuditLtBucketSet` (constr).
- `AuditLtTreeGet` (constr).
- `AuditLtSource` (constr).
- `AuditLtLink` (constr).
- `AuditLtEncode` (constr).
- `AuditLtEq` (constr).
- `AuditLtOutput` (constr).
- `audit_lt_buckets_counted` (Fixpoint).
- `audit_lt_member_run` (ind).
- `AuditLtMember` (constr).
- `audit_lt_members_run` (ind).
- `AuditLtMembersNil` (constr).
- `AuditLtMembersCons` (constr).
- `audit_lt_reverse_run` (ind).
- `AuditLtReverseRoot` (constr).
- `AuditLtReverseNode` (constr).
- `audit_lt_reverse_fold_run` (ind).
- `AuditLtReverseNil` (constr).
- `AuditLtReverseCons` (constr).
- `audit_lt_correct_counted` (def).
- `audit_lt_correct_fold` (Fixpoint).
- `audit_lt_compute_run` (def).
- `audit_lt_event_work` (def).
- `audit_lt_model_work` (def).
- `audit_lt_event_bound` (def).
- `audit_lt_input_width` (def).
- `audit_lt_input_budget` (def).
- `audit_lt_compute_statement` (def).
- `audit_lt_compute_unique_statement` (def).
- `audit_lt_nested_event` (ind).
- `LtNestedCase` (constr).
- `LtNestedSemi` (constr).
- `LtNestedProducer` (constr).
- `LtNestedBucket` (constr).
- `LtNestedTree` (constr).
- `LtNestedSource` (constr).
- `LtNestedEncode` (constr).
- `LtNestedEqual` (constr).
- `LtNestedOutput` (constr).
- `audit_lt_nested_buckets` (Fixpoint).
- `audit_lt_nested_member_run` (ind).
- `LtNestedMember` (constr).
- `audit_lt_nested_members_run` (ind).
- `LtNestedMembersNil` (constr).
- `LtNestedMembersCons` (constr).
- `audit_lt_nested_reverse_run` (ind).
- `LtNestedReverseRoot` (constr).
- `LtNestedReverseNode` (constr).
- `audit_lt_nested_reverse_fold_run` (ind).
- `LtNestedReverseNil` (constr).
- `LtNestedReverseCons` (constr).
- `audit_lt_nested_correct` (def).
- `audit_lt_nested_correct_fold` (Fixpoint).
- `audit_lt_nested_run` (def).
- `audit_lt_nested_erasure_statement` (def).
- `audit_lt_nested_unique_statement` (def).
- `audit_lt_nested_event_work` (def).
- `audit_lt_nested_body_event_work` (def).
- `audit_lt_nested_work` (def).
- `audit_lt_nested_body_work` (def).
- `audit_lt_nested_input_width` (def).
- `audit_lt_nested_input_event_bound` (def).
- `audit_lt_nested_input_budget` (def).
- `audit_lt_nested_bound_statement` (def).
- `audit_virtual_lt_run` (def).
- `audit_virtual_lt_erasure_statement` (def).
- `audit_virtual_lt_stage_work` (def).
- `audit_virtual_lt_external_work` (def).
- `audit_virtual_lt_input_support` (def).
- `audit_virtual_lt_input_width` (def).
- `audit_virtual_lt_input_scale` (def).
- `audit_virtual_lt_input_budget` (def).

Future proof module: `GraphAuditLengauerTarjanAdequacy`.

- `audit_lt_compute_correct`: `GraphAuditLengauerTarjan.audit_lt_compute_statement`; owner
  AUD-GR-LT.
- `audit_lt_compute_unique`: `GraphAuditLengauerTarjan.audit_lt_compute_unique_statement`; owner
  AUD-GR-LT.
- `audit_lt_nested_erasure`: `GraphAuditLengauerTarjan.audit_lt_nested_erasure_statement`; owner
  AUD-GR-LT.
- `audit_lt_nested_unique`: `GraphAuditLengauerTarjan.audit_lt_nested_unique_statement`; owner
  AUD-GR-LT.
- `audit_lt_nested_bound`: `GraphAuditLengauerTarjan.audit_lt_nested_bound_statement`; owner
  AUD-GR-LT.
- `audit_virtual_lt_erasure`: `GraphAuditLengauerTarjan.audit_virtual_lt_erasure_statement`; owner
  AUD-GR-LT.

## GraphAuditLoops

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_loop_call` (ind).
- `AuditLoopCase` (constr).
- `AuditLoopDfs` (constr).
- `AuditLoopScc` (constr).
- `AuditLoopRead` (constr).
- `AuditLoopEdges` (constr).
- `AuditLoopEncode` (constr).
- `AuditLoopTarget` (constr).
- `AuditLoopCompare` (constr).
- `AuditLoopSet` (constr).
- `AuditLoopNodeWrite` (constr).
- `AuditLoopParentWrite` (constr).
- `AuditLoopMap` (constr).
- `AuditLoopUnion` (constr).
- `AuditLoopOutput` (constr).
- `AuditLoopDepth` (constr).
- `audit_loop_choose_counted` (Fixpoint).
- `audit_loop_without_counted` (Fixpoint).
- `audit_loop_self_edges` (Fixpoint).
- `audit_loop_cyclic_counted` (def).
- `audit_loop_block_counted` (def).
- `audit_loop_blocks_counted` (Fixpoint).
- `audit_loop_layer_counted` (def).
- `audit_loop_iter_event` (def).
- `audit_loop_entries_counted` (def).
- `audit_loop_set_counted` (Fixpoint).
- `audit_loop_nodes_counted` (Fixpoint).
- `audit_loop_parents_counted` (Fixpoint).
- `audit_loop_owners_counted` (Fixpoint).
- `audit_loop_counted` (def).
- `audit_loop_trie_nodes_ne` (Fixpoint).
- `audit_loop_trie_nodes` (def).
- `audit_loop_event_work` (def).
- `audit_loop_model_work` (def).
- `audit_loop_input_event_bound` (def).
- `audit_loop_input_budget` (def).
- `audit_loop_counted_statement` (def).
- `audit_loop_singleton_graph` (def).
- `audit_loop_steps_event` (ind).
- `LoopStepsCase` (constr).
- `LoopStepsRank` (constr).
- `LoopStepsEdges` (constr).
- `LoopStepsTarget` (constr).
- `LoopStepsEncode` (constr).
- `LoopStepsEq` (constr).
- `LoopStepsLe` (constr).
- `audit_loop_steps_choose` (Fixpoint).
- `audit_loop_steps_equal` (def).
- `audit_loop_steps_without` (Fixpoint).
- `audit_loop_steps_self` (Fixpoint).
- `audit_loop_steps_cyclic` (def).
- `audit_loop_steps_erasure_statement` (def).
- `audit_loop_steps_event_work` (def).
- `audit_loop_steps_event_external` (def).
- `audit_loop_steps_work` (def).
- `audit_loop_steps_external` (def).
- `audit_loop_steps_budget` (def).
- `audit_loop_steps_bound_statement` (def).
- `audit_loop_pack_event` (ind).
- `LoopPackCase` (constr).
- `LoopPackSet` (constr).
- `LoopPackNodes` (constr).
- `LoopPackParent` (constr).
- `LoopPackTransform` (constr).
- `LoopPackUnion` (constr).
- `audit_loop_pack_nodes` (Fixpoint).
- `audit_loop_pack_parents` (Fixpoint).
- `audit_loop_pack_owners` (Fixpoint).
- `audit_loop_pack_source_counted` (def).
- `audit_loop_pack_event_work` (def).
- `audit_loop_pack_event_external` (def).
- `audit_loop_pack_source_work` (def).
- `audit_loop_pack_source_external` (def).
- `audit_loop_pack_input_scale` (def).
- `audit_loop_pack_source_budget` (def).
- `audit_loop_pack_source_statement` (def).
- `audit_loop_full_event` (ind).
- `LoopFullCase` (constr).
- `LoopFullOutput` (constr).
- `LoopFullDepth` (constr).
- `LoopFullDfs` (constr).
- `LoopFullScc` (constr).
- `LoopFullStep` (constr).
- `LoopFullPack` (constr).
- `audit_loop_full_block` (def).
- `audit_loop_full_blocks` (Fixpoint).
- `audit_loop_full_layer` (def).
- `audit_loop_full_entries` (def).
- `audit_loop_full_source_counted` (def).
- `audit_loop_full_source_erasure_statement` (def).
- `audit_loop_full_event_work` (def).
- `audit_loop_full_event_external` (def).
- `audit_loop_full_source_work` (def).
- `audit_loop_full_source_external` (def).
- `audit_loop_full_source_budget` (def).
- `audit_loop_full_source_statement` (def).
- `audit_loop_full_capture_budget` (def).
- `audit_loop_full_event_budget` (def).
- `audit_loop_full_source_adapted_statement` (def).
- `audit_loop_full_source_contract_statement` (def).

Future proof module: `GraphAuditLoopsAdequacy`.

- `audit_loop_counted_correct`: `GraphAuditLoops.audit_loop_counted_statement`; owner AUD-GR-LOOP.
- `audit_loop_steps_erasure_holds`: `GraphAuditLoops.audit_loop_steps_erasure_statement`; owner
  AUD-GR-LOOP.
- `audit_loop_steps_bound_holds`: `GraphAuditLoops.audit_loop_steps_bound_statement`; owner
  AUD-GR-LOOP.
- `audit_loop_pack_source_holds`: `GraphAuditLoops.audit_loop_pack_source_statement`; owner
  AUD-GR-LOOP.
- `audit_loop_full_source_erasure_holds`:
  `GraphAuditLoops.audit_loop_full_source_erasure_statement`; owner AUD-GR-LOOP.
- `audit_loop_full_source_holds`: `GraphAuditLoops.audit_loop_full_source_statement`; owner
  AUD-GR-LOOP.
- `audit_loop_full_source_adapted_holds`:
  `GraphAuditLoops.audit_loop_full_source_adapted_statement`; owner AUD-GR-LOOP.
- `audit_loop_full_source_contract_holds`:
  `GraphAuditLoops.audit_loop_full_source_contract_statement`; owner AUD-GR-LOOP.

## GraphAuditScc

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_thelper_event` (ind).
- `THCase` (constr).
- `THGet` (constr).
- `THGetEdges` (constr).
- `THSet` (constr).
- `THRemove` (constr).
- `THCompare` (constr).
- `THPosCompare` (constr).
- `THMin` (constr).
- `THSucc` (constr).
- `THTrieSet` (constr).
- `audit_tarjan_discover_counted` (def).
- `audit_tarjan_lower_counted` (def).
- `audit_tarjan_pop_counted` (Fixpoint).
- `audit_tarjan_emit_counted` (def).
- `audit_tarjan_close_counted` (def).
- `audit_thelper_event_work` (def).
- `audit_thelper_work` (def).
- `audit_tarjan_helpers_erasure_statement` (def).
- `audit_tarjan_helpers_event_bound_statement` (def).
- `audit_tarjan_call` (ind).
- `AuditTarjanCase` (constr).
- `AuditTarjanTarget` (constr).
- `AuditTarjanMember` (constr).
- `AuditTarjanGet` (constr).
- `AuditTarjanDiscover` (constr).
- `AuditTarjanLower` (constr).
- `AuditTarjanClose` (constr).
- `AuditTarjanHelper` (constr).
- `AuditTarjanSet` (constr).
- `AuditTarjanOutput` (constr).
- `audit_tarjan_step_counted` (def).
- `audit_tarjan_run_counted` (Fixpoint).
- `audit_tarjan_root_counted` (def).
- `audit_tarjan_roots_counted` (Fixpoint).
- `audit_tarjan_region_counted` (Fixpoint).
- `audit_scc_within_counted` (def).
- `audit_tarjan_event_work` (def).
- `audit_tarjan_model_work` (def).
- `audit_tarjan_input_event_bound` (def).
- `audit_tarjan_input_budget` (def).
- `audit_scc_within_counted_statement` (def).
- `audit_tarjan_nested_event` (def).
- `audit_tarjan_nested_get` (def).
- `audit_tarjan_nested_set` (def).
- `audit_tarjan_nested_remove` (def).
- `audit_tarjan_nested_discover` (def).
- `audit_tarjan_nested_lower` (def).
- `audit_tarjan_nested_pop` (Fixpoint).
- `audit_tarjan_nested_emit` (def).
- `audit_tarjan_nested_close` (def).
- `audit_tarjan_nested_step` (def).
- `audit_tarjan_nested_run` (Fixpoint).
- `audit_tarjan_nested_root` (def).
- `audit_tarjan_nested_roots` (Fixpoint).
- `audit_tarjan_nested_region` (Fixpoint).
- `audit_scc_within_nested_counted` (def).
- `audit_tarjan_nested_body_work` (def).
- `audit_tarjan_nested_total_work` (def).
- `audit_scc_within_nested_statement` (def).
- `audit_scc_within_nested_total_statement` (def).
- `audit_scc_source_counted` (def).
- `audit_scc_source_codes` (def).
- `audit_scc_reverse_work` (def).
- `audit_scc_reverse_run_statement` (def).
- `audit_scc_source_helper_work` (def).
- `audit_scc_source_event_work` (def).
- `audit_scc_source_event_wellformed` (def).
- `audit_scc_source_work` (def).
- `audit_scc_source_body_work` (def).
- `audit_scc_source_budget` (def).
- `audit_scc_source_statement` (def).
- `audit_scc_min_source_model` (def).
- `audit_scc_min_source_model_statement` (def).
- `audit_scc_source_event_primitive` (def).
- `audit_scc_source_primitive_correspondence_statement` (def).
- `audit_scc_source_library_obligations` (def).
- `audit_scc_capture_budget` (def).
- `audit_scc_source_external_budget` (def).
- `audit_scc_source_adapted_statement` (def).
- `audit_scc_source_contract_statement` (def).

Future proof module: `GraphAuditSccAdequacy`.

- `audit_tarjan_helpers_erasure`: `GraphAuditScc.audit_tarjan_helpers_erasure_statement`; owner
  AUD-GR-SCC.
- `audit_tarjan_helpers_event_bound`: `GraphAuditScc.audit_tarjan_helpers_event_bound_statement`;
  owner AUD-GR-SCC.
- `audit_scc_within_counted_correct`: `GraphAuditScc.audit_scc_within_counted_statement`; owner
  AUD-GR-SCC.
- `audit_scc_within_nested_holds`: `GraphAuditScc.audit_scc_within_nested_statement`; owner
  AUD-GR-SCC.
- `audit_scc_within_nested_total_holds`: `GraphAuditScc.audit_scc_within_nested_total_statement`;
  owner AUD-GR-SCC.
- `audit_scc_reverse_run_holds`: `GraphAuditScc.audit_scc_reverse_run_statement`; owner AUD-GR-SCC.
- `audit_scc_source_correct`: `GraphAuditScc.audit_scc_source_statement`; owner AUD-GR-SCC.
- `audit_scc_min_source_model_holds`: `GraphAuditScc.audit_scc_min_source_model_statement`; owner
  AUD-GR-SCC.
- `audit_scc_source_primitive_correspondence_holds`:
  `GraphAuditScc.audit_scc_source_primitive_correspondence_statement`; owner AUD-GR-SCC.
- `audit_scc_source_primitives_correct`: `GraphAuditScc.audit_scc_source_library_obligations`; owner
  AUD-GR-SCC.
- `audit_scc_source_adapted_correct`: `GraphAuditScc.audit_scc_source_adapted_statement`; owner
  AUD-GR-SCC.
- `audit_scc_source_contract_correct`: `GraphAuditScc.audit_scc_source_contract_statement`; owner
  AUD-GR-SCC.

## GraphAuditSemiDominators

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_semi_call` (ind).
- `AuditSemiCase` (constr).
- `AuditSemiGet` (constr).
- `AuditSemiRankGet` (constr).
- `AuditSemiLess` (constr).
- `AuditSemiLe` (constr).
- `AuditSemiSet` (constr).
- `audit_semi_rank_counted` (def).
- `audit_semi_score_counted` (def).
- `audit_semi_label_counted` (def).
- `audit_semi_compress_run` (ind).
- `AuditSemiCompressRoot` (constr).
- `AuditSemiCompressStopped` (constr).
- `AuditSemiCompressRecurNone` (constr).
- `AuditSemiCompressRecurSome` (constr).
- `audit_semi_call_work` (def).
- `audit_semi_compress_work` (def).
- `audit_semi_compress_width` (def).
- `audit_semi_compress_event_bound` (def).
- `audit_semi_compress_budget` (def).
- `audit_semi_compress_statement` (def).
- `audit_semi_compress_unique_statement` (def).
- `audit_semi_outer_call` (ind).
- `AuditSemiOuterCase` (constr).
- `AuditSemiOuterSource` (constr).
- `AuditSemiOuterInner` (constr).
- `AuditSemiOuterTreeGet` (constr).
- `AuditSemiOuterPredGet` (constr).
- `AuditSemiOuterResultSet` (constr).
- `AuditSemiOuterLink` (constr).
- `AuditSemiOuterOutput` (constr).
- `audit_semi_value_counted` (def).
- `audit_semi_predecessor_run` (ind).
- `AuditSemiPredUnnumbered` (constr).
- `AuditSemiPredNumbered` (constr).
- `audit_semi_predecessors_run` (ind).
- `AuditSemiPredsNil` (constr).
- `AuditSemiPredsCons` (constr).
- `audit_semi_settle_run` (ind).
- `AuditSemiSettleRoot` (constr).
- `AuditSemiSettleNode` (constr).
- `audit_semi_settles_run` (ind).
- `AuditSemiSettlesNil` (constr).
- `AuditSemiSettlesCons` (constr).
- `audit_semi_compute_run` (def).
- `audit_semi_outer_event_work` (def).
- `audit_semi_compute_work` (def).
- `audit_semi_compute_input_edges` (def).
- `audit_semi_compute_rank_bound` (def).
- `audit_semi_compute_width` (def).
- `audit_semi_compute_event_bound` (def).
- `audit_semi_compute_input_budget` (def).
- `audit_semi_compute_statement` (def).
- `audit_semi_compute_unique_statement` (def).
- `audit_semi_nested_event` (ind).
- `SemiNestedCase` (constr).
- `SemiNestedVertexMap` (constr).
- `SemiNestedRankMap` (constr).
- `SemiNestedCompare` (constr).
- `audit_semi_nested_rank` (def).
- `audit_semi_nested_score` (def).
- `audit_semi_nested_label` (def).
- `audit_semi_nested_shortcut_set` (def).
- `audit_semi_nested_compress_run` (ind).
- `SemiNestedRoot` (constr).
- `SemiNestedStopped` (constr).
- `SemiNestedRecurNone` (constr).
- `SemiNestedRecurSome` (constr).
- `audit_semi_nested_compress_erasure_statement` (def).
- `audit_semi_nested_compress_unique_statement` (def).
- `audit_semi_nested_event_work` (def).
- `audit_semi_nested_body_event_work` (def).
- `audit_semi_nested_work` (def).
- `audit_semi_nested_body_work` (def).
- `audit_semi_nested_width` (def).
- `audit_semi_nested_input_budget` (def).
- `audit_semi_nested_compress_bound_statement` (def).
- `audit_semi_producer_nested_event` (ind).
- `SemiProducerCase` (constr).
- `SemiProducerSource` (constr).
- `SemiProducerInner` (constr).
- `SemiProducerTreeMap` (constr).
- `SemiProducerPredMap` (constr).
- `SemiProducerOutput` (constr).
- `audit_semi_producer_link` (def).
- `audit_semi_producer_pred_run` (ind).
- `SemiProducerPredMissing` (constr).
- `SemiProducerPredNumbered` (constr).
- `audit_semi_producer_preds_run` (ind).
- `SemiProducerPredsNil` (constr).
- `SemiProducerPredsCons` (constr).
- `audit_semi_producer_settle_run` (ind).
- `SemiProducerSettleRoot` (constr).
- `SemiProducerSettleNode` (constr).
- `audit_semi_producer_settles_run` (ind).
- `SemiProducerSettlesNil` (constr).
- `SemiProducerSettlesCons` (constr).
- `audit_semi_producer_nested_run` (def).
- `audit_semi_producer_nested_erasure_statement` (def).
- `audit_semi_producer_nested_unique_statement` (def).
- `audit_semi_producer_nested_event_work` (def).
- `audit_semi_producer_nested_body_event_work` (def).
- `audit_semi_producer_nested_work` (def).
- `audit_semi_producer_nested_body_work` (def).
- `audit_semi_producer_input_rank` (def).
- `audit_semi_producer_input_edges` (def).
- `audit_semi_producer_input_width` (def).
- `audit_semi_producer_event_bound` (def).
- `audit_semi_producer_input_budget` (def).
- `audit_semi_producer_nested_bound_statement` (def).
- `audit_virtual_semi_run` (def).
- `audit_virtual_semi_erasure_statement` (def).
- `audit_virtual_semi_stage_work` (def).
- `audit_virtual_semi_external_work` (def).

Future proof module: `GraphAuditSemiDominatorsAdequacy`.

- `audit_semi_compress_correct`: `GraphAuditSemiDominators.audit_semi_compress_statement`; owner
  AUD-GR-SEMI.
- `audit_semi_compress_unique`: `GraphAuditSemiDominators.audit_semi_compress_unique_statement`;
  owner AUD-GR-SEMI.
- `audit_semi_compute_correct`: `GraphAuditSemiDominators.audit_semi_compute_statement`; owner
  AUD-GR-SEMI.
- `audit_semi_compute_unique`: `GraphAuditSemiDominators.audit_semi_compute_unique_statement`; owner
  AUD-GR-SEMI.
- `audit_semi_nested_compress_erasure`:
  `GraphAuditSemiDominators.audit_semi_nested_compress_erasure_statement`; owner AUD-GR-SEMI.
- `audit_semi_nested_compress_unique`:
  `GraphAuditSemiDominators.audit_semi_nested_compress_unique_statement`; owner AUD-GR-SEMI.
- `audit_semi_nested_compress_bound`:
  `GraphAuditSemiDominators.audit_semi_nested_compress_bound_statement`; owner AUD-GR-SEMI.
- `audit_semi_producer_nested_erasure`:
  `GraphAuditSemiDominators.audit_semi_producer_nested_erasure_statement`; owner AUD-GR-SEMI.
- `audit_semi_producer_nested_unique`:
  `GraphAuditSemiDominators.audit_semi_producer_nested_unique_statement`; owner AUD-GR-SEMI.
- `audit_semi_producer_nested_bound`:
  `GraphAuditSemiDominators.audit_semi_producer_nested_bound_statement`; owner AUD-GR-SEMI.
- `audit_virtual_semi_erasure_holds`:
  `GraphAuditSemiDominators.audit_virtual_semi_erasure_statement`; owner AUD-GR-SEMI.

## GraphAuditSemiNca

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_nca_walk_run` (ind).
- `AuditNcaThreshold` (constr).
- `AuditNcaNoParent` (constr).
- `AuditNcaStop` (constr).
- `AuditNcaRecur` (constr).
- `audit_nca_walk_width` (def).
- `audit_nca_walk_event_bound` (def).
- `audit_nca_walk_budget` (def).
- `audit_nca_walk_statement` (def).
- `audit_nca_walk_unique_statement` (def).
- `audit_nca_call` (ind).
- `AuditNcaCase` (constr).
- `AuditNcaTreeGet` (constr).
- `AuditNcaSource` (constr).
- `AuditNcaInner` (constr).
- `audit_nca_step_run` (ind).
- `AuditNcaStepRoot` (constr).
- `AuditNcaStepNode` (constr).
- `audit_nca_steps_run` (ind).
- `AuditNcaStepsNil` (constr).
- `AuditNcaStepsCons` (constr).
- `audit_nca_compute_run` (def).
- `audit_nca_event_work` (def).
- `audit_nca_compute_work` (def).
- `audit_nca_compute_event_bound` (def).
- `audit_nca_compute_width` (def).
- `audit_nca_compute_budget` (def).
- `audit_nca_compute_statement` (def).
- `audit_nca_compute_unique_statement` (def).
- `audit_nca_source_event` (ind).
- `NcaSourceCase` (constr).
- `NcaSourceTree` (constr).
- `NcaSourceSource` (constr).
- `NcaSourceInner` (constr).
- `audit_nca_source_walk_run` (ind).
- `NcaSourceThreshold` (constr).
- `NcaSourceNoParent` (constr).
- `NcaSourceStop` (constr).
- `NcaSourceRecur` (constr).
- `audit_nca_source_step_run` (ind).
- `NcaSourceRoot` (constr).
- `NcaSourceNode` (constr).
- `audit_nca_source_steps_run` (ind).
- `NcaSourceStepsNil` (constr).
- `NcaSourceStepsCons` (constr).
- `audit_nca_source_run` (def).
- `audit_nca_source_event_work` (def).
- `audit_nca_source_event_body` (def).
- `audit_nca_source_work` (def).
- `audit_nca_source_body_work` (def).
- `audit_nca_source_input_bound` (def).
- `audit_nca_source_statement` (def).
- `audit_nca_source_unique_statement` (def).

Future proof module: `GraphAuditSemiNcaAdequacy`.

- `audit_nca_walk_correct`: `GraphAuditSemiNca.audit_nca_walk_statement`; owner AUD-GR-SNCA.
- `audit_nca_walk_unique`: `GraphAuditSemiNca.audit_nca_walk_unique_statement`; owner AUD-GR-SNCA.
- `audit_nca_compute_correct`: `GraphAuditSemiNca.audit_nca_compute_statement`; owner AUD-GR-SNCA.
- `audit_nca_compute_unique`: `GraphAuditSemiNca.audit_nca_compute_unique_statement`; owner
  AUD-GR-SNCA.
- `audit_nca_source_holds`: `GraphAuditSemiNca.audit_nca_source_statement`; owner AUD-GR-SNCA.
- `audit_nca_source_unique_holds`: `GraphAuditSemiNca.audit_nca_source_unique_statement`; owner
  AUD-GR-SNCA.

## GraphAuditVirtual

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_virtual_call` (ind).
- `AuditVirtualCase` (constr).
- `AuditVirtualMem` (constr).
- `AuditVirtualAdd` (constr).
- `AuditVirtualOut` (constr).
- `AuditVirtualSource` (constr).
- `AuditVirtualTarget` (constr).
- `AuditVirtualEncode` (constr).
- `AuditVirtualMap` (constr).
- `audit_virtual_entries_counted` (Fixpoint).
- `audit_virtual_out_counted` (def).
- `audit_virtual_source_counted` (def).
- `audit_virtual_target_counted` (def).
- `audit_virtual_encode_counted` (def).
- `audit_virtual_prepare_callbacks` (def).
- `audit_virtual_dfs_callbacks` (def).
- `audit_virtual_callbacks_statement` (def).
- `audit_virtual_search_with_prepared` (def).
- `audit_virtual_search_counted` (def).
- `audit_virtual_search_statement` (def).
- `audit_virtual_event_work` (def).
- `audit_virtual_entries_work` (def).
- `audit_virtual_entries_width` (def).
- `audit_virtual_entries_budget` (def).
- `audit_virtual_entries_statement` (def).
- `audit_virtual_search_work` (def).
- `audit_virtual_search_budget` (def).
- `audit_virtual_search_bound_statement` (def).
- `audit_erase_call` (ind).
- `AuditEraseCase` (constr).
- `AuditEraseElements` (constr).
- `AuditEraseSet` (constr).
- `audit_erase_rows_counted` (Fixpoint).
- `audit_erase_virtual_counted` (def).
- `audit_erase_nodes_ne` (Fixpoint).
- `audit_erase_nodes` (def).
- `audit_erase_event_work` (def).
- `audit_erase_virtual_work` (def).
- `audit_erase_width` (def).
- `audit_erase_event_bound` (def).
- `audit_erase_virtual_budget` (def).
- `audit_erase_virtual_statement` (def).
- `audit_erase_nested_event` (ind).
- `EraseNestedCase` (constr).
- `EraseNestedElements` (constr).
- `EraseNestedSet` (constr).
- `audit_erase_nested_rows` (Fixpoint).
- `audit_erase_virtual_nested` (def).
- `audit_erase_nested_event_work` (def).
- `audit_erase_nested_body_event_work` (def).
- `audit_erase_nested_work` (def).
- `audit_erase_nested_body_work` (def).
- `audit_erase_nested_width` (def).
- `audit_erase_nested_budget` (def).
- `audit_erase_nested_statement` (def).
- `audit_virtual_entries_full_event` (ind).
- `VirtualEntriesCase` (constr).
- `VirtualEntriesSet` (constr).
- `audit_virtual_entries_full_counted` (Fixpoint).
- `audit_virtual_entries_full_internal_event_work` (def).
- `audit_virtual_entries_full_body_event_work` (def).
- `audit_virtual_entries_full_internal_work` (def).
- `audit_virtual_entries_full_body_work` (def).
- `audit_virtual_entries_full_width` (def).
- `audit_virtual_entries_full_budget` (def).
- `audit_virtual_entries_full_statement` (def).
- `audit_virtual_entries_full_total_statement` (def).
- `audit_virtual_base_callbacks` (rec).
- `audit_virtual_base_out` (proj).
- `audit_virtual_base_target` (proj).
- `audit_virtual_base_encode` (proj).
- `audit_virtual_full_call` (ind).
- `VirtualFullCase` (constr).
- `VirtualFullOut` (constr).
- `VirtualFullTarget` (constr).
- `VirtualFullSource` (constr).
- `VirtualFullEncode` (constr).
- `VirtualFullEntry` (constr).
- `VirtualFullMap` (constr).
- `audit_virtual_base_callbacks_erase` (def).
- `audit_virtual_full_out` (def).
- `audit_virtual_full_target` (def).
- `audit_virtual_full_source` (def).
- `audit_virtual_full_source_statement` (def).
- `audit_virtual_full_encode` (def).
- `audit_virtual_full_prepare_callbacks` (def).
- `audit_virtual_full_dfs_callbacks` (def).
- `audit_virtual_full_callbacks_statement` (def).
- `audit_virtual_full_search_with_prepared` (def).
- `audit_virtual_full_search_counted` (def).
- `audit_virtual_full_search_statement` (def).
- `audit_virtual_full_internal_event_work` (def).
- `audit_virtual_full_body_event_work` (def).
- `audit_virtual_full_events_body_work` (def).
- `audit_virtual_full_search_input_budget` (def).
- `audit_virtual_source_search` (def).
- `audit_virtual_source_search_budget` (def).
- `audit_virtual_source_search_statement` (def).
- `AuditVirtualBaseCallbacks` (record-constructor).

Future proof module: `GraphAuditVirtualAdequacy`.

- `audit_virtual_callbacks_correct`: `GraphAuditVirtual.audit_virtual_callbacks_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_virtual_search_correct`: `GraphAuditVirtual.audit_virtual_search_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_virtual_entries_correct`: `GraphAuditVirtual.audit_virtual_entries_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_virtual_search_bound`: `GraphAuditVirtual.audit_virtual_search_bound_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_erase_virtual_correct`: `GraphAuditVirtual.audit_erase_virtual_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_erase_nested_correct`: `GraphAuditVirtual.audit_erase_nested_statement`; owner
  AUD-GR-VIRTUAL.
- `audit_virtual_entries_full_correct`: `GraphAuditVirtual.audit_virtual_entries_full_statement`;
  owner AUD-GR-VIRTUAL.
- `audit_virtual_entries_full_total_holds`:
  `GraphAuditVirtual.audit_virtual_entries_full_total_statement`; owner AUD-GR-VIRTUAL.
- `audit_virtual_full_source_correct`: `GraphAuditVirtual.audit_virtual_full_source_statement`;
  owner AUD-GR-VIRTUAL.
- `audit_virtual_full_callbacks_correct`:
  `GraphAuditVirtual.audit_virtual_full_callbacks_statement`; owner AUD-GR-VIRTUAL.
- `audit_virtual_full_search_correct`: `GraphAuditVirtual.audit_virtual_full_search_statement`;
  owner AUD-GR-VIRTUAL.
- `audit_virtual_source_search_holds`: `GraphAuditVirtual.audit_virtual_source_search_statement`;
  owner AUD-GR-VIRTUAL.

## GraphAuditVirtualAdapter

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_virtual_adapter_call_budget` (def).
- `audit_virtual_source_search_adapted_statement` (def).

Future proof module: `GraphAuditVirtualAdapterAdequacy`.

- `audit_virtual_source_search_adapted_holds`:
  `GraphAuditVirtualAdapter.audit_virtual_source_search_adapted_statement`; owner AUD-GR-VIRTUAL.

## GraphAuditWto

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `audit_wto_call` (ind).
- `AuditWtoCase` (constr).
- `AuditWtoDfs` (constr).
- `AuditWtoScc` (constr).
- `AuditWtoRead` (constr).
- `AuditWtoEdges` (constr).
- `AuditWtoWrite` (constr).
- `AuditWtoSucc` (constr).
- `AuditWtoLe` (constr).
- `AuditWtoEncode` (constr).
- `AuditWtoTarget` (constr).
- `AuditWtoEqual` (constr).
- `AuditWtoDepth` (constr).
- `AuditWtoOutput` (constr).
- `audit_wto_ranks_counted` (Fixpoint).
- `audit_wto_earlier_counted` (def).
- `audit_wto_choose_counted` (Fixpoint).
- `audit_wto_remove_counted` (Fixpoint).
- `audit_wto_self_edges` (Fixpoint).
- `audit_wto_component_counted` (def).
- `audit_wto_components_counted` (Fixpoint).
- `audit_wto_layer_counted` (def).
- `audit_wto_iter_event` (def).
- `audit_wto_counted` (def).
- `audit_wto_event_work` (def).
- `audit_wto_model_work` (def).
- `audit_wto_input_order_bound` (def).
- `audit_wto_input_max_out` (def).
- `audit_wto_input_event_bound` (def).
- `audit_wto_input_budget` (def).
- `audit_wto_counted_statement` (def).
- `audit_wto_nested_event` (def).
- `audit_wto_nested_ranks` (Fixpoint).
- `audit_wto_nested_earlier` (def).
- `audit_wto_nested_choose` (Fixpoint).
- `audit_wto_nested_remove` (Fixpoint).
- `audit_wto_nested_self_edges` (Fixpoint).
- `audit_wto_nested_component` (def).
- `audit_wto_nested_components` (Fixpoint).
- `audit_wto_nested_layer` (def).
- `audit_wto_nested_counted` (def).
- `audit_wto_nested_body_work` (def).
- `audit_wto_nested_total_work` (def).
- `audit_wto_nested_statement` (def).
- `audit_wto_source_layer` (def).
- `audit_wto_source_counted` (def).
- `audit_wto_source_event_work` (def).
- `audit_wto_source_work` (def).
- `audit_wto_source_body_work` (def).
- `audit_wto_source_budget` (def).
- `audit_wto_source_statement` (def).
- `audit_wto_source_external_budget` (def).
- `audit_wto_source_event_wellformed` (def).
- `audit_wto_source_event_primitive` (def).
- `audit_wto_source_event_correspondence_statement` (def).
- `audit_wto_source_adapted_statement` (def).
- `audit_wto_source_contract_statement` (def).

Future proof module: `GraphAuditWtoAdequacy`.

- `audit_wto_counted_correct`: `GraphAuditWto.audit_wto_counted_statement`; owner AUD-GR-WTO.
- `audit_wto_nested_holds`: `GraphAuditWto.audit_wto_nested_statement`; owner AUD-GR-WTO.
- `audit_wto_source_holds`: `GraphAuditWto.audit_wto_source_statement`; owner AUD-GR-WTO.
- `audit_wto_source_event_correspondence_holds`:
  `GraphAuditWto.audit_wto_source_event_correspondence_statement`; owner AUD-GR-WTO.
- `audit_wto_source_adapted_holds`: `GraphAuditWto.audit_wto_source_adapted_statement`; owner
  AUD-GR-WTO.
- `audit_wto_source_contract_holds`: `GraphAuditWto.audit_wto_source_contract_statement`; owner
  AUD-GR-WTO.

<!-- AUD-API-GR-SQ-NAMES-END -->

<!-- AUD-API-NUM-NAMES-BEGIN -->

# NUM audit names

## AnalysesAuditScevCost

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-BASE

- `floor_source_frame_weight` (def).
- `floor_sum_frame_weight` (def).
- `count_frame_weight` (def).
- `count_input_size` (def).

## AnalysesAuditScevFast

Public package: `Galois.Analyses`.

Card: AUD-SA

- `nw_event` (ind).
- `NwModulus` (constr).
- `NwCompare` (constr).
- `NwAdd` (constr).
- `NwSub` (constr).
- `NwNeg` (constr).
- `NwMul` (constr).
- `NwDiv` (constr).
- `NwRem` (constr).
- `NwToN` (constr).
- `nw_guard` (def).
- `nw_fast` (def).
- `scev_nowrap_fast` (def).
- `nw_trip` (def).
- `scev_nowrap_probe_sound_type` (def).
- `scev_nowrap_fast_agrees_type` (def).
- `scev_unsigned_unit_lt_type` (def).
- `scev_nowrap_trip_agrees_type` (def).
- `scev_nowrap_trip_no_exit_type` (def).
- `scev_nowrap_unit_no_fallback_type` (def).

## AnalysesAuditScevFastLegacy

Public package: `Galois.Analyses`.

Card: AUD-SA

- `nw_guard_lean_legacy_agrees_type` (def).
- `scev_nowrap_fast_lean_legacy_agrees_type` (def).

## AnalysesAuditScevFastSource

Public package: `Galois.Analyses`.

Card: AUD-SA

- `scalar_compare` (def).
- `scalar_view` (def).
- `scalar_predicate` (def).
- `scalar_one` (def).
- `scalar_search` (Fixpoint).
- `scalar_fallback` (def).
- `scalar_guard` (def).
- `scev_nowrap_source` (def).
- `nw_guard_lean` (def).
- `scev_nowrap_fast_lean` (def).
- `scalar_guard_lean_erases_type` (def).
- `scev_nowrap_source_lean_erases_type` (def).
- `scalar_frame_weight` (def).
- `scalar_source_work` (def).
- `scalar_predicate_erases_type` (def).
- `scalar_fallback_erases_type` (def).
- `scev_nowrap_source_erases_type` (def).
- `scalar_search_counts_type` (def).
- `scev_nowrap_source_bound_type` (def).
- `scev_nowrap_source_unit_type` (def).

## AnalysesAuditScevFloorGe

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-FLOOR

- `floor_ge_prefix` (def).
- `floor_ge_projection` (def).
- `floor_ge_suffix` (def).
- `floor_ge_run` (ind).
- `FloorGeRun` (constr).
- `audit_floor_ge_traced` (def).
- `audit_floor_ge_source_correct_type` (def).
- `audit_floor_ge_source_total_type` (def).
- `audit_floor_ge_calls_exact_type` (def).
- `audit_floor_ge_weight_bound_type` (def).

## AnalysesAuditScevFloorIter

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-ITER

- `floor_tick_source_budget` (def).
- `floor_iter_run` (ind).
- `FloorIterOne` (constr).
- `FloorIterEven` (constr).
- `FloorIterOdd` (constr).
- `audit_floor_iter_counted` (Fixpoint).
- `audit_floor_iter_source_correct_type` (def).
- `audit_floor_iter_source_total_type` (def).
- `audit_floor_iter_ticks_exact_type` (def).
- `audit_floor_iter_source_count_type` (def).
- `audit_floor_iter_overhead_bounded_type` (def).
- `audit_floor_iter_source_weight_type` (def).

## AnalysesAuditScevFloorSum

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-FLOOR

- `floor_sum_zero_events` (def).
- `floor_sum_prefix` (def).
- `floor_sum_suffix` (def).
- `floor_sum_weight` (def).
- `floor_sum_run` (ind).
- `FloorSumZero` (constr).
- `FloorSumFuelZero` (constr).
- `FloorSumPositive` (constr).
- `audit_floor_sum_traced` (def).
- `audit_floor_sum_source_correct_type` (def).
- `audit_floor_sum_source_total_type` (def).
- `audit_floor_sum_fuel_positive_type` (def).
- `audit_floor_sum_tick_count_type` (def).
- `audit_floor_sum_weight_bound_type` (def).

## AnalysesAuditScevFloorTick

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-TICK

- `floor_strict_event` (ind).
- `FloorProjection` (constr).
- `FloorBranch` (constr).
- `FloorPred` (constr).
- `FloorSucc` (constr).
- `FloorAdd` (constr).
- `FloorMul` (constr).
- `FloorDiv` (constr).
- `FloorMod` (constr).
- `FloorCompare` (constr).
- `FloorConstruct` (constr).
- `floor_bool` (def).
- `floor_active_prefix` (def).
- `floor_finish_output` (def).
- `floor_continue_output` (def).
- `floor_strict_run` (ind).
- `FloorRunDone` (constr).
- `FloorRunFinish` (constr).
- `FloorRunContinue` (constr).
- `floor_tick_counted` (def).
- `floor_tick_correspondence_type` (def).
- `floor_tick_total_type` (def).
- `floor_tick_count_type` (def).
- `floor_shared_event` (def).
- `floor_shared_run` (def).
- `floor_source_weight` (def).
- `floor_input_size` (def).
- `audit_floor_tick_counted` (def).
- `floor_payload_cells` (def).
- `floor_instrumentation_work` (def).
- `audit_floor_tick_source_correct_type` (def).
- `audit_floor_tick_source_total_type` (def).
- `audit_floor_tick_source_count_type` (def).
- `audit_floor_tick_source_counts_exact_type` (def).
- `audit_floor_tick_instrumentation_bound_type` (def).
- `audit_floor_tick_instrumentation_exact_type` (def).
- `audit_floor_tick_source_weight_type` (def).

## AnalysesAuditScevMod

Public package: `Galois.Analyses`.

Card: AUD-SM-HIT

- `mod_probe_trace` (def).
- `scev_mod_first_hit_agrees_type` (def).
- `audit_mod_period_positive_type` (def).
- `audit_mod_period_size_type` (def).
- `scev_mod_no_exit_type` (def).
- `scev_mod_first_hit_count_type` (def).
- `scev_mod_trip` (def).
- `scev_mod_trip_agrees_type` (def).
- `scev_mod_even_no_exit_type` (def).
- `audit_mod_even_no_fallback_type` (def).
- `audit_mod_one_bit_fallback_type` (def).

## AnalysesAuditScevModCount

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT

- `count_zencode_correct_type` (def).
- `count_normalize` (def).
- `scev_mod_count_traced` (def).
- `count_source_work` (def).
- `count_source_budget` (def).
- `scev_mod_count_traced_erases_type` (def).
- `scev_mod_count_source_correspondence_type` (def).
- `count_whole_run` (ind).
- `CountWholeLt` (constr).
- `CountWholeLe` (constr).
- `CountWholeNe` (constr).
- `count_normalize_erases_type` (def).
- `scev_mod_count_whole_correspondence_type` (def).
- `scev_mod_count_whole_total_type` (def).
- `scev_mod_count_whole_unique_type` (def).
- `scev_mod_count_floor_calls_type` (def).
- `scev_mod_count_source_bound_type` (def).

## AnalysesAuditScevModCountPlain

Public package: `Galois.Analyses`.

Card: AUD-SM-COUNT-BASE

- `audit_floor_sum_reference` (def).
- `audit_floor_state` (rec).
- `audit_floor_n` (proj).
- `audit_floor_m` (proj).
- `audit_floor_a` (proj).
- `audit_floor_b` (proj).
- `audit_floor_acc` (proj).
- `audit_floor_done` (proj).
- `audit_floor_updates` (proj).
- `audit_floor_step` (def).
- `audit_floor_sum_counted` (def).
- `audit_floor_state_bits` (def).
- `audit_floor_sum_fast` (def).
- `audit_count_ge` (def).
- `scev_mod_count` (def).
- `audit_failed_indices` (def).
- `scev_mod_count_exact_type` (def).
- `audit_floor_sum_fast_correct_type` (def).
- `audit_floor_sum_terminates_type` (def).
- `audit_floor_live_bits_type` (def).
- `audit_floor_sum_zero_type` (def).

## AnalysesAuditScevModPlain

Public package: `Galois.Analyses`.

Card: AUD-SM-HIT

- `audit_mod_period` (def).
- `mod_hit_tick` (def).
- `mod_probe` (def).
- `scev_mod_first_hit` (def).

## AnalysesAuditScevModSource

Public package: `Galois.Analyses`.

Card: AUD-SM-HIT

- `hit_query` (def).
- `hit_tick` (def).
- `hit_iter` (Fixpoint).
- `hit_probe_source` (def).
- `scev_mod_first_hit_source` (def).
- `hit_frame_weight` (def).
- `hit_source_work` (def).
- `scev_mod_first_hit_source_erases_type` (def).
- `hit_source_width_one_type` (def).
- `hit_period_size_type` (def).
- `hit_source_queries_type` (def).
- `hit_source_bound_type` (def).
- `hit_source_even_no_fallback_type` (def).
- `mod_probe_plain_erases_type` (def).
- `mod_first_hit_plain_erases_type` (def).

## AnalysesAuditScevRecognize

Public package: `Galois.Analyses`.

Card: AUD-SR

- `recognize_check` (def).
- `recognize_sound_type` (def).
- `recognize_cache_type` (def).
- `scev_extra_recognize_sound_type` (def).
- `scev_extra_cache_valid_type` (def).

## AnalysesAuditScevRecognizeCheck

Public package: `Galois.Analyses`.

Card: AUD-SR-CHECK

- `sr_check_call` (ind).
- `SrCheckClosure` (constr).
- `SrCheckEncodeNode` (constr).
- `SrCheckBody` (constr).
- `SrCheckAdd` (constr).
- `SrCheckMul` (constr).
- `SrCheckConstant` (constr).
- `SrCheckSupport` (constr).
- `SrCheckNatural` (constr).
- `check_measure` (def).
- `check_run` (def).
- `check_return` (def).
- `check_bind` (def).
- `check_lift` (def).
- `check_get` (def).
- `check_code_get` (def).
- `check_code_set` (def).
- `check_body` (def).
- `check_flag` (def).
- `check_key` (def).
- `check_node_key` (def).
- `check_union` (def).
- `check_add` (def).
- `check_mem` (def).
- `check_binary` (def).
- `check_constant` (def).
- `check_phi_before` (def).
- `check_context_entry` (def).
- `check_context` (def).
- `check_store` (def).
- `sr_check_expr_source` (Fixpoint).
- `check_update_gate` (def).
- `check_argument_get` (def).
- `check_binding_gate` (def).
- `sr_check_binding_source` (def).
- `sr_check_bindings_source` (Fixpoint).
- `sr_check_dependencies_source` (Fixpoint).
- `sr_check_plan_source` (def).
- `sr_check_plan_source_erases_type` (def).

## AnalysesAuditScevRecognizePlain

Public package: `Galois.Analyses`.

Card: AUD-SR-CLOSURE

- `scev_iexpr_equal_lean` (Fixpoint).
- `scev_chrec_equal_lean` (Fixpoint).
- `scev_lookup_equal_lean` (def).
- `scev_captured_context_lean` (def).
- `scev_captured_store_lean` (def).
- `scev_captured_compile_lean` (Fixpoint).
- `scev_captured_bindings_lean` (Fixpoint).
- `scev_captured_plan_lean` (def).
- `scev_lookup_equal_lean_agrees_statement` (def).
- `scev_captured_compile_lean_erases_statement` (def).
- `scev_extra_recognize` (def).
- `scev_extra_recognize_agrees_statement` (def).

## AnalysesAuditScevRecognizeSource

Public package: `Galois.Analyses`.

Card: AUD-SR

- `sr_producer_call` (ind).
- `SrProducerCheck` (constr).
- `SrProducerHome` (constr).
- `SrProducerDefinition` (constr).
- `SrProducerArguments` (constr).
- `SrProducerCode` (constr).
- `SrProducerSupport` (constr).
- `SrProducerAdvance` (constr).
- `SrProducerCommand` (constr).
- `producer_run` (def).
- `producer_return` (def).
- `producer_mark` (def).
- `producer_bind` (def).
- `producer_lift` (def).
- `producer_get` (def).
- `producer_set` (def).
- `producer_mem` (def).
- `producer_remove` (def).
- `producer_add` (def).
- `producer_argument_get` (def).
- `producer_code` (def).
- `producer_encode` (def).
- `producer_prepare_binary` (def).
- `producer_prepare_expr` (Fixpoint).
- `producer_complete_leaf` (def).
- `producer_complete_binary` (def).
- `producer_finish` (def).
- `producer_expand_phi` (def).
- `producer_expand_value` (def).
- `producer_advance` (Fixpoint).
- `producer_iterate` (Fixpoint).
- `producer_advance_erases_type` (def).
- `producer_prepare_expr_erases_type` (def).
- `producer_inventory` (Fixpoint).
- `producer_arguments` (Fixpoint).
- `producer_ranks` (Fixpoint).
- `producer_prepare_index` (def).
- `producer_compile_bindings` (Fixpoint).
- `producer_compile_plan` (def).
- `scev_extra_recognize_source` (def).
- `scev_extra_recognize_source_erases_type` (def).
- `sr_iexpr_width` (Fixpoint).
- `sr_chrec_width` (Fixpoint).
- `sr_support_width` (def).
- `sr_closure_width` (def).
- `sr_check_width` (def).
- `sr_actual_operand_width` (def).
- `scev_extra_recognize_source_bound_type` (def).
- `producer_source_counts_type` (def).
- `scev_extra_recognize_source_total_type` (def).
- `scev_extra_recognize_source_unique_type` (def).
- `sr_external_callback` (def).
- `sr_external_body_work` (def).

## AnalysesAuditScevRecognizeTrace

Public package: `Galois.Analyses`.

Card: AUD-SR-CLOSURE

- `sr_closure_call` (ind).
- `SrClosureEncode` (constr).
- `SrClosureCode` (constr).
- `SrClosureTrees` (constr).
- `SrClosureSupport` (constr).
- `sr_measure` (def).
- `sr_run` (def).
- `sr_return` (def).
- `sr_bind` (def).
- `sr_get` (def).
- `sr_set` (def).
- `sr_code_get` (def).
- `sr_code_set` (def).
- `sr_iexpr_equal` (Fixpoint).
- `sr_chrec_equal` (Fixpoint).
- `sr_lookup_equal` (def).
- `sr_compiler_memo` (rec).
- `src_entries` (proj).
- `src_hits` (proj).
- `src_misses` (proj).
- `sr_compiler_empty` (def).
- `sr_context_entry` (def).
- `sr_child_work` (def).
- `sr_fold_calls` (def).
- `sr_context_source` (def).
- `sr_compiler_store` (def).
- `sr_compiler_reuse` (def).
- `sr_add_invariant_work` (Fixpoint).
- `sr_add_work` (Fixpoint).
- `sr_mul_invariant_work` (Fixpoint).
- `sr_mul_work` (Fixpoint).
- `sr_compile_expr_source` (Fixpoint).
- `sr_compiler_memo_erases` (def).
- `sr_lookup_equal_erases_type` (def).
- `sr_compile_expr_source_erases_type` (def).

## AnalysesAuditScevTrip

Public package: `Galois.Analyses`.

Card: AUD-SM-HIT

- `trip_client_source` (def).
- `trip_callback_work` (def).
- `trip_library_work` (def).
- `trip_iexpr_nodes` (Fixpoint).
- `trip_chrec_nodes` (Fixpoint).
- `trip_max_operand_bits` (def).
- `trip_client_source_erases_type` (def).
- `trip_expression_source_bound_type` (def).
- `trip_client_source_bound_type` (def).

## AnalysesAuditScevTripScalar

Public package: `Galois.Analyses`.

Card: AUD-SA

- `trip_event` (ind).
- `TripInvariant` (constr).
- `TripSource` (constr).
- `trip_iexpr_source` (Fixpoint).
- `trip_chrec_zero_source` (Fixpoint).
- `trip_nowrap_client_source` (def).
- `trip_nowrap_library_work` (def).
- `trip_nowrap_source_erases_type` (def).
- `trip_scalar_expr_nodes` (Fixpoint).
- `trip_scalar_chain_nodes` (Fixpoint).
- `trip_scalar_operand_bits` (def).
- `trip_nowrap_source_bound_type` (def).

## DomainsAuditKnownBitsSource

Public package: `Galois.Domains`.

Card: AUD-DOM-BASE

- `kb_mark` (def).
- `kb_unary` (def).
- `kb_half` (def).
- `kb_signed` (def).
- `kb_msb` (def).
- `kb_wctz` (def).
- `kb_wrotl` (def).
- `kb_word_shift` (def).
- `kb_scalar_value` (def).
- `kb_map` (def).
- `kb_scalar` (def).
- `kb_not` (def).
- `kb_bitop` (def).
- `kb_constant` (def).
- `kb_sub` (def).
- `kb_trailing` (def).
- `kb_classic_mul` (def).
- `kb_bitlen` (def).
- `kb_upper` (def).
- `kb_stride` (def).
- `kb_expand` (Fixpoint).
- `kb_expand_mask` (def).
- `kb_variable_raw` (def).
- `kb_variable` (def).
- `kb_order` (def).
- `kb_equal` (def).
- `kb_bias` (def).
- `kb_compare` (def).
- `kb_concat` (def).
- `kb_unary_map` (def).
- `kb_forward_raw_source` (def).
- `kb_any_empty_source` (Fixpoint).
- `kb_forward_source` (def).
- `kb_frame_weight` (def).
- `kb_source_work` (def).
- `kb_forward_source_erases_type` (def).
- `kb_empty_scan_source_count_type` (def).

## DomainsAuditMul

Public package: `Galois.Domains`.

Card: AUD-DM

- `audit_mul_sound_type` (def).
- `audit_mul_meet_intersection_type` (def).
- `audit_mul_meet_sound_type` (def).
- `audit_mul_constants_type` (def).
- `audit_mul_bottom_type` (def).
- `audit_mul_width_type` (def).
- `audit_mul_meet_constants_type` (def).
- `audit_mul_meet_bottom_type` (def).
- `audit_mul_meet_width_type` (def).
- `audit_mul_word_laws_type` (def).
- `audit_mul_meet_word_laws_type` (def).
- `audit_mul_active_bits` (def).
- `audit_mul_active_bits_bound_type` (def).
- `audit_mul_counted_bounds_type` (def).
- `audit_mul_steps_exact_type` (def).

## DomainsAuditMulDispatch

Public package: `Galois.Domains`.

Card: AUD-DM

- `domain_positive_eq` (def).
- `domain_positive_le` (def).
- `mul_precise_forward_source` (def).
- `mul_dispatch_source` (def).
- `mul_dispatch_weight` (def).
- `mul_dispatch_work` (def).
- `mul_precise_forward_erases_type` (def).
- `mul_dispatch_fallback_type` (def).
- `mul_dispatch_total_type` (def).
- `mul_dispatch_unique_type` (def).
- `mul_dispatch_source_bound_type` (def).

## DomainsAuditMulPlain

Public package: `Galois.Domains`.

Card: AUD-DM

- `audit_mul_work` (rec).
- `audit_mul_steps` (proj).
- `audit_mul_tests` (proj).
- `audit_mul_additions` (proj).
- `audit_mul_shifts` (proj).
- `audit_mul_products` (proj).
- `audit_mul_update` (def).
- `audit_mul_stage` (def).
- `audit_mul_counted` (def).
- `audit_mul` (def).
- `audit_mul_meet` (def).
- `audit_mul_forward` (def).
- `audit_mul_selected_domain` (def).
- `audit_mul_domain` (def).
- `audit_mul_meet_domain` (def).

## DomainsAuditMulSource

Public package: `Galois.Domains`.

Card: AUD-DM

- `mul_stats` (rec).
- `mul_steps` (proj).
- `mul_tests` (proj).
- `mul_adds` (proj).
- `mul_shifts` (proj).
- `mul_products` (proj).
- `mul_zero` (def).
- `mul_succ` (def).
- `mul_field` (def).
- `mul_update_stats` (def).
- `mul_uncertainty` (def).
- `mul_stage` (def).
- `audit_mul_counted_source` (def).
- `mul_dom8_stage` (def).
- `mul_dom8_source` (def).
- `audit_mul_meet_source` (def).
- `mul_input_size` (def).
- `mul_dom8_source_erases_type` (def).
- `audit_mul_source_counts_type` (def).
- `audit_mul_source_bound_type` (def).
- `audit_mul_counted_plain_erases_type` (def).
- `audit_mul_meet_plain_erases_type` (def).

## DomainsAuditNumericCost

Public package: `Galois.Domains`.

Card: AUD-DOM-BASE

- `domain_run` (def).
- `domain_bind` (def).
- `domain_return` (def).
- `domain_tell` (def).
- `domain_case` (def).
- `domain_zop` (ind).
- `DzAdd` (constr).
- `DzSub` (constr).
- `DzMul` (constr).
- `DzDiv` (constr).
- `DzMod` (constr).
- `DzAnd` (constr).
- `DzOr` (constr).
- `DzXor` (constr).
- `DzMin` (constr).
- `DzMax` (constr).
- `DzPow` (constr).
- `domain_zop_site` (def).
- `domain_z` (def).
- `domain_not` (def).
- `domain_compare` (def).
- `domain_equal` (def).
- `domain_testbit` (def).
- `domain_b2z` (def).
- `domain_modulus` (def).
- `domain_wrap` (def).
- `domain_wnot` (def).
- `domain_word_bits` (def).
- `domain_zeros` (def).
- `domain_ones` (def).
- `domain_tnum` (def).
- `domain_const` (def).
- `domain_normalise` (def).
- `domain_tnum_bits` (def).
- `domain_min` (def).
- `domain_max` (def).
- `domain_mask` (def).
- `domain_empty` (def).
- `domain_bottom` (def).
- `domain_subset` (def).
- `domain_order` (def).
- `domain_uncertain` (def).
- `domain_adc` (def).
- `domain_wshl` (def).
- `domain_shift` (def).
- `domain_auxiliary_frame_weight` (def).
- `domain_frame_weight` (def).
- `domain_work` (def).
- `domain_piter` (Fixpoint).
- `domain_iter` (def).
- `domain_helpers_erases_type` (def).
- `domain_helpers_full_erases_type` (def).

## DomainsAuditNumericDimensions

Public package: `Galois.Domains`.

Card: AUD-DOM-BASE

- `numeric_operator_dimension` (def).
- `numeric_tnum_dimension` (def).
- `numeric_kb_dimension` (def).
- `numeric_envelope` (def).
- `kb_forward_source_bound_type` (def).
- `kb_classic_mul_source_bound_type` (def).
- `kb_source_total_type` (def).
- `kb_source_unique_type` (def).

## DomainsAuditProductSource

Public package: `Galois.Domains`.

Card: AUD-DR-PRODUCT

- `product_offset_source` (def).
- `product_wrapped_norm_source` (def).
- `product_wrapped_order_source` (def).
- `product_depth_source` (Fixpoint).
- `product_tree_source` (def).
- `product_odd_source` (def).
- `product_free_source` (def).
- `product_ceiling_source` (Fixpoint).
- `product_tnum_ceiling_source` (def).
- `product_tnum_not_source` (def).
- `product_tnum_floor_source` (def).
- `product_linear_source` (def).
- `product_arc_source` (def).
- `product_pack_source` (Fixpoint).
- `product_prefix_test_source` (def).
- `product_prefix_source` (def).
- `product_arc_bits_source` (def).
- `product_bits_round_source` (def).
- `product_frame_weight` (def).
- `product_work` (def).
- `product_bits_round_source_erases_type` (def).
- `product_pack_depth_bound_type` (def).
- `product_bits_round_source_bound_type` (def).

## DomainsAuditReduce

Public package: `Galois.Domains`.

Card: AUD-DR

- `audit_exchange` (rec).
- `audit_exchange_step` (proj).
- `audit_exchange_rank` (proj).
- `audit_exchange_laws` (rec).
- `audit_exchange_descends` (proj).
- `audit_exchange_monotone` (proj).
- `audit_exchange_gamma` (proj).
- `audit_exchange_progress` (proj).
- `audit_reduce_loop` (Fixpoint).
- `audit_reduce` (def).
- `audit_reduce_gamma_type` (def).
- `audit_reduce_stable_type` (def).
- `audit_reduce_rank_type` (def).
- `audit_reduce_word_laws_type` (def).

## DomainsAuditReduceBits

Public package: `Galois.Domains`.

Card: AUD-DR

- `reduce_bits_rank` (def).
- `reduce_bits_exchange` (def).
- `reduce_bits_exchange_laws_type` (def).
- `audit_reduce_bits` (def).
- `reduce_bits_compare_source` (def).
- `reduce_bits_rank_source` (def).
- `reduce_bits_call_work` (def).
- `audit_reduce_bits_source` (def).
- `reduce_bits_whole_work` (def).
- `reduce_bits_rank_source_erases_type` (def).
- `audit_reduce_bits_source_erases_type` (def).
- `audit_reduce_bits_plain_erases_type` (def).
- `audit_reduce_bits_source_bound_type` (def).

## DomainsAuditReduceSource

Public package: `Galois.Domains`.

Card: AUD-DR

- `reduce_call` (ind).
- `ReduceRankCall` (constr).
- `ReduceStepCall` (constr).
- `ReduceLeftCall` (constr).
- `ReduceRightCall` (constr).
- `reduce_compare_source` (def).
- `reduce_tick_source` (def).
- `reduce_loop_source` (Fixpoint).
- `audit_reduce_source` (def).
- `reduce_loop_reference` (Fixpoint).
- `audit_reduce_source_erases_type` (def).
- `reduce_step_calls` (def).
- `audit_reduce_source_calls_type` (def).
- `reduce_client_body_work` (def).
- `reduce_library_work` (def).
- `audit_reduce_source_bound_type` (def).
- `reduce_plain_erases_type` (def).

## DomainsAuditTransfer

Public package: `Galois.Domains`.

Card: AUD-DT

- `audit_div_one_guard` (def).
- `audit_div_one_forward` (def).
- `audit_div_one_domain` (def).
- `audit_transfer_sound_type` (def).
- `audit_div_one_fallback_type` (def).
- `audit_div_one_refines_type` (def).
- `audit_div_one_laws_type` (def).
- `audit_transfer_shapes_type` (def).
- `audit_dividend` (def).
- `audit_divisor` (def).
- `audit_existing_division` (def).
- `audit_div_one_strict_type` (def).

## DomainsAuditTransferBounds

Public package: `Galois.Domains`.

Card: AUD-DT

- `numeric_bound_dimension` (def).
- `numeric_interval_dimension` (def).
- `numeric_wrapped_dimension` (def).
- `numeric_word_dimension` (def).
- `numeric_iv_dimension` (def).
- `numeric_wr_dimension` (def).
- `numeric_sb_dimension` (def).
- `word_eval_source_bound_type` (def).
- `iv_forward_source_bound_type` (def).
- `wr_forward_source_bound_type` (def).
- `sb_forward_source_bound_type` (def).
- `transfer_source_bound_type` (def).
- `transfer_guard_source_bound_type` (def).
- `transfer_whole_execution_type` (def).
- `iv_source_total_type` (def).
- `iv_source_unique_type` (def).
- `wr_source_total_type` (def).
- `wr_source_unique_type` (def).

## DomainsAuditTransferInterval

Public package: `Galois.Domains`.

Card: AUD-DT-INTERVAL

- `iv_mark` (def).
- `iv_finite` (def).
- `iv_make` (def).
- `iv_top` (def).
- `iv_bound_le` (def).
- `iv_bound_pick` (def).
- `iv_meet` (def).
- `iv_join` (def).
- `iv_checked` (def).
- `iv_add` (def).
- `iv_sub` (def).
- `iv_add_mod` (def).
- `iv_mul` (def).
- `iv_neg` (def).
- `iv_not` (def).
- `iv_and` (def).
- `iv_mask` (def).
- `iv_or` (def).
- `iv_udiv` (def).
- `iv_urem` (def).
- `iv_shift` (def).
- `iv_concat` (def).
- `iv_rewrap` (def).
- `iv_truth` (def).
- `iv_bool_not` (def).
- `iv_compare` (def).
- `iv_eq` (def).
- `iv_signed` (def).
- `iv_sign` (def).
- `iv_sext` (def).
- `iv_signed_compare` (def).
- `iv_sdiv` (def).
- `iv_mod_choice` (def).
- `iv_smod_base` (def).
- `iv_smod` (def).
- `iv_ashr_small` (def).
- `iv_ashr` (def).
- `iv_clipped` (def).
- `iv_clip_list` (Fixpoint).
- `iv_empty_list` (Fixpoint).
- `iv_values` (Fixpoint).
- `iv_forward` (def).
- `iv_frame_weight` (def).
- `iv_work` (def).
- `iv_forward_erases_type` (def).
- `iv_helpers_erases_type` (def).

## DomainsAuditTransferSource

Public package: `Galois.Domains`.

Card: AUD-DT

- `sb_mark` (def).
- `sb_make` (def).
- `sb_reduce_source` (def).
- `sb_join_half_source` (def).
- `sb_join_source` (def).
- `sb_lift_source` (def).
- `sb_top_source` (def).
- `sb_const_source` (def).
- `sb_from_interval_source` (def).
- `sb_components_source` (def).
- `sb_order_source` (def).
- `sb_choice_prepend` (Fixpoint).
- `sb_append_rows` (Fixpoint).
- `sb_choices_source` (Fixpoint).
- `sb_bits_inputs` (Fixpoint).
- `sb_arc_inputs` (Fixpoint).
- `sb_case_source` (def).
- `sb_case_map_source` (Fixpoint).
- `sb_join_all_source` (Fixpoint).
- `sb_forward_source` (def).
- `transfer_guard_source` (def).
- `transfer_forward_source` (def).
- `transfer_frame_weight` (def).
- `transfer_work` (def).
- `sb_forward_source_erases_type` (def).
- `sb_choices_source_erases_type` (def).
- `transfer_guard_erases_type` (def).
- `transfer_fallback_type` (def).
- `transfer_total_type` (def).
- `transfer_unique_type` (def).
- `transfer_choices_count_type` (def).
- `transfer_forward_plain_erases_type` (def).

## DomainsAuditTransferWord

Public package: `Galois.Domains`.

Card: AUD-DT-WORD

- `word_mark` (def).
- `word_neg` (def).
- `word_udiv` (def).
- `word_signed_div` (def).
- `word_smod` (def).
- `word_clz` (def).
- `word_sequence_source` (Fixpoint).
- `word_pop_filter` (Fixpoint).
- `word_length_source` (Fixpoint).
- `word_popcount` (def).
- `word_unary_source` (def).
- `word_binary_source` (def).
- `word_compare_source` (def).
- `word_width_source` (def).
- `word_normalize_source` (Fixpoint).
- `word_value_source` (def).
- `word_eval_source` (def).
- `word_frame_weight` (def).
- `word_source_work` (def).
- `word_eval_source_erases_type` (def).

## DomainsAuditTransferWrapped

Public package: `Galois.Domains`.

Card: AUD-DT-WRAPPED

- `wr_mark` (def).
- `wr_size` (def).
- `wr_cover` (def).
- `wr_choose` (def).
- `wr_join` (def).
- `wr_four` (def).
- `wr_range` (def).
- `wr_of_interval` (def).
- `wr_parts_raw` (def).
- `wr_parts` (def).
- `wr_add` (def).
- `wr_neg` (def).
- `wr_sub` (def).
- `wr_products` (def).
- `wr_mul_piece` (def).
- `wr_shift_bound` (def).
- `wr_shift_interval` (def).
- `wr_signed_parts` (def).
- `wr_mul_parts` (def).
- `wr_mul_cut` (def).
- `wr_mul_both` (def).
- `wr_mul` (def).
- `wr_signed_piece` (def).
- `wr_project` (def).
- `wr_pole_cut` (def).
- `wr_piece` (def).
- `wr_unary` (def).
- `wr_piece_binary` (def).
- `wr_piece_cut` (def).
- `wr_binary` (def).
- `wr_forward` (def).
- `wr_frame_weight` (def).
- `wr_work` (def).
- `wr_forward_erases_type` (def).
- `wr_helpers_erases_type` (def).

## DomainsAuditWiden

Public package: `Galois.Domains`.

Card: AUD-DW

- `audit_half_top` (def).
- `audit_half_widen` (def).
- `audit_widen` (def).
- `audit_widen_lattice` (def).
- `audit_widen_measure` (def).
- `audit_widen_domain` (def).
- `audit_widen_encloses_type` (def).
- `audit_widen_post_reduction_rank_type` (def).
- `audit_widen_bounded_type` (def).
- `audit_widen_sound_type` (def).
- `audit_widen_laws_type` (def).
- `audit_widen_domain_laws_type` (def).
- `audit_widen_rank_stable_type` (def).
- `audit_widen_rank_exists_type` (def).
- `audit_widen_rank_builder` (def).
- `audit_widen_rank_builder_measure_type` (def).

## DomainsAuditWidenSource

Public package: `Galois.Domains`.

Card: AUD-DW

- `widen_range` (def).
- `widen_merge` (def).
- `widen_bit` (def).
- `widen_fix` (def).
- `widen_search` (Fixpoint).
- `widen_reduce` (def).
- `widen_order` (def).
- `widen_leb` (def).
- `widen_top` (def).
- `widen_half_source` (def).
- `audit_widen_source` (def).
- `audit_widen_measure_source` (def).
- `widen_frame_weight` (def).
- `widen_work` (def).
- `widen_half_size` (def).
- `widen_input_size` (def).
- `audit_widen_source_erases_type` (def).
- `widen_reduce_nodes_type` (def).
- `audit_widen_source_bound_type` (def).
- `audit_widen_measure_source_bound_type` (def).
- `audit_widen_plain_erases_type` (def).

## FloatAuditDiv

Public package: `Galois.Float`.

Card: AUD-FL

- `float_div_split` (def).
- `split_sound_type` (def).
- `zero_sign_sound_type` (def).
- `float_bin_select` (def).
- `select_sound_type` (def).
- `float_div_split_sound_type` (def).
- `float_zero_sign_sound_type` (def).
- `float_bin_select_sound_type` (def).
- `float_bin_select_legacy_type` (def).
- `float_bin_select_split_type` (def).

## FloatAuditDivBody

Public package: `Galois.Float`.

Card: AUD-FL-BODY

- `float_body_event` (ind).
- `FloatBodyCase` (constr).
- `FloatBodyBuild` (constr).
- `FloatBodyAdd` (constr).
- `FloatBodySub` (constr).
- `FloatBodyCompare` (constr).
- `FloatBodyDivide` (constr).
- `FloatBodyMultiply` (constr).
- `FloatBodyParity` (constr).
- `FloatBodyShift` (constr).
- `FloatBodyPower` (constr).
- `FloatBodyConvert` (constr).
- `FloatBodyDigits` (constr).
- `FloatBodyRoundChoice` (constr).
- `FloatBodyShiftOne` (constr).
- `float_body_shift_iter` (Fixpoint).
- `float_body_exponent` (def).
- `float_body_align` (def).
- `float_body_choice` (def).
- `float_body_fit` (def).
- `float_body_round` (def).
- `float_body_location` (def).
- `float_body_core` (def).
- `float_body_event_work` (def).
- `float_body_work` (def).
- `float_body_core_erases_type` (def).
- `float_body_round_erases_type` (def).
- `float_body_shift_count_type` (def).
- `float_body_shift_bound_type` (def).

## FloatAuditDivEndpoint

Public package: `Galois.Float`.

Card: AUD-FL

- `audit_float_min_subnormal` (def).
- `audit_float_positive_endpoint` (def).
- `audit_float_negative_endpoint` (def).
- `audit_float_min_subnormal_correct_statement` (def).

## FloatAuditDivPlain

Public package: `Galois.Float`.

Card: AUD-FL

- `audit_float_endpoint_laws` (def).
- `audit_float_finite_max` (def).
- `audit_float_finite_min` (def).
- `audit_float_piece` (def).
- `audit_float_zero_masks` (def).
- `audit_float_set_zero_masks` (def).
- `audit_float_split_candidate` (def).
- `audit_float_split_candidate_sound_statement` (def).

## FloatAuditDivPrecision

Public package: `Galois.Float`.

Card: AUD-FL

- `audit_bound32` (def).
- `audit_zero32` (def).
- `audit_inf32` (def).
- `audit_one32` (def).
- `audit_two32` (def).
- `audit_minus_one32` (def).
- `audit_point_one32` (def).
- `audit_zero_to_two32` (def).
- `audit_positive_zero_only32` (def).
- `float_div_split_precision_type` (def).

## FloatAuditDivSource

Public package: `Galois.Float`.

Card: AUD-FL

- `float_source_event` (ind).
- `FloatCase` (constr).
- `FloatConstruct` (constr).
- `FloatProjection` (constr).
- `FloatBoolean` (constr).
- `FloatCompare` (constr).
- `FloatDivide` (constr).
- `FloatFormatBound` (constr).
- `FloatInteger` (constr).
- `FloatEndpoint` (constr).
- `float_run` (def).
- `float_bind` (def).
- `float_mark` (def).
- `float_nn_compare` (def).
- `float_minmax` (def).
- `float_active` (def).
- `float_full_bound` (def).
- `float_clamp` (def).
- `float_bounds` (def).
- `float_class` (def).
- `float_join_source` (def).
- `float_bottom_source` (def).
- `float_pair_source` (def).
- `float_join_list` (Fixpoint).
- `float_classes` (def).
- `float_special_row_source` (def).
- `float_special_source` (def).
- `float_directed_source` (def).
- `float_corners_source` (def).
- `float_bounds_interval_source` (def).
- `float_piece_source` (def).
- `float_zero_masks_source` (def).
- `float_div_split_source` (def).
- `float_value_bits` (def).
- `float_alignment_amount` (def).
- `float_pinned_division_body` (def).
- `float_pinned_division_work` (def).
- `float_primitive_body_work` (def).
- `float_source_work` (def).
- `float_input_size` (def).
- `float_primitive_body_positive_type` (def).
- `float_pinned_division_body_correspondence_type` (def).
- `float_div_split_source_erases_type` (def).
- `float_div_split_source_bound_type` (def).
- `float_div_split_source_divides_type` (def).
- `float_div_split_source_total_type` (def).
- `float_div_split_source_unique_type` (def).
- `audit_floor_sum_fast_correct` in `AnalysesAuditScevModCountCorrectness`; owner
  AUD-SM-COUNT-ARITH.


## Future NUM theorem ownership

### Galois.Analyses.AnalysesAuditScevFast

Card: AUD-SA

- `scev_nowrap_fast_agrees` (future Theorem).
- `scev_nowrap_probe_sound` (future Theorem).
- `scev_nowrap_trip_agrees` (future Theorem).
- `scev_nowrap_trip_no_exit` (future Theorem).
- `scev_nowrap_unit_no_fallback` (future Theorem).
- `scev_unsigned_unit_lt` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFastLegacy

Card: AUD-SA

- `nw_guard_lean_legacy_agrees` (future Theorem).
- `scev_nowrap_fast_lean_legacy_agrees` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFastSource

Card: AUD-SA

- `scalar_fallback_erases` (future Theorem).
- `scalar_guard_lean_erases` (future Theorem).
- `scalar_predicate_erases` (future Theorem).
- `scalar_search_counts` (future Theorem).
- `scev_nowrap_source_bound` (future Theorem).
- `scev_nowrap_source_erases` (future Theorem).
- `scev_nowrap_source_lean_erases` (future Theorem).
- `scev_nowrap_source_unit` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFloorGe

Card: AUD-SM-COUNT-FLOOR

- `audit_floor_ge_calls_exact` (future Theorem).
- `audit_floor_ge_source_correct` (future Theorem).
- `audit_floor_ge_source_total` (future Theorem).
- `audit_floor_ge_weight_bound` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFloorIter

Card: AUD-SM-COUNT-ITER

- `audit_floor_iter_overhead_bounded` (future Theorem).
- `audit_floor_iter_source_correct` (future Theorem).
- `audit_floor_iter_source_count` (future Theorem).
- `audit_floor_iter_source_total` (future Theorem).
- `audit_floor_iter_source_weight` (future Theorem).
- `audit_floor_iter_ticks_exact` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFloorSum

Card: AUD-SM-COUNT-FLOOR

- `audit_floor_sum_fuel_positive` (future Theorem).
- `audit_floor_sum_source_correct` (future Theorem).
- `audit_floor_sum_source_total` (future Theorem).
- `audit_floor_sum_tick_count` (future Theorem).
- `audit_floor_sum_weight_bound` (future Theorem).

### Galois.Analyses.AnalysesAuditScevFloorTick

Card: AUD-SM-COUNT-TICK

- `audit_floor_tick_instrumentation_bound` (future Theorem).
- `audit_floor_tick_instrumentation_exact` (future Theorem).
- `audit_floor_tick_source_correct` (future Theorem).
- `audit_floor_tick_source_count` (future Theorem).
- `audit_floor_tick_source_counts_exact` (future Theorem).
- `audit_floor_tick_source_total` (future Theorem).
- `audit_floor_tick_source_weight` (future Theorem).
- `floor_tick_correspondence` (future Theorem).
- `floor_tick_count` (future Theorem).
- `floor_tick_total` (future Theorem).

### Galois.Analyses.AnalysesAuditScevMod

Card: AUD-SM-HIT

- `audit_mod_even_no_fallback` (future Theorem).
- `audit_mod_one_bit_fallback` (future Theorem).
- `audit_mod_period_positive` (future Theorem).
- `audit_mod_period_size` (future Theorem).
- `scev_mod_even_no_exit` (future Theorem).
- `scev_mod_first_hit_agrees` (future Theorem).
- `scev_mod_first_hit_count` (future Theorem).
- `scev_mod_no_exit` (future Theorem).
- `scev_mod_trip_agrees` (future Theorem).

### Galois.Analyses.AnalysesAuditScevModCount

Card: AUD-SM-COUNT

- `count_normalize_erases` (future Theorem).
- `count_zencode_correct` (future Theorem).
- `scev_mod_count_floor_calls` (future Theorem).
- `scev_mod_count_source_bound` (future Theorem).
- `scev_mod_count_source_correspondence` (future Theorem).
- `scev_mod_count_traced_erases` (future Theorem).
- `scev_mod_count_whole_correspondence` (future Theorem).
- `scev_mod_count_whole_total` (future Theorem).
- `scev_mod_count_whole_unique` (future Theorem).

### Galois.Analyses.AnalysesAuditScevModCountCorrectness

Card: AUD-SM-COUNT-ARITH

- `audit_floor_live_bits` (future Theorem).
- `audit_floor_sum_fast_correct` (future Theorem).
- `audit_floor_sum_terminates` (future Theorem).
- `audit_floor_sum_zero` (future Theorem).
- `scev_mod_count_exact` (future Theorem).

### Galois.Analyses.AnalysesAuditScevModSource

Card: AUD-SM-HIT

- `hit_period_size` (future Theorem).
- `hit_source_bound` (future Theorem).
- `hit_source_even_no_fallback` (future Theorem).
- `hit_source_queries` (future Theorem).
- `hit_source_width_one` (future Theorem).
- `mod_first_hit_plain_erases` (future Theorem).
- `mod_probe_plain_erases` (future Theorem).
- `scev_mod_first_hit_source_erases` (future Theorem).

### Galois.Analyses.AnalysesAuditScevRecognize

Card: AUD-SR

- `recognize_cache` (future Theorem).
- `recognize_sound` (future Theorem).
- `scev_extra_cache_valid` (future Theorem).
- `scev_extra_recognize_sound` (future Theorem).

### Galois.Analyses.AnalysesAuditScevRecognizeCheck

Card: AUD-SR-CHECK

- `sr_check_plan_source_erases` (future Theorem).

### Galois.Analyses.AnalysesAuditScevRecognizePlain

Card: AUD-SR-CLOSURE

- `scev_captured_compile_lean_erases` (future Theorem).
- `scev_extra_recognize_agrees` (future Theorem).
- `scev_lookup_equal_lean_agrees` (future Theorem).

### Galois.Analyses.AnalysesAuditScevRecognizeSource

Card: AUD-SR

- `producer_advance_erases` (future Theorem).
- `producer_prepare_expr_erases` (future Theorem).
- `producer_source_counts` (future Theorem).
- `scev_extra_recognize_source_bound` (future Theorem).
- `scev_extra_recognize_source_erases` (future Theorem).
- `scev_extra_recognize_source_total` (future Theorem).
- `scev_extra_recognize_source_unique` (future Theorem).

### Galois.Analyses.AnalysesAuditScevRecognizeTrace

Card: AUD-SR-CLOSURE

- `sr_compile_expr_source_erases` (future Theorem).
- `sr_lookup_equal_erases` (future Theorem).

### Galois.Analyses.AnalysesAuditScevTrip

Card: AUD-SM-HIT

- `trip_client_source_bound` (future Theorem).
- `trip_client_source_erases` (future Theorem).
- `trip_expression_source_bound` (future Theorem).

### Galois.Analyses.AnalysesAuditScevTripScalar

Card: AUD-SA

- `trip_nowrap_source_bound` (future Theorem).
- `trip_nowrap_source_erases` (future Theorem).

### Galois.Domains.DomainsAuditMul

Card: AUD-DM

- `audit_mul_active_bits_bound` (future Theorem).
- `audit_mul_bottom` (future Theorem).
- `audit_mul_constants` (future Theorem).
- `audit_mul_counted_bounds` (future Theorem).
- `audit_mul_meet_bottom` (future Theorem).
- `audit_mul_meet_constants` (future Theorem).
- `audit_mul_meet_intersection` (future Theorem).
- `audit_mul_meet_sound` (future Theorem).
- `audit_mul_meet_width` (future Theorem).
- `audit_mul_meet_word_laws` (future Theorem).
- `audit_mul_sound` (future Theorem).
- `audit_mul_steps_exact` (future Theorem).
- `audit_mul_width` (future Theorem).
- `audit_mul_word_laws` (future Theorem).

### Galois.Domains.DomainsAuditMulDispatch

Card: AUD-DM

- `mul_dispatch_fallback` (future Theorem).
- `mul_dispatch_source_bound` (future Theorem).
- `mul_dispatch_total` (future Theorem).
- `mul_dispatch_unique` (future Theorem).
- `mul_precise_forward_erases` (future Theorem).

### Galois.Domains.DomainsAuditMulSource

Card: AUD-DM

- `audit_mul_counted_plain_erases` (future Theorem).
- `audit_mul_meet_plain_erases` (future Theorem).
- `audit_mul_source_bound` (future Theorem).
- `audit_mul_source_counts` (future Theorem).
- `mul_dom8_source_erases` (future Theorem).

### Galois.Domains.DomainsAuditNumericAdequacy

Card: AUD-DOM-ADEQUACY

- `domain_helpers_erases` (future Theorem).
- `domain_helpers_full_erases` (future Theorem).
- `kb_empty_scan_source_count` (future Theorem).
- `kb_forward_source_erases` (future Theorem).
- `kb_classic_mul_source_bound` (future Theorem).
- `kb_forward_source_bound` (future Theorem).
- `kb_source_total` (future Theorem).
- `kb_source_unique` (future Theorem).

### Galois.Domains.DomainsAuditProductSource

Card: AUD-DR-PRODUCT

- `product_bits_round_source_bound` (future Theorem).
- `product_bits_round_source_erases` (future Theorem).
- `product_pack_depth_bound` (future Theorem).

### Galois.Domains.DomainsAuditReduce

Card: AUD-DR

- `audit_reduce_gamma` (future Theorem).
- `audit_reduce_rank` (future Theorem).
- `audit_reduce_stable` (future Theorem).
- `audit_reduce_word_laws` (future Theorem).

### Galois.Domains.DomainsAuditReduceBits

Card: AUD-DR

- `audit_reduce_bits_plain_erases` (future Theorem).
- `audit_reduce_bits_source_bound` (future Theorem).
- `audit_reduce_bits_source_erases` (future Theorem).
- `reduce_bits_exchange_laws` (future Theorem).
- `reduce_bits_rank_source_erases` (future Theorem).

### Galois.Domains.DomainsAuditReduceSource

Card: AUD-DR

- `audit_reduce_source_bound` (future Theorem).
- `audit_reduce_source_calls` (future Theorem).
- `audit_reduce_source_erases` (future Theorem).
- `reduce_plain_erases` (future Theorem).

### Galois.Domains.DomainsAuditTransfer

Card: AUD-DT

- `audit_div_one_fallback` (future Theorem).
- `audit_div_one_laws` (future Theorem).
- `audit_div_one_refines` (future Theorem).
- `audit_div_one_strict` (future Theorem).
- `audit_transfer_shapes` (future Theorem).
- `audit_transfer_sound` (future Theorem).

### Galois.Domains.DomainsAuditTransferBounds

Card: AUD-DT

- `iv_forward_source_bound` (future Theorem).
- `iv_source_total` (future Theorem).
- `iv_source_unique` (future Theorem).
- `sb_forward_source_bound` (future Theorem).
- `transfer_guard_source_bound` (future Theorem).
- `transfer_source_bound` (future Theorem).
- `transfer_whole_execution` (future Theorem).
- `word_eval_source_bound` (future Theorem).
- `wr_forward_source_bound` (future Theorem).
- `wr_source_total` (future Theorem).
- `wr_source_unique` (future Theorem).

### Galois.Domains.DomainsAuditTransferInterval

Card: AUD-DT-INTERVAL

- `iv_forward_erases` (future Theorem).
- `iv_helpers_erases` (future Theorem).

### Galois.Domains.DomainsAuditTransferSource

Card: AUD-DT

- `sb_choices_source_erases` (future Theorem).
- `sb_forward_source_erases` (future Theorem).
- `transfer_choices_count` (future Theorem).
- `transfer_fallback` (future Theorem).
- `transfer_forward_plain_erases` (future Theorem).
- `transfer_guard_erases` (future Theorem).
- `transfer_total` (future Theorem).
- `transfer_unique` (future Theorem).

### Galois.Domains.DomainsAuditTransferWord

Card: AUD-DT-WORD

- `word_eval_source_erases` (future Theorem).

### Galois.Domains.DomainsAuditTransferWrapped

Card: AUD-DT-WRAPPED

- `wr_forward_erases` (future Theorem).
- `wr_helpers_erases` (future Theorem).

### Galois.Domains.DomainsAuditWiden

Card: AUD-DW

- `audit_widen_bounded` (future Theorem).
- `audit_widen_domain_laws` (future Theorem).
- `audit_widen_encloses` (future Theorem).
- `audit_widen_laws` (future Theorem).
- `audit_widen_post_reduction_rank` (future Theorem).
- `audit_widen_rank_builder_measure` (future Theorem).
- `audit_widen_rank_exists` (future Theorem).
- `audit_widen_rank_stable` (future Theorem).
- `audit_widen_sound` (future Theorem).
- `audit_widen_rank_measure` (future Theorem).

### Galois.Domains.DomainsAuditWidenSource

Card: AUD-DW

- `audit_widen_measure_source_bound` (future Theorem).
- `audit_widen_plain_erases` (future Theorem).
- `audit_widen_source_bound` (future Theorem).
- `audit_widen_source_erases` (future Theorem).
- `widen_reduce_nodes` (future Theorem).

### Galois.Float.FloatAuditDiv

Card: AUD-FL

- `float_bin_select_legacy` (future Theorem).
- `float_bin_select_sound` (future Theorem).
- `float_bin_select_split` (future Theorem).
- `float_div_split_sound` (future Theorem).
- `float_zero_sign_sound` (future Theorem).
- `select_sound` (future Theorem).
- `split_sound` (future Theorem).
- `zero_sign_sound` (future Theorem).

### Galois.Float.FloatAuditDivBody

Card: AUD-FL-BODY

- `float_body_core_erases` (future Theorem).
- `float_body_round_erases` (future Theorem).
- `float_body_shift_bound` (future Theorem).
- `float_body_shift_count` (future Theorem).

### Galois.Float.FloatAuditDivEndpoint

Card: AUD-FL

- `audit_float_min_subnormal_correct` (future Theorem).

### Galois.Float.FloatAuditDivPlain

Card: AUD-FL

- `audit_float_split_candidate_sound` (future Theorem).

### Galois.Float.FloatAuditDivPrecision

Card: AUD-FL

- `float_div_split_precision` (future Theorem).

### Galois.Float.FloatAuditDivSource

Card: AUD-FL

- `float_div_split_source_bound` (future Theorem).
- `float_div_split_source_divides` (future Theorem).
- `float_div_split_source_erases` (future Theorem).
- `float_div_split_source_total` (future Theorem).
- `float_div_split_source_unique` (future Theorem).
- `float_pinned_division_body_correspondence` (future Theorem).
- `float_primitive_body_positive` (future Theorem).

The public `audit_widen_rank` definition is owned by AUD-DW.
<!-- AUD-API-NUM-NAMES-END -->

<!-- AUD-API-MAT-NAMES-BEGIN -->

# MAT audit names

## RulesAuditMaterializeDeltaTotal

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_total_run` (ind).
- `MatTotalStop` (constr).
- `MatTotalNext` (constr).
- `mat_stratum_run` (ind).
- `MatStratumRun` (constr).
- `mat_levels_run` (ind).
- `MatLevelsZero` (constr).
- `MatLevelsNext` (constr).
- `mat_bounded_program` (def).
- `mat_program_run` (ind).
- `MatProgramRejected` (constr).
- `MatProgramAccepted` (constr).
- `mat_terms_dimension` (Fixpoint).
- `mat_atom_dimension` (def).
- `mat_rule_dimension` (def).
- `mat_input_dimension` (def).
- `mat_whole_budget` (def).
- `mat_total_realization_statement` (def).
- `mat_total_erases_statement` (def).
- `mat_total_unique_statement` (def).
- `mat_stratum_realization_statement` (def).
- `mat_stratum_erases_statement` (def).
- `mat_levels_realization_statement` (def).
- `mat_levels_erases_statement` (def).
- `mat_program_realization_statement` (def).
- `mat_program_erases_statement` (def).
- `mat_program_unique_statement` (def).
- `mat_program_whole_bound_statement` (def).
- `mat_bounded_program_erases_statement` (def).
- `mat_bounded_program_bound_statement` (def).
- `mat_materialization_consumer_statement` (def).
- `mat_program_loop_budget` (def).
- `mat_total_rounds_input_bound_statement` (def).
- `mat_program_rounds_input_bound_statement` (def).
- `mat_program_input_loop_bound_statement` (def).
- `rules_materialization_cost_statement` (def).
- `rules_materialization_source_correspondence_statement` (def).
- `rules_materialization_consumer_statement` (def).
- `rules_materialization_same_execution_bound_statement` (def).
- `mat_predicate_callback_source` (rec).
- `mat_predicate_encoder_body` (proj).
- `mat_predicate_arity_body` (proj).
- `mat_predicate_body_frame_weight` (proj).
- `mat_predicate_callback_receipts_statement` (def).
- `mat_predicate_callback_input_bounds_statement` (def).
- `mat_external_level_source` (rec).
- `mat_external_level_body` (proj).
- `mat_external_level_frame_weight` (proj).
- `mat_external_level_receipts_statement` (def).

## RulesAuditMaterializeDifference

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_node` (def).
- `mat_filter_ne` (Fixpoint).
- `mat_filter_trie` (def).
- `mat_diff_value` (def).
- `mat_diff_left` (def).
- `mat_diff_right` (def).
- `mat_diff_ne` (Fixpoint).
- `mat_diff` (def).
- `mat_diff_erases_statement` (def).
- `mat_diff_bound_statement` (def).

## RulesAuditMaterializeFullSource

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_delta_program_callback_receipts_statement` (def).
- `rules_delta_materialization_full_source_statement` (def).
- `rules_materialization_full_source_statement` (def).

## RulesAuditMaterializeJobs

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_pos_equal` (def).
- `mat_term_equal` (def).
- `mat_terms_equal` (Fixpoint).
- `mat_atom_equal` (def).
- `mat_tag_atom` (def).
- `mat_tag_rule` (def).
- `mat_recursive` (def).
- `mat_specs` (def).
- `mat_current` (def).
- `mat_tag_env` (def).
- `mat_predicate_set_calls` (def).
- `mat_universe_calls` (def).
- `mat_universe_prepare_source` (def).
- `mat_setup_cached` (def).
- `mat_accept_cached` (def).
- `mat_variant` (def).
- `mat_variant_legacy` (def).
- `mat_prepare_jobs` (def).
- `mat_update_jobs` (def).
- `mat_candidates` (def).
- `mat_candidates_prepared` (def).
- `mat_tag_rule_erases_statement` (def).
- `mat_prepare_jobs_erases_statement` (def).
- `mat_candidates_erases_statement` (def).

## RulesAuditMaterializeNaiveBodies

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_nat_encoder` (def).
- `mat_numbered_rules` (Fixpoint).
- `mat_rule_index` (Fixpoint).
- `mat_dependencies` (def).
- `mat_fill_values` (Fixpoint).
- `mat_generated_env` (def).
- `mat_classic_join` (Fixpoint).
- `mat_naive_firing` (def).
- `mat_clamp` (def).
- `mat_constraints` (def).
- `mat_generated_deps` (def).
- `mat_generated_targets` (def).
- `mat_store_relations` (def).
- `mat_rule_index_erases_statement` (def).
- `mat_dependencies_erases_statement` (def).
- `mat_constraints_erases_statement` (def).
- `mat_classic_join_erases_statement` (def).
- `mat_classic_join_source_erases_statement` (def).
- `mat_naive_firing_erases_statement` (def).
- `mat_clamp_erases_statement` (def).
- `mat_generated_env_erases_statement` (def).

## RulesAuditMaterializeNaiveCallbacks

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_constraint_encoder` (def).
- `mat_positive_body_work` (def).
- `mat_index_source_event_work` (def).
- `mat_dep_source_weight` (def).
- `mat_naive_body_event` (ind).
- `MatNaiveLocal` (constr).
- `MatNaiveScheduleQuery` (constr).
- `mat_naive_body_weight` (def).
- `mat_local_receipt` (def).
- `mat_naive_declared_source` (def).
- `mat_naive_declared_source_laws_statement` (def).
- `mat_naive_body_positive_statement` (def).
- `mat_index_weight_instance_statement` (def).

## RulesAuditMaterializeNaiveDimensions

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_relation_dimension` (def).
- `mat_assignment_dimension` (def).
- `mat_constraint_dimension` (def).
- `mat_queue_dimension` (def).
- `mat_engine_call_dimension` (def).
- `mat_engine_trace_dimension` (def).
- `mat_rpo_dimension` (def).
- `mat_naive_level_input_steps` (def).
- `mat_naive_levels_input_steps` (Fixpoint).
- `mat_naive_program_input_steps` (def).
- `mat_naive_whole_budget` (def).

## RulesAuditMaterializeNaiveQuery

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_rule_finish_context` (rec).
- `mat_finish_rule` (proj).
- `mat_finish_head` (proj).
- `mat_finish_dependencies` (proj).
- `mat_native_finish` (def).
- `mat_rule_finish_source` (def).
- `mat_finish_capture` (ind).
- `MatFinishBase` (constr).
- `MatFinishCons` (constr).
- `mat_finish_apply` (Fixpoint).
- `mat_ask_all_source` (def).
- `mat_finish_depth` (Fixpoint).
- `mat_finish_origin` (Fixpoint).
- `mat_finish_origin_valid` (def).
- `mat_generated_continuation_source` (ind).
- `MatGeneratedContinuation` (constr).
- `mat_rhs_source` (def).
- `mat_rhs_source_erases_statement` (def).
- `mat_finish_apply_erases_statement` (def).
- `mat_generated_continuation_erases_statement` (def).
- `mat_generated_continuation_total_statement` (def).

## RulesAuditMaterializeNaiveTotal

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_facts_by_pred_source` (def).
- `mat_store_total_values` (def).
- `mat_store_total_values_erases_statement` (def).
- `mat_facts_by_pred_source_erases_statement` (def).
- `mat_setup_cached_erases_statement` (def).
- `mat_naive_event` (ind).
- `MatNaiveFrame` (constr).
- `MatNaiveScheduler` (constr).
- `MatNaiveEngine` (constr).
- `mat_naive_event_work` (def).
- `mat_naive_event_frames` (def).
- `mat_naive_event_dimension` (def).
- `mat_naive_work` (def).
- `mat_naive_operand_max` (def).
- `mat_naive_callback_frames` (def).
- `mat_naive_level_run` (ind).
- `MatNaiveLevelRun` (constr).
- `mat_naive_levels_run` (ind).
- `MatNaiveLevelsZero` (constr).
- `MatNaiveLevelsNext` (constr).
- `mat_naive_program_run` (ind).
- `MatNaiveProgramRejected` (constr).
- `MatNaiveProgramAccepted` (constr).
- `mat_naive_program_realization_statement` (def).
- `mat_naive_program_erases_statement` (def).
- `mat_naive_program_source_bound_statement` (def).
- `mat_naive_program_callback_receipts_statement` (def).
- `rules_naive_materialization_full_source_statement` (def).
- `rules_naive_materialization_consumer_statement` (def).

## RulesAuditMaterializePlans

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_nested_rows` (Fixpoint).
- `mat_nested_prepare` (def).
- `mat_nested_rebuild` (def).
- `mat_nested_update` (def).
- `mat_variable_domains` (def).
- `mat_multiway_rows` (Fixpoint).
- `mat_multiway_prepare` (def).
- `mat_variable_erase` (def).
- `mat_variable_rebuild` (def).
- `mat_variable_update` (def).
- `mat_plan_rows` (def).
- `mat_plan_prepare` (def).
- `mat_plan_update` (def).
- `mat_terminal_atom` (def).
- `mat_positive` (def).
- `mat_negative` (def).
- `mat_plan_bindings` (def).
- `mat_fill_snapshot` (Fixpoint).
- `mat_snapshot_encoded` (def).
- `mat_snapshot` (def).
- `mat_snapshot_rows` (def).
- `mat_snapshot_rows_encoded` (def).
- `mat_plan_rows_erases_statement` (def).
- `mat_plan_update_erases_statement` (def).
- `mat_plan_bindings_erases_statement` (def).

## RulesAuditMaterializePowerset

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_subset_root` (def).
- `mat_subset_ne` (Fixpoint).
- `mat_subset` (def).
- `mat_subset_erases_statement` (def).
- `mat_subset_bound_statement` (def).
- `mat_relation_leb` (def).
- `mat_relation_bot` (def).
- `mat_relation_join` (def).
- `mat_relation_widen` (def).
- `mat_relation_narrow` (def).
- `mat_relation_callbacks_erases_statement` (def).
- `mat_relation_callbacks_bound_statement` (def).

## RulesAuditMaterializeQueryTrace

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_query_cursor` (ind).
- `MatQueryCursor` (constr).
- `mat_cursor_start` (def).
- `mat_cursor_next` (def).
- `mat_event_changes_cursor` (def).
- `mat_naive_trace_source` (ind).
- `MatNaiveTraceNil` (constr).
- `MatNaiveTraceOther` (constr).
- `MatNaiveTraceRhs` (constr).
- `MatNaiveTraceContinuation` (constr).
- `mat_naive_trace_source_forgets_statement` (def).

## RulesAuditMaterializeReceipts

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_frame_needs_callback` (def).
- `mat_external_frame_receipt` (ind).
- `MatInternalFrameReceipt` (constr).
- `MatPredicateEncodeReceipt` (constr).
- `MatPredicateArityReceipt` (constr).
- `mat_external_trace_receipts` (def).
- `mat_external_body_work` (def).
- `mat_external_trace_allowance` (def).
- `mat_external_trace_bound_statement` (def).

## RulesAuditMaterializeRounds

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_selected` (def).
- `mat_seed_atoms` (def).
- `mat_initial` (def).
- `mat_advance` (def).
- `mat_step` (def).
- `mat_prepared_step` (def).
- `mat_one` (def).
- `mat_observe` (Fixpoint).
- `mat_bounded_stratum` (def).
- `mat_bounded_levels` (Fixpoint).
- `mat_initial_erases_statement` (def).
- `mat_step_erases_statement` (def).
- `mat_prepared_step_erases_statement` (def).
- `mat_bounded_levels_erases_statement` (def).

## RulesAuditMaterializeStratify

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_rule_edges` (def).
- `mat_program_edges` (def).
- `mat_rule_predicates` (def).
- `mat_rule_nodes` (def).
- `mat_level_at` (def).
- `mat_edge_ok` (def).
- `mat_raise_edge` (def).
- `mat_stratify_tick` (def).
- `mat_piter` (Fixpoint).
- `mat_niter` (def).
- `mat_stratify` (def).
- `mat_stratify_erases_statement` (def).
- `mat_stratify_input_size` (def).
- `mat_stratify_bound_statement` (def).
- `mat_stratify_total_statement` (def).
- `mat_stratify_unique_statement` (def).

## RulesAuditMaterializeSystem

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_compiled_system` (def).
- `mat_compiled_static` (def).
- `mat_target_source` (def).
- `mat_index_callbacks` (def).
- `mat_naive_index_source` (def).
- `mat_index_callbacks_erases_statement` (def).
- `mat_index_callbacks_source_statement` (def).
- `mat_level_capture_dimension` (def).
- `mat_dependency_rule_dimension` (def).
- `mat_index_capture_dimension` (def).
- `mat_index_callback_budget` (def).
- `mat_index_callback_bounded_statement` (def).
- `mat_rpo_source` (def).
- `mat_rpo_source_erases_statement` (def).

## RulesAuditMaterializeTrace

Public package: `Galois.Rules`.

Card: AUD-RU-MAT-BASE

- `mat_set_callback_frames` (def).
- `mat_index_callback_frames` (def).
- `mat_dep_callback_frames` (def).
- `mat_dep_map_frames` (def).
- `mat_dep_set_frames` (def).
- `mat_prepare_callback_frames` (def).
- `mat_dfs_callback_frames` (def).
- `mat_positions_callback_frames` (def).
- `mat_retreat_callback_frames` (def).
- `mat_rpo_callback_frames` (def).
- `mat_naive_body_callback_frames` (def).
- `mat_naive_bodies_callback_frames` (def).
- `mat_classic_join_source_erases` in `RulesAuditMaterializeBodiesCorrectness`; owner
  AUD-RU-MAT-BODIES.
- `mat_facts_by_pred_source_erases` in `RulesAuditMaterializeBodiesCorrectness`; owner
  AUD-RU-MAT-BODIES.
- `mat_relation_callbacks_bound` in `RulesAuditMaterializeBodiesCorrectness`; owner
  AUD-RU-MAT-BODIES.
- `mat_relation_callbacks_erases` in `RulesAuditMaterializeBodiesCorrectness`; owner
  AUD-RU-MAT-BODIES.
- `mat_store_total_values_erases` in `RulesAuditMaterializeBodiesCorrectness`; owner
  AUD-RU-MAT-BODIES.
- `mat_program_rounds_input_bound` in `RulesAuditMaterializeDeltaCorrectness`; owner
  AUD-RU-MAT-DELTA.
- `rules_materialization_consumer` in `RulesAuditMaterializeDeltaCorrectness`; owner
  AUD-RU-MAT-DELTA.
- `rules_materialization_same_execution_bound` in `RulesAuditMaterializeDeltaCorrectness`; owner
  AUD-RU-MAT-DELTA.
- `rules_materialization_source_correspondence` in `RulesAuditMaterializeDeltaCorrectness`; owner
  AUD-RU-MAT-DELTA.
- `mat_delta_program_callback_receipts` in `RulesAuditMaterializeFullSourceCorrectness`; owner
  AUD-RU-MAT.
- `rules_delta_materialization_full_source` in `RulesAuditMaterializeFullSourceCorrectness`; owner
  AUD-RU-MAT.
- `rules_materialization_full_source` in `RulesAuditMaterializeFullSourceCorrectness`; owner
  AUD-RU-MAT.
- `mat_naive_program_callback_receipts` in `RulesAuditMaterializeNaiveCorrectness`; owner
  AUD-RU-MAT-NAIVE.
- `mat_naive_program_realization` in `RulesAuditMaterializeNaiveCorrectness`; owner
  AUD-RU-MAT-NAIVE.
- `mat_naive_program_source_bound` in `RulesAuditMaterializeNaiveCorrectness`; owner
  AUD-RU-MAT-NAIVE.
- `rules_naive_materialization_consumer` in `RulesAuditMaterializeNaiveCorrectness`; owner
  AUD-RU-MAT-NAIVE.
- `rules_naive_materialization_full_source` in `RulesAuditMaterializeNaiveCorrectness`; owner
  AUD-RU-MAT-NAIVE.
- `mat_external_trace_bound` in `RulesAuditMaterializeReceiptsCorrectness`; owner
  AUD-RU-MAT-RECEIPTS.


## Future MAT theorem ownership

### Galois.Rules.RulesAuditMaterializeBodiesCorrectness

Card: AUD-RU-MAT-BODIES

- `mat_clamp_erases` (future Theorem).
- `mat_classic_join_erases` (future Theorem).
- `mat_classic_join_source_erases` (future Theorem).
- `mat_constraints_erases` (future Theorem).
- `mat_dependencies_erases` (future Theorem).
- `mat_generated_env_erases` (future Theorem).
- `mat_naive_firing_erases` (future Theorem).
- `mat_rule_index_erases` (future Theorem).
- `mat_relation_callbacks_bound` (future Theorem).
- `mat_relation_callbacks_erases` (future Theorem).
- `mat_subset_bound` (future Theorem).
- `mat_subset_erases` (future Theorem).
- `mat_facts_by_pred_source_erases` (future Theorem).
- `mat_setup_cached_erases` (future Theorem).
- `mat_store_total_values_erases` (future Theorem).

### Galois.Rules.RulesAuditMaterializeDeltaCorrectness

Card: AUD-RU-MAT-DELTA

- `mat_bounded_levels_erases` (future Theorem).
- `mat_initial_erases` (future Theorem).
- `mat_prepared_step_erases` (future Theorem).
- `mat_step_erases` (future Theorem).
- `mat_bounded_program_bound` (future Theorem).
- `mat_bounded_program_erases` (future Theorem).
- `mat_levels_erases` (future Theorem).
- `mat_levels_realization` (future Theorem).
- `mat_materialization_consumer` (future Theorem).
- `mat_program_erases` (future Theorem).
- `mat_program_input_loop_bound` (future Theorem).
- `mat_program_realization` (future Theorem).
- `mat_program_rounds_input_bound` (future Theorem).
- `mat_program_unique` (future Theorem).
- `mat_program_whole_bound` (future Theorem).
- `mat_stratum_erases` (future Theorem).
- `mat_stratum_realization` (future Theorem).
- `mat_total_erases` (future Theorem).
- `mat_total_realization` (future Theorem).
- `mat_total_rounds_input_bound` (future Theorem).
- `mat_total_unique` (future Theorem).
- `rules_materialization_consumer` (future Theorem).
- `rules_materialization_cost` (future Theorem).
- `rules_materialization_same_execution_bound` (future Theorem).
- `rules_materialization_source_correspondence` (future Theorem).

### Galois.Rules.RulesAuditMaterializeFullSourceCorrectness

Card: AUD-RU-MAT

- `mat_delta_program_callback_receipts` (future Theorem).
- `rules_delta_materialization_full_source` (future Theorem).
- `rules_materialization_full_source` (future Theorem).

### Galois.Rules.RulesAuditMaterializeFxCorrectness

Card: AUD-RU-MAT-FX

- `mat_index_callback_bounded` (future Theorem).
- `mat_index_callbacks_erases` (future Theorem).
- `mat_index_callbacks_source` (future Theorem).
- `mat_rpo_source_erases` (future Theorem).
- `mat_index_weight_instance` (future Theorem).
- `mat_naive_body_positive` (future Theorem).
- `mat_naive_declared_source_laws` (future Theorem).
- `mat_finish_apply_erases` (future Theorem).
- `mat_generated_continuation_erases` (future Theorem).
- `mat_generated_continuation_total` (future Theorem).
- `mat_rhs_source_erases` (future Theorem).
- `mat_naive_trace_source_forgets` (future Theorem).

### Galois.Rules.RulesAuditMaterializeNaiveCorrectness

Card: AUD-RU-MAT-NAIVE

- `mat_naive_program_callback_receipts` (future Theorem).
- `mat_naive_program_erases` (future Theorem).
- `mat_naive_program_realization` (future Theorem).
- `mat_naive_program_source_bound` (future Theorem).
- `rules_naive_materialization_consumer` (future Theorem).
- `rules_naive_materialization_full_source` (future Theorem).

### Galois.Rules.RulesAuditMaterializePlansCorrectness

Card: AUD-RU-MAT-PLANS

- `mat_diff_bound` (future Theorem).
- `mat_diff_erases` (future Theorem).
- `mat_plan_bindings_erases` (future Theorem).
- `mat_plan_rows_erases` (future Theorem).
- `mat_plan_update_erases` (future Theorem).
- `mat_candidates_erases` (future Theorem).
- `mat_prepare_jobs_erases` (future Theorem).
- `mat_tag_rule_erases` (future Theorem).

### Galois.Rules.RulesAuditMaterializeReceiptsCorrectness

Card: AUD-RU-MAT-RECEIPTS

- `mat_external_trace_bound` (future Theorem).

### Galois.Rules.RulesAuditMaterializeStratifyCorrectness

Card: AUD-RU-MAT-STRATIFY

- `mat_stratify_bound` (future Theorem).
- `mat_stratify_erases` (future Theorem).
- `mat_stratify_total` (future Theorem).
- `mat_stratify_unique` (future Theorem).
<!-- AUD-API-MAT-NAMES-END -->

<!-- AUD-API-FX-NAMES-BEGIN -->

# Fixpoint audit names

## FixpointAuditCache

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `cache_key_models` (Record).
- `cache_key_models_erase` (Definition).
- `cache_callback_event` (Inductive).
- `cache_init_callbacks` (Definition).
- `cache_query_callbacks` (Definition).
- `cache_callbacks_erasure_statement` (Definition).
- `cache_key_source` (Record).
- `cache_key_budget` (Record).
- `cache_key_source_laws` (Definition).
- `cache_key_source_bounded` (Definition).
- `cache_event_source` (Definition).
- `cache_trace_source` (Definition).
- `cache_callback_event_work` (Definition).
- `cache_callback_work` (Definition).
- `cache_external_engine_work` (Definition).
- `cache_callback_event_budget` (Definition).
- `cache_callback_budget` (Definition).
- `cache_index_source_laws` (Definition).
- `cache_refuel_index_laws` (Definition).
- `cache_query_callbacks_source_statement` (Definition).
- `cache_init_callbacks_source_statement` (Definition).
- `cache_compare_input_budget` (Definition).
- `cache_rebuild_input_budget` (Definition).
- `cache_query_input_budget` (Definition).
- `cache_engine_external_budget` (Definition).
- `cache_query_input_bound_statement` (Definition).
- `CacheKeyModels` (constructor of `cache_key_models`).
- `cache_epoch_encoder` (field of `cache_key_models`).
- `cache_context_encoder` (field of `cache_key_models`).
- `CacheEpochBody` (constructor of `cache_callback_event`).
- `CacheContextBody` (constructor of `cache_callback_event`).
- `CacheCompareBody` (constructor of `cache_callback_event`).
- `CacheIndexBody` (constructor of `cache_callback_event`).
- `CacheEngineBody` (constructor of `cache_callback_event`).
- `CacheCase` (constructor of `cache_callback_event`).
- `CacheKeySource` (constructor of `cache_key_source`).
- `cache_epoch_source` (field of `cache_key_source`).
- `cache_context_source` (field of `cache_key_source`).
- `CacheKeyBudget` (constructor of `cache_key_budget`).
- `cache_key_weight` (field of `cache_key_budget`).
- `cache_epoch_bound` (field of `cache_key_budget`).
- `cache_context_bound` (field of `cache_key_budget`).

Future proof module: `FixpointAuditCacheAdequacy`.

- `cache_callbacks_erasure`: `FixpointAuditCache.cache_callbacks_erasure_statement`; owner
  AUD-FX-CACHE.
- `cache_query_callbacks_source`: `FixpointAuditCache.cache_query_callbacks_source_statement`; owner
  AUD-FX-CACHE.
- `cache_init_callbacks_source`: `FixpointAuditCache.cache_init_callbacks_source_statement`; owner
  AUD-FX-CACHE.
- `cache_query_input_bound`: `FixpointAuditCache.cache_query_input_bound_statement`; owner
  AUD-FX-CACHE.

## FixpointAuditCacheSemantic

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `solver_snapshot` (Record).
- `snapshot_equiv` (Definition).
- `epoch_laws` (Record).
- `run_indexed` (Definition).
- `solver_cache` (Record).
- `cache_valid` (Definition).
- `cache_init` (Definition).
- `cache_query` (Definition).
- `cache_query_correct` (Definition).
- `contextual_snapshot` (Record).
- `contextual_laws` (Record).
- `contextual_cache` (Record).
- `contextual_init` (Definition).
- `contextual_query` (Definition).
- `contextual_query_correct` (Definition).
- `contextual_miss_rebuild` (Definition).
- `cache_epoch_initial_valid_statement` (Definition).
- `cache_epoch_miss_rebuild_statement` (Definition).
- `cache_epoch_hit_statement` (Definition).
- `cache_epoch_refuel_statement` (Definition).
- `cache_epoch_valid` (Definition).
- `SolverSnapshot` (constructor of `solver_snapshot`).
- `epoch` (field of `solver_snapshot`).
- `system` (field of `solver_snapshot`).
- `static` (field of `solver_snapshot`).
- `lat` (field of `solver_snapshot`).
- `schedule` (field of `solver_snapshot`).
- `mode` (field of `solver_snapshot`).
- `epoch_sound` (field of `epoch_laws`).
- `SolverCache` (constructor of `solver_cache`).
- `cached_snapshot` (field of `solver_cache`).
- `cached_index` (field of `solver_cache`).
- `cached_fuel` (field of `solver_cache`).
- `cached_result` (field of `solver_cache`).
- `ContextualSnapshot` (constructor of `contextual_snapshot`).
- `context_snapshot` (field of `contextual_snapshot`).
- `context_token` (field of `contextual_snapshot`).
- `context_identity` (field of `contextual_laws`).
- `ContextualCache` (constructor of `contextual_cache`).
- `context_cached_token` (field of `contextual_cache`).
- `context_cached_solver` (field of `contextual_cache`).
- `Build_epoch_laws` (constructor of `epoch_laws`).
- `Build_contextual_laws` (constructor of `contextual_laws`).

Future proof module: `FixpointAuditCacheSemanticAdequacy`.

- `cache_epoch_initial_valid`: `FixpointAuditCacheSemantic.cache_epoch_initial_valid_statement`;
  owner AUD-FX-CACHE.
- `cache_epoch_miss_rebuild`: `FixpointAuditCacheSemantic.cache_epoch_miss_rebuild_statement`; owner
  AUD-FX-CACHE.
- `cache_epoch_hit`: `FixpointAuditCacheSemantic.cache_epoch_hit_statement`; owner AUD-FX-CACHE.
- `cache_epoch_refuel`: `FixpointAuditCacheSemantic.cache_epoch_refuel_statement`; owner
  AUD-FX-CACHE.

## FixpointAuditCheckCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_local_set_entries` (Definition).
- `fx_local_x_entry_source` (Definition).
- `fx_local_c_entry_source` (Definition).
- `fx_local_x_entries_budget` (Definition).
- `fx_local_c_entries_budget` (Definition).
- `fx_narrow_check_source` (Definition).
- `fx_narrow_check_budget` (Definition).
- `fx_fullcheck_rooted_laws` (Definition).
- `fx_fullcheck_rooted_trace_source` (Definition).
- `fx_fullcheck_rooted_external_budget` (Definition).
- `fx_fullcheck_rooted_source_statement` (Definition).

Future proof module: `FixpointAuditCheckCallbacksAdequacy`.

- `fx_fullcheck_rooted_source`: `FixpointAuditCheckCallbacks.fx_fullcheck_rooted_source_statement`;
  owner AUD-FX-FULLCHECK.

## FixpointAuditContractClosures

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_declared_model_erasure_contract` (Definition).
- `run_worklist_declared_model_cost_contract` (Definition).
- `fx_declared_total_engine_total_contract` (Definition).
- `fx_declared_total_engine_erases_contract` (Definition).
- `fx_recorded_model_erasure_contract` (Definition).
- `fx_recorded_model_cost_contract` (Definition).
- `fx_recorded_successor_count_contract` (Definition).
- `fx_partial_model_erasure_contract` (Definition).
- `fx_partial_model_cost_contract` (Definition).
- `fx_local_step_erasure_contract` (Definition).
- `fx_local_walk_erasure_contract` (Definition).
- `fx_local_solve_erasure_contract` (Definition).
- `fx_local_checked_erasure_contract` (Definition).
- `fx_cut_model_erasure_contract` (Definition).
- `fx_narrow_checked_erasure_contract` (Definition).
- `fx_nested_machine_erasure_contract` (Definition).
- `fx_fullcheck_erasure_contract` (Definition).

## FixpointAuditCut

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_cut_set_nested_work` (Definition).
- `fx_cut_event` (Inductive).
- `fx_cut_map_mem` (Definition).
- `fx_cut_index_get` (Definition).
- `fx_cut_equal` (Definition).
- `fx_cut_store` (Definition).
- `fx_cut_seed` (Fixpoint).
- `fx_cut_prepare` (Fixpoint).
- `fx_cut_coverage_outputs` (Fixpoint).
- `fx_cut_coverage_constraints` (Fixpoint).
- `fx_cut_ready` (Definition).
- `fx_cut_ready_all` (Fixpoint).
- `fx_cut_join` (Fixpoint).
- `fx_cut_gather` (Fixpoint).
- `fx_cut_compute` (Fixpoint).
- `fx_cut_compare_value` (Definition).
- `fx_cut_check_sides` (Fixpoint).
- `fx_cut_check_constraints` (Fixpoint).
- `fx_cut_check_at` (Definition).
- `fx_cut_check_all` (Fixpoint).
- `fx_cut_expand_counted` (Definition).
- `fx_cut_model_erasure_statement` (Definition).
- `fx_cut_event_work` (Definition).
- `fx_cut_event_budget` (Definition).
- `fx_cut_work` (Definition).
- `fx_cut_budget` (Definition).
- `fx_cut_expand_selected_cost_statement` (Definition).
- `fx_cut_key_budget` (Definition).
- `fx_cut_write_budget` (Definition).
- `fx_cut_equal_budget` (Definition).
- `fx_cut_seed_budget` (Fixpoint).
- `fx_cut_prepare_budget` (Fixpoint).
- `fx_cut_coverage_outputs_budget` (Fixpoint).
- `fx_cut_coverage_constraints_budget` (Fixpoint).
- `fx_cut_ready_budget` (Fixpoint).
- `fx_cut_join_budget` (Fixpoint).
- `fx_cut_gather_budget` (Fixpoint).
- `fx_cut_compute_budget` (Fixpoint).
- `fx_cut_compare_budget` (Definition).
- `fx_cut_check_sides_budget` (Fixpoint).
- `fx_cut_check_constraints_budget` (Fixpoint).
- `fx_cut_check_all_budget` (Fixpoint).
- `fx_cut_elements_budget` (Definition).
- `fx_cut_expand_input_budget` (Definition).
- `fx_cut_expand_input_bound_statement` (Definition).
- `FxCutSetMem` (constructor of `fx_cut_event`).
- `FxCutSetAdd` (constructor of `fx_cut_event`).
- `FxCutMapGet` (constructor of `fx_cut_event`).
- `FxCutMapSet` (constructor of `fx_cut_event`).
- `FxCutIndexGet` (constructor of `fx_cut_event`).
- `FxCutElements` (constructor of `fx_cut_event`).
- `FxCutQuery` (constructor of `fx_cut_event`).
- `FxCutRhs` (constructor of `fx_cut_event`).
- `FxCutTarget` (constructor of `fx_cut_event`).
- `FxCutSides` (constructor of `fx_cut_event`).
- `FxCutEqual` (constructor of `fx_cut_event`).
- `FxCutJoin` (constructor of `fx_cut_event`).
- `FxCutLeb` (constructor of `fx_cut_event`).
- `FxCutBool` (constructor of `fx_cut_event`).
- `FxCutCase` (constructor of `fx_cut_event`).

Future proof module: `FixpointAuditCutAdequacy`.

- `fx_cut_model_erasure`: `FixpointAuditContractClosures.fx_cut_model_erasure_contract`; owner
  AUD-FX-CUT.
- `fx_cut_expand_selected_cost`: `FixpointAuditCut.fx_cut_expand_selected_cost_statement`; owner
  AUD-FX-CUT.
- `fx_cut_expand_input_bound`: `FixpointAuditCut.fx_cut_expand_input_bound_statement`; owner
  AUD-FX-CUT.

## FixpointAuditCutCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_cut_set_entries` (Definition).
- `fx_cut_entry_source` (Definition).
- `fx_cut_event_source` (Definition).
- `fx_cut_trace_source` (Definition).
- `fx_cut_source_laws` (Definition).
- `fx_cut_sides_bounded` (Definition).
- `fx_cut_event_external_budget` (Definition).
- `fx_cut_external_trace_budget` (Definition).
- `fx_cut_external_source_statement` (Definition).

Future proof module: `FixpointAuditCutCallbacksAdequacy`.

- `fx_cut_external_source_holds`: `FixpointAuditCutCallbacks.fx_cut_external_source_statement`;
  owner AUD-FX-CUT.

## FixpointAuditFallback

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_fallback_event` (Inductive).
- `fx_fallback_result` (Definition).
- `fx_recorded_fallback_counted` (Definition).
- `fx_nested_fallback_counted` (Definition).
- `fx_fallback_erasure_statement` (Definition).
- `fx_fallback_event_work` (Definition).
- `fx_fallback_work` (Definition).
- `fx_recorded_fallback_input_bound_statement` (Definition).
- `fx_nested_fallback_input_bound_statement` (Definition).
- `fx_fallback_apply_counted` (Definition).
- `fx_fallback_apply_statement` (Definition).
- `FxFallbackRecorded` (constructor of `fx_fallback_event`).
- `FxFallbackNested` (constructor of `fx_fallback_event`).
- `FxFallbackCase` (constructor of `fx_fallback_event`).

Future proof module: `FixpointAuditFallbackAdequacy`.

- `fx_fallback_erasure`: `FixpointAuditFallback.fx_fallback_erasure_statement`; owner
  AUD-FX-FALLBACK.
- `fx_recorded_fallback_input_bound`:
  `FixpointAuditFallback.fx_recorded_fallback_input_bound_statement`; owner AUD-FX-FALLBACK.
- `fx_nested_fallback_input_bound`:
  `FixpointAuditFallback.fx_nested_fallback_input_bound_statement`; owner AUD-FX-FALLBACK.
- `fx_fallback_apply`: `FixpointAuditFallback.fx_fallback_apply_statement`; owner AUD-FX-FALLBACK.

## FixpointAuditFallbackCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_fallback_event_source` (Definition).
- `fx_fallback_trace_source` (Definition).
- `fx_fallback_external_trace_budget` (Definition).
- `fx_recorded_fallback_external_source_statement` (Definition).
- `fx_nested_fallback_external_source_statement` (Definition).
- `fx_fallback_apply_external_source_statement` (Definition).

Future proof module: `FixpointAuditFallbackCallbacksAdequacy`.

- `fx_recorded_fallback_external_source`:
  `FixpointAuditFallbackCallbacks.fx_recorded_fallback_external_source_statement`; owner
  AUD-FX-FALLBACK.
- `fx_nested_fallback_external_source`:
  `FixpointAuditFallbackCallbacks.fx_nested_fallback_external_source_statement`; owner
  AUD-FX-FALLBACK.
- `fx_fallback_apply_external_source`:
  `FixpointAuditFallbackCallbacks.fx_fallback_apply_external_source_statement`; owner
  AUD-FX-FALLBACK.

## FixpointAuditFullCheck

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_check_external_model` (Record).
- `fx_check_external_erases` (Definition).
- `fx_check_nested_event` (Inductive).
- `fcn_lookup` (Definition).
- `fcn_query_run` (Inductive).
- `fcn_sides` (Fixpoint).
- `fcn_constraints_run` (Inductive).
- `fx_fullcheck_nested_run` (Definition).
- `fx_fullcheck_nested_erasure_statement` (Definition).
- `fx_fullcheck_nested_total_statement` (Definition).
- `fx_check_external_budget` (Record).
- `fx_check_body_work` (Definition).
- `fx_check_external_bounded` (Definition).
- `fx_check_nested_event_work` (Definition).
- `fx_check_nested_work` (Definition).
- `fx_check_nested_lookup_budget` (Definition).
- `fx_check_nested_query_budget` (Fixpoint).
- `fx_check_nested_sides_budget` (Fixpoint).
- `fx_check_nested_constraints_budget` (Fixpoint).
- `fx_fullcheck_nested_input_budget` (Definition).
- `fx_fullcheck_nested_input_bound_statement` (Definition).
- `fx_check_external_source` (Record).
- `fx_check_external_source_adequacy` (Definition).
- `fx_check_external_trace_adequacy` (Definition).
- `fx_fullcheck_external_source_statement` (Definition).
- `FxCheckExternalModel` (constructor of `fx_check_external_model`).
- `fx_check_encode_model` (field of `fx_check_external_model`).
- `fx_check_rhs_model` (field of `fx_check_external_model`).
- `fx_check_target_model` (field of `fx_check_external_model`).
- `fx_check_continue_model` (field of `fx_check_external_model`).
- `fx_check_leb_model` (field of `fx_check_external_model`).
- `FcnGet` (constructor of `fx_check_nested_event`).
- `FcnRhs` (constructor of `fx_check_nested_event`).
- `FcnTarget` (constructor of `fx_check_nested_event`).
- `FcnContinue` (constructor of `fx_check_nested_event`).
- `FcnLeb` (constructor of `fx_check_nested_event`).
- `FcnCase` (constructor of `fx_check_nested_event`).
- `FcnQueryRet` (constructor of `fcn_query_run`).
- `FcnQueryAsk` (constructor of `fcn_query_run`).
- `FcnQuerySide` (constructor of `fcn_query_run`).
- `FcnConstraintsNil` (constructor of `fcn_constraints_run`).
- `FcnConstraintsCons` (constructor of `fcn_constraints_run`).
- `FxCheckExternalBudget` (constructor of `fx_check_external_budget`).
- `fx_check_body_weight` (field of `fx_check_external_budget`).
- `fx_check_encode_bound` (field of `fx_check_external_budget`).
- `fx_check_rhs_bound` (field of `fx_check_external_budget`).
- `fx_check_target_bound` (field of `fx_check_external_budget`).
- `fx_check_continue_bound` (field of `fx_check_external_budget`).
- `fx_check_leb_bound` (field of `fx_check_external_budget`).
- `FxCheckExternalSource` (constructor of `fx_check_external_source`).
- `fx_check_encode_source` (field of `fx_check_external_source`).
- `fx_check_rhs_source` (field of `fx_check_external_source`).
- `fx_check_target_source` (field of `fx_check_external_source`).
- `fx_check_continue_source` (field of `fx_check_external_source`).
- `fx_check_leb_source` (field of `fx_check_external_source`).

Future proof module: `FixpointAuditFullCheckAdequacy`.

- `fx_fullcheck_nested_erasure`: `FixpointAuditFullCheck.fx_fullcheck_nested_erasure_statement`;
  owner AUD-FX-FULLCHECK.
- `fx_fullcheck_nested_total`: `FixpointAuditFullCheck.fx_fullcheck_nested_total_statement`; owner
  AUD-FX-FULLCHECK.
- `fx_fullcheck_nested_input_bound`:
  `FixpointAuditFullCheck.fx_fullcheck_nested_input_bound_statement`; owner AUD-FX-FULLCHECK.
- `fx_fullcheck_external_source`: `FixpointAuditFullCheck.fx_fullcheck_external_source_statement`;
  owner AUD-FX-FULLCHECK.

## FixpointAuditIndex

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_index_external_model` (Record).
- `fx_index_external_erases` (Definition).
- `fx_index_nested_event` (Inductive).
- `fxi_distinct_counted` (Definition).
- `fxi_push_many` (Fixpoint).
- `fxi_fold` (Fixpoint).
- `fx_index_nested_counted` (Definition).
- `fx_index_nested_erasure_statement` (Definition).
- `fx_index_external_budget` (Record).
- `fxi_body_work` (Definition).
- `fx_index_external_bounded` (Definition).
- `fxi_event_work` (Definition).
- `fx_index_adapter_work` (Definition).
- `fxi_set_input_budget` (Fixpoint).
- `fxi_distinct_input_budget` (Definition).
- `fxi_push_input_budget` (Fixpoint).
- `fxi_constraints_input_budget` (Fixpoint).
- `fx_index_nested_input_budget` (Definition).
- `fx_index_nested_input_bound_statement` (Definition).
- `fx_index_external_source` (Record).
- `fxi_set_external_adequacy` (Definition).
- `fx_index_external_trace_adequacy` (Definition).
- `fx_index_external_source_statement` (Definition).
- `FxIndexExternalModel` (constructor of `fx_index_external_model`).
- `fxi_encode` (field of `fx_index_external_model`).
- `fxi_target` (field of `fx_index_external_model`).
- `fxi_sides` (field of `fx_index_external_model`).
- `fxi_deps` (field of `fx_index_external_model`).
- `FxiTarget` (constructor of `fx_index_nested_event`).
- `FxiSides` (constructor of `fx_index_nested_event`).
- `FxiDeps` (constructor of `fx_index_nested_event`).
- `FxiDistinctBuild` (constructor of `fx_index_nested_event`).
- `FxiDistinctElements` (constructor of `fx_index_nested_event`).
- `FxiRead` (constructor of `fx_index_nested_event`).
- `FxiWrite` (constructor of `fx_index_nested_event`).
- `FxiCase` (constructor of `fx_index_nested_event`).
- `FxIndexExternalBudget` (constructor of `fx_index_external_budget`).
- `fxi_body_weight` (field of `fx_index_external_budget`).
- `fxi_encode_bound` (field of `fx_index_external_budget`).
- `fxi_target_bound` (field of `fx_index_external_budget`).
- `fxi_sides_bound` (field of `fx_index_external_budget`).
- `fxi_deps_bound` (field of `fx_index_external_budget`).
- `FxIndexExternalSource` (constructor of `fx_index_external_source`).
- `fxi_encode_source` (field of `fx_index_external_source`).
- `fxi_target_source` (field of `fx_index_external_source`).
- `fxi_sides_source` (field of `fx_index_external_source`).
- `fxi_deps_source` (field of `fx_index_external_source`).

Future proof module: `FixpointAuditIndexAdequacy`.

- `fx_index_nested_erasure`: `FixpointAuditIndex.fx_index_nested_erasure_statement`; owner
  AUD-FX-INDEX.
- `fx_index_nested_input_bound`: `FixpointAuditIndex.fx_index_nested_input_bound_statement`; owner
  AUD-FX-INDEX.
- `fx_index_external_source_holds`: `FixpointAuditIndex.fx_index_external_source_statement`; owner
  AUD-FX-INDEX.

## FixpointAuditLocal

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_local_input_bits` (Definition).
- `fx_local_full_event` (Inductive).
- `fx_local_roots_init` (Fixpoint).
- `local_solve_counted` (Definition).
- `fx_local_roots_checked` (Fixpoint).
- `local_checked_counted` (Definition).
- `fx_local_solve_erasure_statement` (Definition).
- `fx_local_checked_erasure_statement` (Definition).
- `fx_local_full_event_work` (Definition).
- `fx_local_full_event_budget` (Definition).
- `fx_local_full_work` (Definition).
- `fx_local_full_budget` (Definition).
- `fx_local_checked_selected_cost_statement` (Definition).
- `fx_local_roots_input_budget` (Fixpoint).
- `fx_local_region_build_budget` (Definition).
- `fx_local_solve_input_budget` (Definition).
- `fx_local_checked_input_budget` (Definition).
- `fx_local_checked_input_bound_statement` (Definition).
- `FxLocalClosureTrace` (constructor of `fx_local_full_event`).
- `FxLocalEngineTrace` (constructor of `fx_local_full_event`).
- `FxLocalPartialTrace` (constructor of `fx_local_full_event`).
- `FxLocalSelectedElements` (constructor of `fx_local_full_event`).
- `FxLocalRegionElements` (constructor of `fx_local_full_event`).
- `FxLocalRegionBuild` (constructor of `fx_local_full_event`).
- `FxLocalRootMem` (constructor of `fx_local_full_event`).
- `FxLocalFullCase` (constructor of `fx_local_full_event`).

Future proof module: `FixpointAuditLocalAdequacy`.

- `fx_local_solve_erasure`: `FixpointAuditContractClosures.fx_local_solve_erasure_contract`; owner
  AUD-FX-LOCAL.
- `fx_local_checked_erasure`: `FixpointAuditContractClosures.fx_local_checked_erasure_contract`;
  owner AUD-FX-LOCAL.
- `fx_local_checked_selected_cost`: `FixpointAuditLocal.fx_local_checked_selected_cost_statement`;
  owner AUD-FX-LOCAL.
- `fx_local_checked_input_bound`: `FixpointAuditLocal.fx_local_checked_input_bound_statement`; owner
  AUD-FX-LOCAL.

## FixpointAuditLocalCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_local_closure_event_source` (Definition).
- `fx_local_full_event_source` (Definition).
- `fx_local_trace_source` (Definition).
- `fx_local_deps_laws` (Definition).
- `fx_local_closure_event_budget` (Definition).
- `fx_local_full_event_external_budget` (Definition).
- `fx_local_external_trace_budget` (Definition).
- `fx_local_external_source_statement` (Definition).

Future proof module: `FixpointAuditLocalCallbacksAdequacy`.

- `fx_local_external_source_holds`:
  `FixpointAuditLocalCallbacks.fx_local_external_source_statement`; owner AUD-FX-LOCAL.

## FixpointAuditLocalClosure

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_local_event` (Inductive).
- `fx_local_inl` (Fixpoint).
- `fx_local_inr` (Fixpoint).
- `fx_local_step` (Definition).
- `fx_local_walk` (Fixpoint).
- `fx_local_step_erasure_statement` (Definition).
- `fx_local_walk_erasure_statement` (Definition).
- `fx_local_event_work` (Definition).
- `fx_local_event_budget` (Definition).
- `fx_local_work` (Definition).
- `fx_local_budget` (Definition).
- `fx_local_walk_selected_cost_statement` (Definition).
- `fx_local_step_input_budget` (Definition).
- `fx_local_walk_input_budget` (Fixpoint).
- `fx_local_walk_input_bound_statement` (Definition).
- `FxLocalUnknownMem` (constructor of `fx_local_event`).
- `FxLocalUnknownAdd` (constructor of `fx_local_event`).
- `FxLocalConstraintMem` (constructor of `fx_local_event`).
- `FxLocalConstraintAdd` (constructor of `fx_local_event`).
- `FxLocalContributors` (constructor of `fx_local_event`).
- `FxLocalDeps` (constructor of `fx_local_event`).
- `FxLocalFoldUnknown` (constructor of `fx_local_event`).
- `FxLocalFoldConstraint` (constructor of `fx_local_event`).
- `FxLocalCase` (constructor of `fx_local_event`).

Future proof module: `FixpointAuditLocalClosureAdequacy`.

- `fx_local_step_erasure`: `FixpointAuditContractClosures.fx_local_step_erasure_contract`; owner
  AUD-FX-LOCAL.
- `fx_local_walk_erasure`: `FixpointAuditContractClosures.fx_local_walk_erasure_contract`; owner
  AUD-FX-LOCAL.
- `fx_local_walk_selected_cost`: `FixpointAuditLocalClosure.fx_local_walk_selected_cost_statement`;
  owner AUD-FX-LOCAL.
- `fx_local_walk_input_bound`: `FixpointAuditLocalClosure.fx_local_walk_input_bound_statement`;
  owner AUD-FX-LOCAL.

## FixpointAuditLocalPartial

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_partial_event` (Inductive).
- `fx_partial_reads` (Fixpoint).
- `fx_partial_sides` (Fixpoint).
- `fx_partial_constraint` (Definition).
- `fx_partial_contributors` (Fixpoint).
- `fx_partial_unknowns` (Fixpoint).
- `check_partial_counted` (Definition).
- `fx_partial_model_erasure_statement` (Definition).
- `fx_partial_event_work` (Definition).
- `fx_partial_event_budget` (Definition).
- `fx_partial_work` (Definition).
- `fx_partial_budget` (Definition).
- `fx_partial_model_cost_statement` (Definition).
- `fx_partial_reads_input_budget` (Fixpoint).
- `fx_partial_sides_input_budget` (Fixpoint).
- `fx_partial_constraint_input_budget` (Definition).
- `fx_partial_contributors_input_budget` (Fixpoint).
- `fx_partial_unknowns_input_budget` (Fixpoint).
- `fx_partial_input_budget` (Definition).
- `fx_partial_input_bound_statement` (Definition).
- `FxPartialQuery` (constructor of `fx_partial_event`).
- `FxPartialRhs` (constructor of `fx_partial_event`).
- `FxPartialTarget` (constructor of `fx_partial_event`).
- `FxPartialLeb` (constructor of `fx_partial_event`).
- `FxPartialMem` (constructor of `fx_partial_event`).
- `FxPartialIndexGet` (constructor of `fx_partial_event`).
- `FxPartialElements` (constructor of `fx_partial_event`).
- `FxPartialNot` (constructor of `fx_partial_event`).
- `FxPartialAnd` (constructor of `fx_partial_event`).
- `FxPartialOr` (constructor of `fx_partial_event`).
- `FxPartialCase` (constructor of `fx_partial_event`).

Future proof module: `FixpointAuditLocalPartialAdequacy`.

- `fx_partial_model_erasure`: `FixpointAuditContractClosures.fx_partial_model_erasure_contract`;
  owner AUD-FX-PARTIALCHECK.
- `fx_partial_model_cost`: `FixpointAuditContractClosures.fx_partial_model_cost_contract`; owner
  AUD-FX-PARTIALCHECK.
- `fx_partial_input_bound`: `FixpointAuditLocalPartial.fx_partial_input_bound_statement`; owner
  AUD-FX-PARTIALCHECK.

## FixpointAuditNarrow

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_narrow_event` (Inductive).
- `fx_narrow_write` (Definition).
- `fx_narrow_collect` (Fixpoint).
- `fx_narrow_constraints` (Fixpoint).
- `fx_narrow_output` (Definition).
- `fx_narrow_outputs` (Fixpoint).
- `fx_narrow_pass` (Definition).
- `fx_narrow_iter` (Fixpoint).
- `fx_narrow_checked_counted` (Definition).
- `fx_narrow_checked_erasure_statement` (Definition).
- `fx_narrow_event_work` (Definition).
- `fx_narrow_event_budget` (Definition).
- `fx_narrow_work` (Definition).
- `fx_narrow_budget` (Definition).
- `fx_narrow_checked_selected_cost_statement` (Definition).
- `fx_narrow_discovery_rows_budget` (Fixpoint).
- `fx_narrow_discovery_input_budget` (Definition).
- `fx_narrow_collect_input_budget` (Fixpoint).
- `fx_narrow_constraints_input_budget` (Fixpoint).
- `fx_narrow_outputs_input_budget` (Fixpoint).
- `fx_narrow_pass_input_budget` (Definition).
- `fx_narrow_rounds_input_budget` (Fixpoint).
- `fx_narrow_checked_input_budget` (Definition).
- `fx_narrow_checked_input_bound_statement` (Definition).
- `fx_narrow_checked_run` (Inductive).
- `fx_narrow_run_total_statement` (Definition).
- `fx_narrow_run_correct_statement` (Definition).
- `FnarrowDep` (constructor of `fx_narrow_event`).
- `FnarrowQuery` (constructor of `fx_narrow_event`).
- `FnarrowCheck` (constructor of `fx_narrow_event`).
- `FnarrowRhs` (constructor of `fx_narrow_event`).
- `FnarrowTarget` (constructor of `fx_narrow_event`).
- `FnarrowJoin` (constructor of `fx_narrow_event`).
- `FnarrowLeb` (constructor of `fx_narrow_event`).
- `FnarrowNarrow` (constructor of `fx_narrow_event`).
- `FnarrowIndexGet` (constructor of `fx_narrow_event`).
- `FnarrowSet` (constructor of `fx_narrow_event`).
- `FnarrowCase` (constructor of `fx_narrow_event`).
- `FxNarrowCheckedRun` (constructor of `fx_narrow_checked_run`).

Future proof module: `FixpointAuditNarrowAdequacy`.

- `fx_narrow_checked_erasure`: `FixpointAuditContractClosures.fx_narrow_checked_erasure_contract`;
  owner AUD-FX-NARROW.
- `fx_narrow_checked_selected_cost`:
  `FixpointAuditNarrow.fx_narrow_checked_selected_cost_statement`; owner AUD-FX-NARROW.
- `fx_narrow_checked_input_bound`: `FixpointAuditNarrow.fx_narrow_checked_input_bound_statement`;
  owner AUD-FX-NARROW.
- `fx_narrow_run_total`: `FixpointAuditNarrow.fx_narrow_run_total_statement`; owner AUD-FX-NARROW.
- `fx_narrow_run_correct`: `FixpointAuditNarrow.fx_narrow_run_correct_statement`; owner
  AUD-FX-NARROW.

## FixpointAuditNarrowCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_narrow_extra_source` (Record).
- `fx_narrow_extra_budget` (Record).
- `fx_narrow_entries` (Definition).
- `fx_narrow_entry_source` (Definition).
- `fx_narrow_dep_source` (Definition).
- `fx_narrow_event_source` (Definition).
- `fx_narrow_trace_source` (Definition).
- `fx_narrow_entries_budget` (Definition).
- `fx_narrow_dep_budget` (Definition).
- `fx_narrow_event_external_budget` (Definition).
- `fx_narrow_external_trace_budget` (Definition).
- `fx_narrow_extra_laws` (Definition).
- `fx_narrow_core_laws` (Definition).
- `fx_narrow_external_source_statement` (Definition).
- `FxNarrowExtraSource` (constructor of `fx_narrow_extra_source`).
- `fx_narrow_sides_source` (field of `fx_narrow_extra_source`).
- `fx_narrow_operation_source` (field of `fx_narrow_extra_source`).
- `FxNarrowExtraBudget` (constructor of `fx_narrow_extra_budget`).
- `fx_narrow_sides_bound` (field of `fx_narrow_extra_budget`).
- `fx_narrow_operation_bound` (field of `fx_narrow_extra_budget`).

Future proof module: `FixpointAuditNarrowCallbacksAdequacy`.

- `fx_narrow_external_source`: `FixpointAuditNarrowCallbacks.fx_narrow_external_source_statement`;
  owner AUD-FX-NARROW.

## FixpointAuditNarrowCheck

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_fullcheck_event` (Inductive).
- `fx_fullcheck_sides` (Fixpoint).
- `fx_fullcheck_constraints` (Fixpoint).
- `fx_fullcheck_counted` (Definition).
- `fx_fullcheck_erasure_statement` (Definition).
- `fx_fullcheck_event_work` (Definition).
- `fx_fullcheck_event_budget` (Definition).
- `fx_fullcheck_work` (Definition).
- `fx_fullcheck_budget` (Definition).
- `fx_fullcheck_selected_cost_statement` (Definition).
- `fx_fullcheck_sides_input_budget` (Fixpoint).
- `fx_fullcheck_constraints_input_budget` (Fixpoint).
- `fx_fullcheck_input_budget` (Definition).
- `fx_fullcheck_input_bound_statement` (Definition).
- `FfcQuery` (constructor of `fx_fullcheck_event`).
- `FfcRhs` (constructor of `fx_fullcheck_event`).
- `FfcTarget` (constructor of `fx_fullcheck_event`).
- `FfcLeb` (constructor of `fx_fullcheck_event`).
- `FfcAnd` (constructor of `fx_fullcheck_event`).
- `FfcCase` (constructor of `fx_fullcheck_event`).

Future proof module: `FixpointAuditNarrowCheckAdequacy`.

- `fx_fullcheck_erasure`: `FixpointAuditContractClosures.fx_fullcheck_erasure_contract`; owner
  AUD-FX-FULLCHECK.
- `fx_fullcheck_selected_cost`: `FixpointAuditNarrowCheck.fx_fullcheck_selected_cost_statement`;
  owner AUD-FX-FULLCHECK.
- `fx_fullcheck_input_bound`: `FixpointAuditNarrowCheck.fx_fullcheck_input_bound_statement`; owner
  AUD-FX-FULLCHECK.

## FixpointAuditNarrowDiscovery

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_dependency_event` (Inductive).
- `fx_dependency_distinct` (Definition).
- `fx_dependency_outputs_input` (Fixpoint).
- `fx_index_input_bits` (Definition).
- `fx_dependency_event_work` (Definition).
- `fx_dependency_event_budget` (Definition).
- `fx_dependency_work` (Definition).
- `fx_dependency_budget` (Definition).
- `FxDepTarget` (constructor of `fx_dependency_event`).
- `FxDepSides` (constructor of `fx_dependency_event`).
- `FxDepDistinct` (constructor of `fx_dependency_event`).
- `FxDepAppend` (constructor of `fx_dependency_event`).
- `FxDepCase` (constructor of `fx_dependency_event`).

## FixpointAuditNested

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_nested_whole_event` (Inductive).
- `fx_nested_run_counted` (Definition).
- `fx_nested_run_erasure_statement` (Definition).
- `fx_nested_whole_event_work` (Definition).
- `fx_nested_whole_work` (Definition).
- `fx_nested_run_input_budget` (Definition).
- `fx_nested_run_input_bound_statement` (Definition).
- `fx_nested_run_model_relation` (Inductive).
- `fx_nested_run_model_total_statement` (Definition).
- `fx_nested_run_model_correct_statement` (Definition).
- `FnWholeDependency` (constructor of `fx_nested_whole_event`).
- `FnWholePrepare` (constructor of `fx_nested_whole_event`).
- `FnWholeWto` (constructor of `fx_nested_whole_event`).
- `FnWholePlan` (constructor of `fx_nested_whole_event`).
- `FnWholeMachine` (constructor of `fx_nested_whole_event`).
- `FnWholeCase` (constructor of `fx_nested_whole_event`).
- `FxNestedRunModel` (constructor of `fx_nested_run_model_relation`).

Future proof module: `FixpointAuditNestedAdequacy`.

- `fx_nested_run_erasure`: `FixpointAuditNested.fx_nested_run_erasure_statement`; owner
  AUD-FX-NESTED.
- `fx_nested_run_input_bound`: `FixpointAuditNested.fx_nested_run_input_bound_statement`; owner
  AUD-FX-NESTED.
- `fx_nested_run_model_total`: `FixpointAuditNested.fx_nested_run_model_total_statement`; owner
  AUD-FX-NESTED.
- `fx_nested_run_model_correct`: `FixpointAuditNested.fx_nested_run_model_correct_statement`; owner
  AUD-FX-NESTED.

## FixpointAuditNestedCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_nested_entries` (Definition).
- `fx_nested_entry_source` (Definition).
- `fx_nested_plan_event_source` (Definition).
- `fx_nested_machine_event_source` (Definition).
- `fx_nested_wto_event_source` (Definition).
- `fx_nested_whole_event_source` (Definition).
- `fx_nested_trace_source` (Definition).
- `fx_nested_entries_budget` (Definition).
- `fx_nested_plan_external_budget` (Definition).
- `fx_nested_machine_external_budget` (Definition).
- `fx_nested_external_trace_budget` (Definition).
- `fx_nested_machine_source_laws` (Definition).
- `fx_nested_external_source_statement` (Definition).

Future proof module: `FixpointAuditNestedCallbacksAdequacy`.

- `fx_nested_external_source`: `FixpointAuditNestedCallbacks.fx_nested_external_source_statement`;
  owner AUD-FX-NESTED.

## FixpointAuditNestedMachine

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_nested_event` (Inductive).
- `fx_nested_mark_heads` (Fixpoint).
- `fx_nested_mark` (Definition).
- `fx_nested_raise` (Definition).
- `fx_nested_update` (Definition).
- `fx_nested_updates` (Fixpoint).
- `fx_nested_step` (Definition).
- `fx_nested_tick` (Definition).
- `fx_nested_loop` (Fixpoint).
- `fx_nested_machine_erasure_statement` (Definition).
- `fx_nested_event_work` (Definition).
- `fx_nested_event_budget` (Definition).
- `fx_nested_work` (Definition).
- `fx_nested_budget` (Definition).
- `fx_nested_loop_selected_cost_statement` (Definition).
- `fx_nested_mark_input_budget` (Fixpoint).
- `fx_nested_update_input_budget` (Definition).
- `fx_nested_updates_input_budget` (Fixpoint).
- `fx_nested_step_input_budget` (Definition).
- `fx_nested_tick_input_budget` (Definition).
- `fx_nested_loop_input_budget` (Fixpoint).
- `fx_nested_loop_input_bound_statement` (Definition).
- `FxNestedQuery` (constructor of `fx_nested_event`).
- `FxNestedRhs` (constructor of `fx_nested_event`).
- `FxNestedTarget` (constructor of `fx_nested_event`).
- `FxNestedLeb` (constructor of `fx_nested_event`).
- `FxNestedJoin` (constructor of `fx_nested_event`).
- `FxNestedWiden` (constructor of `fx_nested_event`).
- `FxNestedMapGet` (constructor of `fx_nested_event`).
- `FxNestedTargetsGet` (constructor of `fx_nested_event`).
- `FxNestedValueSet` (constructor of `fx_nested_event`).
- `FxNestedSetMem` (constructor of `fx_nested_event`).
- `FxNestedSetAdd` (constructor of `fx_nested_event`).
- `FxNestedSetRemove` (constructor of `fx_nested_event`).
- `FxNestedCase` (constructor of `fx_nested_event`).

Future proof module: `FixpointAuditNestedMachineAdequacy`.

- `fx_nested_machine_erasure`: `FixpointAuditContractClosures.fx_nested_machine_erasure_contract`;
  owner AUD-FX-NESTED.
- `fx_nested_loop_selected_cost`:
  `FixpointAuditNestedMachine.fx_nested_loop_selected_cost_statement`; owner AUD-FX-NESTED.
- `fx_nested_loop_input_bound`: `FixpointAuditNestedMachine.fx_nested_loop_input_bound_statement`;
  owner AUD-FX-NESTED.

## FixpointAuditNestedPlan

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_nested_plan_event` (Inductive).
- `fx_nested_parse` (Fixpoint).
- `fx_nested_tree` (Definition).
- `fx_nested_rows` (Fixpoint).
- `fx_nested_heads` (Fixpoint).
- `fx_nested_member_fold` (Fixpoint).
- `fx_nested_members` (Definition).
- `fx_nested_target_fold` (Fixpoint).
- `fx_nested_targets` (Definition).
- `fx_nested_plan_from_tokens` (Definition).
- `fx_nested_plan_semantic_statement` (Definition).
- `fx_nested_plan_event_work` (Definition).
- `fx_nested_plan_event_budget` (Definition).
- `fx_nested_plan_work` (Definition).
- `fx_nested_plan_budget` (Definition).
- `fx_nested_plan_selected_cost_statement` (Definition).
- `fx_nested_plan_input_budget` (Definition).
- `fx_nested_plan_input_bound_statement` (Definition).
- `FnpParse` (constructor of `fx_nested_plan_event`).
- `FnpRows` (constructor of `fx_nested_plan_event`).
- `FnpHeads` (constructor of `fx_nested_plan_event`).
- `FnpLength` (constructor of `fx_nested_plan_event`).
- `FnpAppend` (constructor of `fx_nested_plan_event`).
- `FnpTarget` (constructor of `fx_nested_plan_event`).
- `FnpMembersSet` (constructor of `fx_nested_plan_event`).
- `FnpTargetRead` (constructor of `fx_nested_plan_event`).
- `FnpTargetWrite` (constructor of `fx_nested_plan_event`).
- `FnpHeadsSet` (constructor of `fx_nested_plan_event`).
- `FnpCase` (constructor of `fx_nested_plan_event`).

Future proof module: `FixpointAuditNestedPlanAdequacy`.

- `fx_nested_plan_semantic`: `FixpointAuditNestedPlan.fx_nested_plan_semantic_statement`; owner
  AUD-FX-NESTED.
- `fx_nested_plan_selected_cost`: `FixpointAuditNestedPlan.fx_nested_plan_selected_cost_statement`;
  owner AUD-FX-NESTED.
- `fx_nested_plan_input_bound`: `FixpointAuditNestedPlan.fx_nested_plan_input_bound_statement`;
  owner AUD-FX-NESTED.

## FixpointAuditPartialCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_local_partial_event_source` (Definition).
- `fx_local_partial_event_budget` (Definition).
- `fx_partial_rooted_trace_source` (Definition).
- `fx_partial_rooted_external_budget` (Definition).
- `fx_partial_rooted_source_statement` (Definition).

Future proof module: `FixpointAuditPartialCallbacksAdequacy`.

- `fx_partial_rooted_source`: `FixpointAuditPartialCallbacks.fx_partial_rooted_source_statement`;
  owner AUD-FX-PARTIALCHECK.

## FixpointAuditPartialCheck

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_partial_nested_event` (Inductive).
- `fpn_reads` (Fixpoint).
- `fpn_sides` (Fixpoint).
- `fpn_constraint_run` (Inductive).
- `fpn_constraints_run` (Inductive).
- `fpn_unknowns_run` (Inductive).
- `fx_partial_nested_run` (Inductive).
- `fx_partial_nested_erasure_statement` (Definition).
- `fx_partial_nested_total_statement` (Definition).
- `fpn_event_work` (Definition).
- `fx_partial_nested_work` (Definition).
- `fpn_mem_budget` (Definition).
- `fpn_reads_budget` (Fixpoint).
- `fpn_sides_budget` (Fixpoint).
- `fpn_constraint_budget` (Definition).
- `fpn_constraints_budget` (Fixpoint).
- `fpn_unknowns_budget` (Fixpoint).
- `fx_partial_nested_input_budget` (Definition).
- `fx_partial_nested_input_bound_statement` (Definition).
- `fpn_set_source_adequacy` (Definition).
- `fpn_map_source_adequacy` (Definition).
- `fx_partial_external_trace_adequacy` (Definition).
- `fx_partial_external_source_statement` (Definition).
- `FpnCheck` (constructor of `fx_partial_nested_event`).
- `FpnMem` (constructor of `fx_partial_nested_event`).
- `FpnIndex` (constructor of `fx_partial_nested_event`).
- `FpnElements` (constructor of `fx_partial_nested_event`).
- `FpnCase` (constructor of `fx_partial_nested_event`).
- `FpnConstraint` (constructor of `fpn_constraint_run`).
- `FpnConstraintsNil` (constructor of `fpn_constraints_run`).
- `FpnConstraintsCons` (constructor of `fpn_constraints_run`).
- `FpnUnknownsNil` (constructor of `fpn_unknowns_run`).
- `FpnUnknownsCons` (constructor of `fpn_unknowns_run`).
- `FpnRun` (constructor of `fx_partial_nested_run`).

Future proof module: `FixpointAuditPartialCheckAdequacy`.

- `fx_partial_nested_erasure`: `FixpointAuditPartialCheck.fx_partial_nested_erasure_statement`;
  owner AUD-FX-PARTIALCHECK.
- `fx_partial_nested_total`: `FixpointAuditPartialCheck.fx_partial_nested_total_statement`; owner
  AUD-FX-PARTIALCHECK.
- `fx_partial_nested_input_bound`:
  `FixpointAuditPartialCheck.fx_partial_nested_input_bound_statement`; owner AUD-FX-PARTIALCHECK.
- `fx_partial_external_source`: `FixpointAuditPartialCheck.fx_partial_external_source_statement`;
  owner AUD-FX-PARTIALCHECK.

## FixpointAuditRecorded

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_index_set_nested_work` (Definition).
- `fx_recorded_event` (Inductive).
- `fx_recorded_read_one` (Definition).
- `fx_record_reads_counted` (Fixpoint).
- `fx_recorded_readers_counted` (Definition).
- `fx_record_reads_erasure_statement` (Definition).
- `fx_record_reads_count_statement` (Definition).
- `fx_recorded_readers_erasure_statement` (Definition).
- `fx_recorded_update` (Definition).
- `fx_recorded_updates` (Fixpoint).
- `fx_recorded_step` (Definition).
- `fx_recorded_loop` (Fixpoint).
- `run_worklist_recorded_model` (Definition).
- `fx_recorded_model_erasure_statement` (Definition).
- `fx_recorded_event_work` (Definition).
- `fx_recorded_work` (Definition).
- `fx_recorded_event_budget` (Definition).
- `fx_recorded_budget` (Definition).
- `fx_recorded_base_calls` (Fixpoint).
- `fx_recorded_model_cost_statement` (Definition).
- `fx_recorded_successor_count_statement` (Definition).
- `FxRecordedBase` (constructor of `fx_recorded_event`).
- `FxRecordedRead` (constructor of `fx_recorded_event`).
- `FxRecordedReaders` (constructor of `fx_recorded_event`).
- `FxRecordedWrite` (constructor of `fx_recorded_event`).
- `FxRecordedCompare` (constructor of `fx_recorded_event`).
- `FxRecordedCase` (constructor of `fx_recorded_event`).

Future proof module: `FixpointAuditRecordedAdequacy`.

- `fx_record_reads_erasure`: `FixpointAuditRecorded.fx_record_reads_erasure_statement`; owner
  AUD-FX-RECORDED.
- `fx_record_reads_count`: `FixpointAuditRecorded.fx_record_reads_count_statement`; owner
  AUD-FX-RECORDED.
- `fx_recorded_readers_erasure`: `FixpointAuditRecorded.fx_recorded_readers_erasure_statement`;
  owner AUD-FX-RECORDED.
- `fx_recorded_model_erasure`: `FixpointAuditContractClosures.fx_recorded_model_erasure_contract`;
  owner AUD-FX-RECORDED.
- `fx_recorded_model_cost`: `FixpointAuditContractClosures.fx_recorded_model_cost_contract`; owner
  AUD-FX-RECORDED.
- `fx_recorded_successor_count`:
  `FixpointAuditContractClosures.fx_recorded_successor_count_contract`; owner AUD-FX-RECORDED.

## FixpointAuditRecordedBudget

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_record_reads_input_budget` (Fixpoint).
- `fx_recorded_update_input_budget` (Definition).
- `fx_recorded_updates_input_budget` (Fixpoint).
- `fx_recorded_step_input_budget` (Definition).
- `fx_recorded_loop_input_budget` (Fixpoint).
- `fx_recorded_run_input_budget` (Definition).
- `fx_recorded_run_input_bound_statement` (Definition).

Future proof module: `FixpointAuditRecordedBudgetAdequacy`.

- `fx_recorded_run_input_bound`:
  `FixpointAuditRecordedBudget.fx_recorded_run_input_bound_statement`; owner AUD-FX-RECORDED.

## FixpointAuditRecordedCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_recorded_set_entries` (Definition).
- `fx_recorded_event_source` (Definition).
- `fx_recorded_trace_source` (Definition).
- `fx_recorded_event_external_budget` (Definition).
- `fx_recorded_external_trace_budget` (Definition).
- `fx_recorded_external_source_statement` (Definition).

Future proof module: `FixpointAuditRecordedCallbacksAdequacy`.

- `fx_recorded_external_source`:
  `FixpointAuditRecordedCallbacks.fx_recorded_external_source_statement`; owner AUD-FX-RECORDED.

## FixpointAuditSchedule

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `audit_rpo_schedule_event` (Inductive).
- `audit_rpo_schedule_positions` (Fixpoint).
- `audit_rpo_schedule_priority` (Definition).
- `audit_rpo_schedule_widening` (Definition).
- `audit_rpo_schedule_positions_statement` (Definition).
- `audit_rpo_schedule_callbacks_statement` (Definition).
- `audit_rpo_graph_callbacks` (Record).
- `audit_rpo_graph_event` (Inductive).
- `audit_rpo_graph_ancestor` (Definition).
- `audit_rpo_graph_filter` (Fixpoint).
- `audit_rpo_graph_targets` (Fixpoint).
- `audit_rpo_graph_collect` (Fixpoint).
- `audit_rpo_graph_add_all` (Fixpoint).
- `audit_rpo_schedule_retreats` (Definition).
- `audit_rpo_graph_callbacks_erase` (Definition).
- `audit_rpo_schedule_retreats_statement` (Definition).
- `audit_rpo_schedule_event_work` (Definition).
- `audit_rpo_graph_event_work` (Definition).
- `audit_rpo_schedule_event_body` (Definition).
- `audit_rpo_graph_event_body` (Definition).
- `audit_rpo_schedule_work` (Definition).
- `audit_rpo_schedule_body_work` (Definition).
- `audit_rpo_graph_work` (Definition).
- `audit_rpo_graph_body_work` (Definition).
- `audit_rpo_positions_budget` (Definition).
- `audit_rpo_graph_budget` (Definition).
- `audit_rpo_positions_bound_statement` (Definition).
- `audit_rpo_retreats_bound_statement` (Definition).
- `audit_rpo_schedule_query_bound_statement` (Definition).
- `audit_rpo_schedule_event_budget` (Definition).
- `audit_rpo_graph_event_budget` (Definition).
- `audit_rpo_positions_adapted_statement` (Definition).
- `audit_rpo_retreats_adapted_statement` (Definition).
- `audit_rpo_successor_source_obligations` (Definition).
- `RpoScheduleCase` (constructor of `audit_rpo_schedule_event`).
- `RpoScheduleNext` (constructor of `audit_rpo_schedule_event`).
- `RpoScheduleMap` (constructor of `audit_rpo_schedule_event`).
- `RpoScheduleSet` (constructor of `audit_rpo_schedule_event`).
- `AuditRpoGraphCallbacks` (constructor of `audit_rpo_graph_callbacks`).
- `audit_rpo_graph_encode` (field of `audit_rpo_graph_callbacks`).
- `audit_rpo_graph_out` (field of `audit_rpo_graph_callbacks`).
- `audit_rpo_graph_source` (field of `audit_rpo_graph_callbacks`).
- `audit_rpo_graph_target` (field of `audit_rpo_graph_callbacks`).
- `RpoGraphCase` (constructor of `audit_rpo_graph_event`).
- `RpoGraphOut` (constructor of `audit_rpo_graph_event`).
- `RpoGraphSource` (constructor of `audit_rpo_graph_event`).
- `RpoGraphTarget` (constructor of `audit_rpo_graph_event`).
- `RpoGraphRank` (constructor of `audit_rpo_graph_event`).
- `RpoGraphSet` (constructor of `audit_rpo_graph_event`).
- `RpoGraphCompare` (constructor of `audit_rpo_graph_event`).

Future proof module: `FixpointAuditScheduleAdequacy`.

- `audit_rpo_schedule_positions_erases`:
  `FixpointAuditSchedule.audit_rpo_schedule_positions_statement`; owner AUD-FX-SCHEDULE.
- `audit_rpo_schedule_callbacks_erases`:
  `FixpointAuditSchedule.audit_rpo_schedule_callbacks_statement`; owner AUD-FX-SCHEDULE.
- `audit_rpo_schedule_retreats_erases`:
  `FixpointAuditSchedule.audit_rpo_schedule_retreats_statement`; owner AUD-FX-SCHEDULE.
- `audit_rpo_positions_bound_correct`: `FixpointAuditSchedule.audit_rpo_positions_bound_statement`;
  owner AUD-FX-SCHEDULE.
- `audit_rpo_retreats_bound_correct`: `FixpointAuditSchedule.audit_rpo_retreats_bound_statement`;
  owner AUD-FX-SCHEDULE.
- `audit_rpo_schedule_query_bound_correct`:
  `FixpointAuditSchedule.audit_rpo_schedule_query_bound_statement`; owner AUD-FX-SCHEDULE.
- `audit_rpo_positions_adapted_correct`:
  `FixpointAuditSchedule.audit_rpo_positions_adapted_statement`; owner AUD-FX-SCHEDULE.
- `audit_rpo_retreats_adapted_correct`:
  `FixpointAuditSchedule.audit_rpo_retreats_adapted_statement`; owner AUD-FX-SCHEDULE.

## FixpointAuditScheduleWrapper

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_dep_event` (Inductive).
- `fx_dep_unknowns_input` (Fixpoint).
- `fx_dep_outputs_input` (Fixpoint).
- `fx_dep_out` (Definition).
- `fx_dep_graph_build` (Definition).
- `fx_dep_encoder` (Definition).
- `fx_dep_prepare_cb` (Definition).
- `fx_dep_dfs_cb` (Definition).
- `fx_dep_rpo_cb` (Definition).
- `fx_dep_event_work` (Definition).
- `fx_dep_events_work` (Definition).
- `fx_dep_build_erasure_statement` (Definition).
- `fx_dep_out_erasure_statement` (Definition).
- `fx_rpo_result` (Record).
- `fx_rpo_scheduler_counted` (Definition).
- `fx_rpo_scheduler_erasure_statement` (Definition).
- `fx_rpo_scheduler_work` (Definition).
- `fx_dep_unknowns_native` (Definition).
- `fx_dep_out_values_native` (Definition).
- `fx_dep_callback_budget` (Definition).
- `fx_dep_build_budget` (Definition).
- `fx_dep_out_budget` (Definition).
- `fx_dep_build_bound_statement` (Definition).
- `fx_dep_out_bound_statement` (Definition).
- `fx_rpo_callback_max` (Definition).
- `fx_rpo_receipt_count_limit` (Definition).
- `fx_rpo_scheduler_budget` (Definition).
- `fx_rpo_scheduler_input_bound_statement` (Definition).
- `fx_dep_source_laws` (Definition).
- `fx_dep_event_source` (Definition).
- `fx_dep_body_source` (Definition).
- `fx_dep_map_source` (Definition).
- `fx_dep_set_source` (Definition).
- `fx_dep_prepare_source` (Definition).
- `fx_dep_dfs_source` (Definition).
- `fx_dep_positions_source` (Definition).
- `fx_dep_retreat_source` (Definition).
- `fx_rpo_scheduler_source_statement` (Definition).
- `fx_rpo_receipt_count_statement` (Definition).
- `fx_rpo_fast_reverse_statement` (Definition).
- `FxDepIndexEvent` (constructor of `fx_dep_event`).
- `FxDepEncode` (constructor of `fx_dep_event`).
- `FxDepCase` (constructor of `fx_dep_event`).
- `FxDepListWork` (constructor of `fx_dep_event`).
- `FxRpoResult` (constructor of `fx_rpo_result`).
- `fx_rpo_positions` (field of `fx_rpo_result`).
- `fx_rpo_heads` (field of `fx_rpo_result`).
- `fx_rpo_reverse_input` (field of `fx_rpo_result`).
- `fx_rpo_reverse_output` (field of `fx_rpo_result`).
- `fx_rpo_reverse_work` (field of `fx_rpo_result`).
- `fx_rpo_build_events` (field of `fx_rpo_result`).
- `fx_rpo_prepare_events` (field of `fx_rpo_result`).
- `fx_rpo_dfs_events` (field of `fx_rpo_result`).
- `fx_rpo_position_events` (field of `fx_rpo_result`).
- `fx_rpo_retreat_events` (field of `fx_rpo_result`).

Future proof module: `FixpointAuditScheduleWrapperAdequacy`.

- `fx_dep_build_erasure_correct`: `FixpointAuditScheduleWrapper.fx_dep_build_erasure_statement`;
  owner AUD-FX-SCHEDULE.
- `fx_dep_out_erasure_correct`: `FixpointAuditScheduleWrapper.fx_dep_out_erasure_statement`; owner
  AUD-FX-SCHEDULE.
- `fx_rpo_scheduler_erasure_correct`:
  `FixpointAuditScheduleWrapper.fx_rpo_scheduler_erasure_statement`; owner AUD-FX-SCHEDULE.
- `fx_dep_build_bound_correct`: `FixpointAuditScheduleWrapper.fx_dep_build_bound_statement`; owner
  AUD-FX-SCHEDULE.
- `fx_dep_out_bound_correct`: `FixpointAuditScheduleWrapper.fx_dep_out_bound_statement`; owner
  AUD-FX-SCHEDULE.
- `fx_rpo_scheduler_input_bound_correct`:
  `FixpointAuditScheduleWrapper.fx_rpo_scheduler_input_bound_statement`; owner AUD-FX-SCHEDULE.
- `fx_rpo_scheduler_source_correct`:
  `FixpointAuditScheduleWrapper.fx_rpo_scheduler_source_statement`; owner AUD-FX-SCHEDULE.
- `fx_rpo_receipt_count_correct`: `FixpointAuditScheduleWrapper.fx_rpo_receipt_count_statement`;
  owner AUD-FX-SCHEDULE.
- `fx_rpo_fast_reverse_correct`: `FixpointAuditScheduleWrapper.fx_rpo_fast_reverse_statement`; owner
  AUD-FX-SCHEDULE.

## FixpointAuditTotal

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_total_weight_bound` (Definition).
- `fx_total_queue_bound` (Definition).
- `fx_total_join_step_bound` (Definition).
- `fx_total_widen_step_bound` (Definition).
- `fx_total_callbacks_run` (Inductive).
- `fx_total_callbacks_realization_statement` (Definition).
- `fx_total_callbacks_erasure_statement` (Definition).
- `fx_total_callbacks_source_statement` (Definition).
- `fx_total_callbacks_join_work_statement` (Definition).
- `fx_total_callbacks_widen_work_statement` (Definition).
- `FxTotalCallbacksRun` (constructor of `fx_total_callbacks_run`).

Future proof module: `FixpointAuditTotalAdequacy`.

- `fx_total_callbacks_realization`: `FixpointAuditTotal.fx_total_callbacks_realization_statement`;
  owner AUD-FX-TOTAL.
- `fx_total_callbacks_erasure`: `FixpointAuditTotal.fx_total_callbacks_erasure_statement`; owner
  AUD-FX-TOTAL.
- `fx_total_callbacks_source`: `FixpointAuditTotal.fx_total_callbacks_source_statement`; owner
  AUD-FX-TOTAL.
- `fx_total_callbacks_join_work`: `FixpointAuditTotal.fx_total_callbacks_join_work_statement`; owner
  AUD-FX-TOTAL.
- `fx_total_callbacks_widen_work`: `FixpointAuditTotal.fx_total_callbacks_widen_work_statement`;
  owner AUD-FX-TOTAL.

## FixpointAuditWorklist

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_encoder_entry` (Inductive).
- `fx_index_encoder` (Definition).
- `fx_declared_call` (Inductive).
- `fx_queue_internal_charge` (Definition).
- `fx_model_lookup` (Definition).
- `fx_model_query` (Fixpoint).
- `fx_model_enqueue` (Fixpoint).
- `fx_model_raise` (Definition).
- `fx_model_update` (Definition).
- `fx_model_updates` (Fixpoint).
- `fx_model_step` (Definition).
- `fx_model_loop` (Fixpoint).
- `run_worklist_declared_model` (Definition).
- `fx_declared_model_erasure_statement` (Definition).
- `fx_declared_call_charge` (Definition).
- `fx_declared_model_work` (Fixpoint).
- `fx_declared_primitive_budget` (Fixpoint).
- `run_worklist_declared_model_cost_statement` (Definition).
- `fx_declared_total_engine_run` (Inductive).
- `fx_declared_total_engine_total_statement` (Definition).
- `fx_declared_total_engine_erases_statement` (Definition).
- `total_solver_map_model_execution_statement` (Definition).
- `FxTarget` (constructor of `fx_declared_call`).
- `FxPriority` (constructor of `fx_declared_call`).
- `FxWideningPoint` (constructor of `fx_declared_call`).
- `FxRhs` (constructor of `fx_declared_call`).
- `FxContinuation` (constructor of `fx_declared_call`).
- `FxLeb` (constructor of `fx_declared_call`).
- `FxJoin` (constructor of `fx_declared_call`).
- `FxWiden` (constructor of `fx_declared_call`).
- `FxGet` (constructor of `fx_declared_call`).
- `FxSet` (constructor of `fx_declared_call`).
- `FxReaders` (constructor of `fx_declared_call`).
- `FxPush` (constructor of `fx_declared_call`).
- `FxPop` (constructor of `fx_declared_call`).
- `FxTotalEngineStop` (constructor of `fx_declared_total_engine_run`).
- `FxTotalEngineContinue` (constructor of `fx_declared_total_engine_run`).
- `FxEncodeEntry` (constructor of `fx_encoder_entry`).

Future proof module: `FixpointAuditWorklistAdequacy`.

- `fx_declared_model_erasure`: `FixpointAuditContractClosures.fx_declared_model_erasure_contract`;
  owner AUD-FX-WORKLIST.
- `run_worklist_declared_model_cost`:
  `FixpointAuditContractClosures.run_worklist_declared_model_cost_contract`; owner AUD-FX-WORKLIST.
- `fx_declared_total_engine_total`:
  `FixpointAuditContractClosures.fx_declared_total_engine_total_contract`; owner AUD-FX-WORKLIST.
- `fx_declared_total_engine_erases`:
  `FixpointAuditContractClosures.fx_declared_total_engine_erases_contract`; owner AUD-FX-WORKLIST.
- `total_solver_map_model_execution`:
  `FixpointAuditWorklist.total_solver_map_model_execution_statement`; owner AUD-FX-WORKLIST.

## FixpointAuditWorklistBudget

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_fullcheck_lookup_input_budget` (Definition).
- `fx_fullcheck_query_input_budget` (Fixpoint).
- `fx_declared_push_input_budget` (Definition).
- `fx_declared_pop_input_budget` (Definition).
- `fx_declared_enqueue_input_budget` (Fixpoint).
- `fx_declared_update_input_budget` (Definition).
- `fx_declared_updates_input_budget` (Fixpoint).
- `fx_declared_step_input_budget` (Definition).
- `fx_declared_loop_input_budget` (Fixpoint).
- `fx_declared_run_input_budget` (Definition).
- `fx_declared_run_input_bound_statement` (Definition).

Future proof module: `FixpointAuditWorklistBudgetAdequacy`.

- `fx_declared_run_input_bound`:
  `FixpointAuditWorklistBudget.fx_declared_run_input_bound_statement`; owner AUD-FX-WORKLIST.

## FixpointAuditWorklistCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_declared_callback_source` (Record).
- `fx_queue_encoder_entries` (Definition).
- `fx_queue_encoder_source` (Definition).
- `fx_declared_call_source` (Definition).
- `fx_declared_event_source` (Definition).
- `fx_declared_trace_source` (Definition).
- `fx_declared_body_work` (Definition).
- `fx_declared_query_reachable` (Inductive).
- `fx_declared_source_laws` (Definition).
- `fx_declared_callback_budget` (Record).
- `fx_one_body_work` (Definition).
- `fx_declared_callback_bounded` (Definition).
- `fx_queue_entry_budget` (Definition).
- `fx_declared_external_call_budget` (Definition).
- `fx_declared_external_trace_budget` (Definition).
- `fx_declared_external_source_statement` (Definition).
- `FxDeclaredCallbackSource` (constructor of `fx_declared_callback_source`).
- `fx_source_encode_x` (field of `fx_declared_callback_source`).
- `fx_source_encode_c` (field of `fx_declared_callback_source`).
- `fx_source_target` (field of `fx_declared_callback_source`).
- `fx_source_priority` (field of `fx_declared_callback_source`).
- `fx_source_widening_point` (field of `fx_declared_callback_source`).
- `fx_source_rhs` (field of `fx_declared_callback_source`).
- `fx_source_continuation` (field of `fx_declared_callback_source`).
- `fx_source_leb` (field of `fx_declared_callback_source`).
- `fx_source_join` (field of `fx_declared_callback_source`).
- `fx_source_widen` (field of `fx_declared_callback_source`).
- `FxReachableRhs` (constructor of `fx_declared_query_reachable`).
- `FxReachableAsk` (constructor of `fx_declared_query_reachable`).
- `FxReachableSide` (constructor of `fx_declared_query_reachable`).
- `FxDeclaredCallbackBudget` (constructor of `fx_declared_callback_budget`).
- `fx_body_weight` (field of `fx_declared_callback_budget`).
- `fx_budget_encode_x` (field of `fx_declared_callback_budget`).
- `fx_budget_encode_c` (field of `fx_declared_callback_budget`).
- `fx_budget_target` (field of `fx_declared_callback_budget`).
- `fx_budget_priority` (field of `fx_declared_callback_budget`).
- `fx_budget_widening_point` (field of `fx_declared_callback_budget`).
- `fx_budget_rhs` (field of `fx_declared_callback_budget`).
- `fx_budget_continuation` (field of `fx_declared_callback_budget`).
- `fx_budget_leb` (field of `fx_declared_callback_budget`).
- `fx_budget_join` (field of `fx_declared_callback_budget`).
- `fx_budget_widen` (field of `fx_declared_callback_budget`).

Future proof module: `FixpointAuditWorklistCallbacksAdequacy`.

- `fx_declared_external_source_holds`:
  `FixpointAuditWorklistCallbacks.fx_declared_external_source_statement`; owner AUD-FX-WORKLIST.

<!-- AUD-API-FX-NAMES-END -->

<!-- AUD-API-RU-NAMES-BEGIN -->

# Rules audit names

## RulesAuditAtomFold

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_atom_full_event` (Inductive).
- `rules_atom_fold_counted` (Fixpoint).
- `rules_delta_index_counted` (Definition).
- `rules_atom_fold_erasure_statement` (Definition).
- `rules_atom_full_event_work` (Definition).
- `rules_atom_full_event_budget` (Definition).
- `rules_atom_full_work` (Definition).
- `rules_atom_full_budget` (Definition).
- `rules_atom_fold_selected_cost_statement` (Definition).
- `rules_atom_fold_input_budget` (Fixpoint).
- `rules_atom_fold_input_bound_statement` (Definition).
- `rules_delta_index_input_budget` (Definition).
- `rules_delta_index_input_bound_statement` (Definition).
- `rules_atom_fold_run` (Inductive).
- `rules_atom_fold_run_total_statement` (Definition).
- `rules_atom_fold_run_unique_statement` (Definition).
- `rules_atom_fold_run_erasure_statement` (Definition).
- `RafRelationGet` (constructor of `rules_atom_full_event`).
- `RafTupleAdd` (constructor of `rules_atom_full_event`).
- `RafRelationSet` (constructor of `rules_atom_full_event`).
- `RafElements` (constructor of `rules_atom_full_event`).
- `RafCase` (constructor of `rules_atom_full_event`).
- `RulesAtomFoldNil` (constructor of `rules_atom_fold_run`).
- `RulesAtomFoldCons` (constructor of `rules_atom_fold_run`).

Future proof module: `RulesAuditAtomFoldAdequacy`.

- `rules_atom_fold_erasure`: `RulesAuditAtomFold.rules_atom_fold_erasure_statement`; owner
  AUD-RU-DATA.
- `rules_atom_fold_selected_cost`: `RulesAuditAtomFold.rules_atom_fold_selected_cost_statement`;
  owner AUD-RU-DATA.
- `rules_atom_fold_input_bound`: `RulesAuditAtomFold.rules_atom_fold_input_bound_statement`; owner
  AUD-RU-DATA.
- `rules_delta_index_input_bound`: `RulesAuditAtomFold.rules_delta_index_input_bound_statement`;
  owner AUD-RU-DATA.
- `rules_atom_fold_run_total`: `RulesAuditAtomFold.rules_atom_fold_run_total_statement`; owner
  AUD-RU-DATA.
- `rules_atom_fold_run_unique`: `RulesAuditAtomFold.rules_atom_fold_run_unique_statement`; owner
  AUD-RU-DATA.
- `rules_atom_fold_run_erasure`: `RulesAuditAtomFold.rules_atom_fold_run_erasure_statement`; owner
  AUD-RU-DATA.

## RulesAuditCost

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_index_cost` (Definition).

Future proof module: `RulesAuditCostAdequacy`.

- `rules_index_cost_holds`: `RulesAuditCost.rules_index_cost`; owner AUD-RU-JOIN.

## RulesAuditDeltaRows

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_delta_rows_snapshot_counted` (Definition).
- `rules_delta_rows_lookup_counted` (Definition).
- `rules_delta_rows_erasure_statement` (Definition).
- `rules_delta_rows_snapshot_work` (Definition).
- `rules_delta_rows_snapshot_budget` (Definition).
- `rules_delta_rows_snapshot_cost_statement` (Definition).
- `rules_delta_rows_input_budget` (Definition).
- `rules_delta_rows_input_bound_statement` (Definition).

Future proof module: `RulesAuditDeltaRowsAdequacy`.

- `rules_delta_rows_erasure`: `RulesAuditDeltaRows.rules_delta_rows_erasure_statement`; owner
  AUD-RU-DATA.
- `rules_delta_rows_snapshot_cost`: `RulesAuditDeltaRows.rules_delta_rows_snapshot_cost_statement`;
  owner AUD-RU-DATA.
- `rules_delta_rows_input_bound`: `RulesAuditDeltaRows.rules_delta_rows_input_bound_statement`;
  owner AUD-RU-DATA.

## RulesAuditFiring

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_negative_filter_capture` (Fixpoint).
- `rules_head_rows_capture` (Fixpoint).
- `rules_universe_filter_capture` (Fixpoint).
- `rules_firing_tail_run` (Record).
- `rules_firing_tail_capture` (Definition).
- `rules_firing_tail_work` (Definition).
- `rules_firing_binding_size` (Definition).
- `rules_firing_atom_size` (Definition).
- `rules_firing_rule_size` (Definition).
- `rules_firing_tail_input_size` (Definition).
- `rules_firing_tail_input_budget` (Definition).
- `rules_firing_tail_input_bound_statement` (Definition).
- `RulesFiringTailRun` (constructor of `rules_firing_tail_run`).
- `rules_firing_tail_result` (field of `rules_firing_tail_run`).
- `rules_firing_tail_negative_events` (field of `rules_firing_tail_run`).
- `rules_firing_tail_head_events` (field of `rules_firing_tail_run`).
- `rules_firing_tail_universe_events` (field of `rules_firing_tail_run`).
- `rules_firing_tail_filter_events` (field of `rules_firing_tail_run`).
- `rules_firing_tail_output_events` (field of `rules_firing_tail_run`).

Future proof module: `RulesAuditFiringAdequacy`.

- `rules_firing_tail_input_bound`: `RulesAuditFiring.rules_firing_tail_input_bound_statement`; owner
  AUD-RU-JOIN.

## RulesAuditFiringCallbacks

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_arity_source_laws` (Definition).
- `rules_universe_event_source` (Definition).
- `rules_universe_trace_source` (Definition).
- `rules_negative_filter_source` (Definition).
- `rules_negative_input_budget` (Definition).
- `rules_universe_external_input_budget` (Definition).
- `rules_firing_tail_source_statement` (Definition).

Future proof module: `RulesAuditFiringCallbacksAdequacy`.

- `rules_firing_tail_source`: `RulesAuditFiringCallbacks.rules_firing_tail_source_statement`; owner
  AUD-RU-JOIN.

## RulesAuditIndex

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `mat_tuple_encoder` (Definition).
- `mat_bound_term` (Definition).
- `mat_tuple_key` (Fixpoint).
- `mat_index_add_full` (Definition).
- `mat_build_index_full` (Definition).
- `mat_variable_add_full` (Definition).
- `mat_build_variable_full` (Definition).
- `mat_index_full_erases_statement` (Definition).
- `mat_index_terms_input` (Definition).
- `mat_index_rows_input` (Definition).
- `mat_index_input_budget` (Definition).
- `mat_index_full_input_bound_statement` (Definition).
- `mat_variable_full_input_bound_statement` (Definition).
- `mat_index_full_source_statement` (Definition).

Future proof module: `RulesAuditIndexAdequacy`.

- `mat_index_full_erases`: `RulesAuditIndex.mat_index_full_erases_statement`; owner AUD-RU-INDEX.
- `mat_index_full_input_bound`: `RulesAuditIndex.mat_index_full_input_bound_statement`; owner
  AUD-RU-INDEX.
- `mat_variable_full_input_bound`: `RulesAuditIndex.mat_variable_full_input_bound_statement`; owner
  AUD-RU-INDEX.
- `mat_index_full_source`: `RulesAuditIndex.mat_index_full_source_statement`; owner AUD-RU-INDEX.

## RulesAuditIndexCounts

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `mat_block_count` (Definition).
- `mat_import_count` (Definition).
- `mat_index_success` (Definition).
- `mat_index_fold_run` (Inductive).
- `mat_index_row_counts_statement` (Definition).
- `mat_index_fold_counts_statement` (Definition).
- `mat_index_add_run` (Inductive).
- `mat_index_add_run_total_statement` (Definition).
- `MatIndexFoldNil` (constructor of `mat_index_fold_run`).
- `MatIndexFoldCons` (constructor of `mat_index_fold_run`).
- `MatIndexAddNoKey` (constructor of `mat_index_add_run`).
- `MatIndexAddKey` (constructor of `mat_index_add_run`).

Future proof module: `RulesAuditIndexCountsAdequacy`.

- `mat_index_row_counts`: `RulesAuditIndexCounts.mat_index_row_counts_statement`; owner
  AUD-RU-INDEX.
- `mat_index_fold_counts`: `RulesAuditIndexCounts.mat_index_fold_counts_statement`; owner
  AUD-RU-INDEX.
- `mat_index_add_run_total`: `RulesAuditIndexCounts.mat_index_add_run_total_statement`; owner
  AUD-RU-INDEX.

## RulesAuditJoin

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_selection_capture` (Inductive).
- `rules_select_capture` (Definition).
- `rules_selection_result` (Definition).
- `rules_selection_work` (Definition).
- `rules_selection_input_budget` (Definition).
- `rules_join_firing_run` (Record).
- `rules_join_firing_capture` (Definition).
- `rules_join_firing_work` (Definition).
- `rules_join_firing_input_budget` (Definition).
- `rules_join_firing_input_bound_statement` (Definition).
- `rules_flat_body_work` (Definition).
- `rules_selection_receipt_source` (Definition).
- `rules_tail_receipt_source` (Definition).
- `rules_selection_external_budget` (Definition).
- `rules_join_firing_source_statement` (Definition).
- `rules_join_agrees` (Definition).
- `RulesNestedCapture` (constructor of `rules_selection_capture`).
- `RulesMultiwayCapture` (constructor of `rules_selection_capture`).
- `RulesJoinFiringRun` (constructor of `rules_join_firing_run`).
- `rules_join_firing_selection` (field of `rules_join_firing_run`).
- `rules_join_firing_tail` (field of `rules_join_firing_run`).

Future proof module: `RulesAuditJoinAdequacy`.

- `rules_join_firing_input_bound`: `RulesAuditJoin.rules_join_firing_input_bound_statement`; owner
  AUD-RU-JOIN.
- `rules_join_firing_source`: `RulesAuditJoin.rules_join_firing_source_statement`; owner
  AUD-RU-JOIN.
- `rules_join_agrees_holds`: `RulesAuditJoin.rules_join_agrees`; owner AUD-RU-JOIN.

## RulesAuditJoinSyntax

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `mat_term_vars` (Definition).
- `mat_atom_vars` (Definition).
- `mat_bound_add` (Definition).
- `mat_positive_literal` (Definition).
- `mat_positive_atoms` (Definition).
- `mat_join_variables` (Definition).
- `mat_has_variable` (Definition).
- `mat_atoms_with` (Definition).
- `mat_join_syntax_erasure_statement` (Definition).

Future proof module: `RulesAuditJoinSyntaxAdequacy`.

- `mat_join_syntax_erasure`: `RulesAuditJoinSyntax.mat_join_syntax_erasure_statement`; owner
  AUD-RU-PREP.

## RulesAuditMaterializeAdapters

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `mat_ground_encoder` (Definition).
- `mat_ground_encoding_work` (Definition).
- `mat_ground_calls` (Definition).
- `mat_ground_set` (Definition).
- `mat_atom_calls` (Definition).
- `mat_atom_fold` (Definition).
- `mat_index` (Definition).
- `mat_instantiate` (Definition).
- `mat_tagged_encoder` (Definition).

## RulesAuditMaterializePrelude

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `mat_frame` (Inductive).
- `mat_frame_work` (Definition).
- `mat_work` (Definition).
- `mat_width` (Definition).
- `mat_run` (Definition).
- `mat_return` (Definition).
- `mat_bind` (Definition).
- `mat_mark` (Definition).
- `mat_lift` (Definition).
- `mat_emit` (Definition).
- `mat_map` (Fixpoint).
- `mat_append` (Fixpoint).
- `mat_flatmap` (Fixpoint).
- `mat_filter` (Fixpoint).
- `mat_foldr` (Fixpoint).
- `mat_foldl` (Fixpoint).
- `mat_all` (Fixpoint).
- `mat_encode` (Definition).
- `mat_level_context` (Inductive).
- `mat_native_levels` (Definition).
- `mat_arity` (Definition).
- `mat_nat` (Definition).
- `mat_nat_test` (Definition).
- `mat_tuple_size` (Definition).
- `mat_set_size` (Definition).
- `mat_db_size` (Definition).
- `mat_get` (Definition).
- `mat_level` (Definition).
- `mat_set` (Definition).
- `mat_rel` (Definition).
- `mat_elements` (Definition).
- `mat_of_list` (Definition).
- `mat_tuple_mem` (Definition).
- `mat_union` (Definition).
- `mat_nat_add` (Definition).
- `mat_get_encoded` (Definition).
- `mat_set_encoded` (Definition).
- `mat_predicate_set_encoded` (Definition).
- `MatBlock` (constructor of `mat_frame`).
- `MatNat` (constructor of `mat_frame`).
- `MatEncode` (constructor of `mat_frame`).
- `MatLevel` (constructor of `mat_frame`).
- `MatArity` (constructor of `mat_frame`).
- `MatOperand` (constructor of `mat_frame`).
- `MatChild` (constructor of `mat_frame`).
- `MatImported` (constructor of `mat_frame`).
- `MatExternalLevels` (constructor of `mat_level_context`).
- `MatCapturedLevels` (constructor of `mat_level_context`).

## RulesAuditMultiwayPrepare

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_variable_map_full` (Fixpoint).
- `rules_prepare_variable_full` (Definition).
- `rules_prepare_multiway_full` (Fixpoint).
- `rules_prepare_multiway_full_erases_statement` (Definition).

Future proof module: `RulesAuditMultiwayPrepareAdequacy`.

- `rules_prepare_multiway_full_erases`:
  `RulesAuditMultiwayPrepare.rules_prepare_multiway_full_erases_statement`; owner AUD-RU-MULTIWAY.

## RulesAuditMultiwayProbe

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_multi_probe_event` (Inductive).
- `rules_variable_probe_counted` (Definition).
- `rules_intersect_domains_counted` (Fixpoint).
- `rules_variable_candidates_counted` (Definition).
- `rules_multiway_values_counted` (Fixpoint).
- `rules_multiway_bindings_counted` (Fixpoint).
- `rules_run_multiway_counted` (Fixpoint).
- `rules_multiway_probe_erasure_statement` (Definition).
- `rules_multi_probe_event_work` (Definition).
- `rules_multi_probe_event_budget` (Definition).
- `rules_multi_probe_work` (Definition).
- `rules_multi_probe_budget` (Definition).
- `rules_run_multiway_selected_cost_statement` (Definition).
- `RmProbeKey` (constructor of `rules_multi_probe_event`).
- `RmTableGet` (constructor of `rules_multi_probe_event`).
- `RmIntersect` (constructor of `rules_multi_probe_event`).
- `RmElements` (constructor of `rules_multi_probe_event`).
- `RmBind` (constructor of `rules_multi_probe_event`).
- `RmAppend` (constructor of `rules_multi_probe_event`).
- `RmCase` (constructor of `rules_multi_probe_event`).

Future proof module: `RulesAuditMultiwayProbeAdequacy`.

- `rules_multiway_probe_erasure`: `RulesAuditMultiwayProbe.rules_multiway_probe_erasure_statement`;
  owner AUD-RU-MULTIWAY.
- `rules_run_multiway_selected_cost`:
  `RulesAuditMultiwayProbe.rules_run_multiway_selected_cost_statement`; owner AUD-RU-MULTIWAY.

## RulesAuditMultiwaySelection

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_multiway_selection_run` (Record).
- `rules_selected_multiway_capture` (Definition).
- `rules_multiway_selection_work` (Definition).
- `rules_multiway_selection_input_budget` (Definition).
- `rules_multiway_selection_count_statement` (Definition).
- `rules_multiway_selection_input_bound_statement` (Definition).
- `rules_multiway_selection_source_statement` (Definition).
- `RulesMultiwaySelectionRun` (constructor of `rules_multiway_selection_run`).
- `rules_multiway_selection_result` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_candidates` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_atoms` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_atom_events` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_relation_events` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_variable_events` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_prepare_events` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_probe_events` (field of `rules_multiway_selection_run`).
- `rules_multiway_selection_terminal_events` (field of `rules_multiway_selection_run`).

Future proof module: `RulesAuditMultiwaySelectionAdequacy`.

- `rules_multiway_selection_count`:
  `RulesAuditMultiwaySelection.rules_multiway_selection_count_statement`; owner AUD-RU-MULTIWAY.
- `rules_multiway_selection_input_bound`:
  `RulesAuditMultiwaySelection.rules_multiway_selection_input_bound_statement`; owner
  AUD-RU-MULTIWAY.
- `rules_multiway_selection_source`:
  `RulesAuditMultiwaySelection.rules_multiway_selection_source_statement`; owner AUD-RU-MULTIWAY.

## RulesAuditNestedPrepare

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_prepare_nested_full` (Fixpoint).
- `rules_prepare_nested_full_erases_statement` (Definition).
- `rules_nested_prepare_input_size` (Definition).
- `rules_nested_prepare_input_budget` (Definition).
- `rules_prepare_nested_full_input_bound_statement` (Definition).

Future proof module: `RulesAuditNestedPrepareAdequacy`.

- `rules_prepare_nested_full_erases`:
  `RulesAuditNestedPrepare.rules_prepare_nested_full_erases_statement`; owner AUD-RU-NESTED.
- `rules_prepare_nested_full_input_bound`:
  `RulesAuditNestedPrepare.rules_prepare_nested_full_input_bound_statement`; owner AUD-RU-NESTED.

## RulesAuditNestedProbe

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_nested_probe_event` (Inductive).
- `rules_probe_bound_term` (Definition).
- `rules_probe_filter` (Fixpoint).
- `rules_probe_value` (Definition).
- `rules_probe_instantiate` (Fixpoint).
- `rules_bound_key_counted` (Definition).
- `rules_bind_term_counted` (Definition).
- `rules_bind_terms_counted` (Fixpoint).
- `rules_probe_rows` (Fixpoint).
- `rules_probe_bindings` (Fixpoint).
- `rules_run_nested_counted` (Fixpoint).
- `rules_nested_probe_erasure_statement` (Definition).
- `rules_nested_probe_event_work` (Definition).
- `rules_nat_encoder_budget` (Definition).
- `rules_nested_probe_event_budget` (Definition).
- `rules_nested_probe_work` (Definition).
- `rules_nested_probe_budget` (Definition).
- `rules_run_nested_selected_cost_statement` (Definition).
- `RprobeBoundMem` (constructor of `rules_nested_probe_event`).
- `RprobeBindingGet` (constructor of `rules_nested_probe_event`).
- `RprobeBindingSet` (constructor of `rules_nested_probe_event`).
- `RprobeIndexGet` (constructor of `rules_nested_probe_event`).
- `RprobeEqual` (constructor of `rules_nested_probe_event`).
- `RprobeAppend` (constructor of `rules_nested_probe_event`).
- `RprobeCase` (constructor of `rules_nested_probe_event`).

Future proof module: `RulesAuditNestedProbeAdequacy`.

- `rules_nested_probe_erasure`: `RulesAuditNestedProbe.rules_nested_probe_erasure_statement`; owner
  AUD-RU-INDEX.
- `rules_run_nested_selected_cost`:
  `RulesAuditNestedProbe.rules_run_nested_selected_cost_statement`; owner AUD-RU-INDEX.

## RulesAuditNestedSelection

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_nested_selection_run` (Record).
- `rules_selected_nested_capture` (Definition).
- `rules_nested_selection_work` (Definition).
- `rules_nested_selection_input_size` (Definition).
- `rules_nested_selection_input_budget` (Definition).
- `rules_nested_selection_input_bound_statement` (Definition).
- `rules_nested_selection_source_statement` (Definition).
- `RulesNestedSelectionRun` (constructor of `rules_nested_selection_run`).
- `rules_nested_selection_result` (field of `rules_nested_selection_run`).
- `rules_nested_selection_atoms` (field of `rules_nested_selection_run`).
- `rules_nested_selection_atom_events` (field of `rules_nested_selection_run`).
- `rules_nested_selection_relation_events` (field of `rules_nested_selection_run`).
- `rules_nested_selection_prepare_events` (field of `rules_nested_selection_run`).
- `rules_nested_selection_probe_events` (field of `rules_nested_selection_run`).

Future proof module: `RulesAuditNestedSelectionAdequacy`.

- `rules_nested_selection_input_bound`:
  `RulesAuditNestedSelection.rules_nested_selection_input_bound_statement`; owner AUD-RU-NESTED.
- `rules_nested_selection_source`:
  `RulesAuditNestedSelection.rules_nested_selection_source_statement`; owner AUD-RU-NESTED.

## RulesAuditPrepareCallbacks

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_predicate_frame_source` (Definition).
- `rules_predicate_trace_source` (Definition).
- `rules_predicate_bodies_work` (Definition).
- `rules_predicate_input_budget` (Definition).
- `rules_predicate_source_laws` (Definition).
- `rules_nested_prepare_source_statement` (Definition).
- `rules_multiway_prepare_input_size` (Definition).
- `rules_multiway_prepare_input_budget` (Definition).
- `rules_multiway_prepare_source_statement` (Definition).

Future proof module: `RulesAuditPrepareCallbacksAdequacy`.

- `rules_nested_prepare_source`: `RulesAuditPrepareCallbacks.rules_nested_prepare_source_statement`;
  owner AUD-RU-PREP.
- `rules_multiway_prepare_source`:
  `RulesAuditPrepareCallbacks.rules_multiway_prepare_source_statement`; owner AUD-RU-PREP.

## RulesAuditRelationCallbacks

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_relation_entries` (Definition).
- `rules_relation_entry_source` (Definition).
- `rules_relation_event_source` (Definition).
- `rules_relation_trace_source` (Definition).
- `rules_environment_source_laws` (Definition).
- `rules_relation_external_input_budget` (Definition).
- `rules_relations_external_source_statement` (Definition).

Future proof module: `RulesAuditRelationCallbacksAdequacy`.

- `rules_relations_external_source`:
  `RulesAuditRelationCallbacks.rules_relations_external_source_statement`; owner AUD-RU-DATA.

## RulesAuditRelations

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_encode_entry` (Inductive).
- `rules_encoder` (Definition).
- `rules_relation_event` (Inductive).
- `rules_relation_predicates` (Fixpoint).
- `rules_relation_rows_counted` (Fixpoint).
- `rules_relation_fill_counted` (Fixpoint).
- `rules_join_relations_counted` (Definition).
- `rules_join_relations_erasure_statement` (Definition).
- `rules_join_relations_row_count_statement` (Definition).
- `rules_relation_set_event_work` (Definition).
- `rules_relation_event_work` (Definition).
- `rules_relation_event_budget` (Definition).
- `rules_relation_work` (Definition).
- `rules_relation_budget` (Definition).
- `rules_join_relations_selected_cost_statement` (Definition).
- `rules_relation_predicate_bits` (Fixpoint).
- `rules_relation_input_rows_budget` (Fixpoint).
- `rules_join_relations_input_budget` (Definition).
- `rules_join_relations_input_bound_statement` (Definition).
- `RulesEncodeEntry` (constructor of `rules_encode_entry`).
- `RulesRelationPredicate` (constructor of `rules_relation_event`).
- `RulesRelationDistinct` (constructor of `rules_relation_event`).
- `RulesRelationKeys` (constructor of `rules_relation_event`).
- `RulesRelationEnv` (constructor of `rules_relation_event`).
- `RulesRelationRows` (constructor of `rules_relation_event`).
- `RulesRelationSet` (constructor of `rules_relation_event`).
- `RulesRelationCase` (constructor of `rules_relation_event`).

Future proof module: `RulesAuditRelationsAdequacy`.

- `rules_join_relations_erasure`: `RulesAuditRelations.rules_join_relations_erasure_statement`;
  owner AUD-RU-DATA.
- `rules_join_relations_row_count`: `RulesAuditRelations.rules_join_relations_row_count_statement`;
  owner AUD-RU-DATA.
- `rules_join_relations_selected_cost`:
  `RulesAuditRelations.rules_join_relations_selected_cost_statement`; owner AUD-RU-DATA.
- `rules_join_relations_input_bound`:
  `RulesAuditRelations.rules_join_relations_input_bound_statement`; owner AUD-RU-DATA.

## RulesAuditTerminal

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_terminal_event` (Inductive).
- `rules_terminal_atom_counted` (Definition).
- `rules_positive_check_counted` (Fixpoint).
- `rules_negative_literals_counted` (Fixpoint).
- `rules_terminal_erasure_statement` (Definition).
- `rules_terminal_event_work` (Definition).
- `rules_terminal_event_budget` (Definition).
- `rules_terminal_work` (Definition).
- `rules_terminal_budget` (Definition).
- `rules_terminal_selected_cost_statement` (Definition).
- `RtInstantiate` (constructor of `rules_terminal_event`).
- `RtEnv` (constructor of `rules_terminal_event`).
- `RtMember` (constructor of `rules_terminal_event`).
- `RtNot` (constructor of `rules_terminal_event`).
- `RtAnd` (constructor of `rules_terminal_event`).
- `RtCase` (constructor of `rules_terminal_event`).

Future proof module: `RulesAuditTerminalAdequacy`.

- `rules_terminal_erasure`: `RulesAuditTerminal.rules_terminal_erasure_statement`; owner
  AUD-RU-JOIN.
- `rules_terminal_selected_cost`: `RulesAuditTerminal.rules_terminal_selected_cost_statement`; owner
  AUD-RU-JOIN.

## RulesAuditTerminalCallbacks

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_terminal_event_source` (Definition).
- `rules_terminal_trace_source` (Definition).
- `rules_positive_filter_capture` (Fixpoint).
- `rules_positive_filter_work` (Definition).
- `rules_positive_filter_source` (Definition).
- `rules_terminal_bodies_work` (Definition).
- `rules_positive_filter_erasure_statement` (Definition).

Future proof module: `RulesAuditTerminalCallbacksAdequacy`.

- `rules_positive_filter_erasure`:
  `RulesAuditTerminalCallbacks.rules_positive_filter_erasure_statement`; owner AUD-RU-JOIN.

## RulesAuditUniverse

Public package: `Galois.Rules`.

Card: AUD-RU-MODELS

- `rules_universe_event` (Inductive).
- `ru_literal_predicates` (Fixpoint).
- `ru_rule_predicates` (Fixpoint).
- `ru_fact_predicates` (Fixpoint).
- `ru_term_constants` (Fixpoint).
- `ru_literal_constants` (Fixpoint).
- `ru_rule_constants` (Fixpoint).
- `ru_fact_constants` (Fixpoint).
- `rules_universe_prepare_counted` (Definition).
- `ru_constants_check` (Fixpoint).
- `ru_nat_eqb` (Fixpoint).
- `rules_universe_check_counted` (Definition).
- `rules_universe_erasure_statement` (Definition).
- `rules_universe_event_work` (Definition).
- `rules_universe_event_budget` (Definition).
- `rules_universe_work` (Definition).
- `rules_universe_budget` (Definition).
- `rules_universe_selected_cost_statement` (Definition).
- `RuCase` (constructor of `rules_universe_event`).
- `RuAppend` (constructor of `rules_universe_event`).
- `RuPredicatesSet` (constructor of `rules_universe_event`).
- `RuConstantsSet` (constructor of `rules_universe_event`).
- `RuPredicateMem` (constructor of `rules_universe_event`).
- `RuConstantMem` (constructor of `rules_universe_event`).
- `RuArity` (constructor of `rules_universe_event`).
- `RuLength` (constructor of `rules_universe_event`).
- `RuNatEq` (constructor of `rules_universe_event`).
- `RuAnd` (constructor of `rules_universe_event`).

Future proof module: `RulesAuditUniverseAdequacy`.

- `rules_universe_erasure`: `RulesAuditUniverse.rules_universe_erasure_statement`; owner
  AUD-RU-DATA.
- `rules_universe_selected_cost`: `RulesAuditUniverse.rules_universe_selected_cost_statement`; owner
  AUD-RU-DATA.

<!-- AUD-API-RU-NAMES-END -->

<!-- AUD-API-OBS-NAMES-BEGIN -->

# Observation audit names

## FixpointAuditObserveCompare

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_seteq_budget` (Definition).
- `fx_observe_seteq_statement` (Definition).
- `fx_observe_nodup_statement` (Definition).
- `fx_observe_compare_source` (Definition).
- `fx_observe_compare_event` (Inductive).
- `fx_observe_compare_source_laws` (Definition).
- `fx_observe_compare_external_budget` (Definition).
- `fx_observe_seteq_source_statement` (Definition).
- `fx_observe_nodup_source_statement` (Definition).
- `fx_observe_key_compare` (Definition).
- `fx_observe_exists_key` (Fixpoint).
- `fx_observe_all_keys` (Fixpoint).
- `fx_observe_seteq` (Definition).
- `fx_observe_nodup` (Fixpoint).
- `fx_observe_compare_event_work` (Definition).
- `fx_observe_compare_work` (Definition).
- `fx_observe_exists_key_budget` (Fixpoint).
- `fx_observe_all_keys_budget` (Fixpoint).
- `fx_observe_nodup_budget` (Fixpoint).
- `FxObserveCompare` (constructor).
- `FxObserveCompareCase` (constructor).

Future proof module: `FixpointAuditObserveCompareAdequacy`.

- `fx_observe_seteq_correct`: `fx_observe_seteq_statement`; owner AUD-FX-OBS-PRIMS.
- `fx_observe_nodup_correct`: `fx_observe_nodup_statement`; owner AUD-FX-OBS-PRIMS.
- `fx_observe_seteq_source`: `fx_observe_seteq_source_statement`; owner AUD-FX-OBS-PRIMS.
- `fx_observe_nodup_source`: `fx_observe_nodup_source_statement`; owner AUD-FX-OBS-PRIMS.

## FixpointAuditObserveCompile

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_compile_targets` (Definition).
- `fx_observe_compile_event_work` (Definition).
- `fx_observe_compile_work` (Definition).
- `fx_compile_members_budget` (Fixpoint).
- `fx_compile_callback_max` (Definition).
- `fx_compile_code_budget` (Definition).
- `fx_compile_component_budget` (Definition).
- `fx_compile_components_budget` (Fixpoint).
- `fx_observe_compile_event` (Inductive).
- `fx_observe_compile_targets_budget` (Definition).
- `fx_compile_prepare_source` (Definition).
- `fx_compile_wto_source` (Definition).
- `fx_observe_compile_event_source` (Definition).
- `fx_observe_compile_external_budget` (Definition).
- `fx_observe_compile_targets_source_statement` (Definition).
- `fx_compile_restrict` (Fixpoint).
- `fx_compile_outputs` (Fixpoint).
- `fx_compile_component` (Definition).
- `fx_compile_components` (Fixpoint).
- `FxCompileDependency` (constructor).
- `FxCompileSet` (constructor).
- `FxCompileInduced` (constructor).
- `FxCompilePrepare` (constructor).
- `FxCompileWto` (constructor).
- `FxCompilePlan` (constructor).
- `FxCompileHeads` (constructor).
- `FxCompileTargets` (constructor).
- `FxCompileExpiry` (constructor).
- `FxCompileCase` (constructor).

Future proof module: `FixpointAuditObserveCompileAdequacy`.

- `fx_observe_compile_targets_source`: `fx_observe_compile_targets_source_statement`; owner
  AUD-FX-OBS-COMPILE.

## FixpointAuditObserveCompileWhole

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_compile_whole_event` (Inductive).
- `fx_observe_compile_whole` (Definition).
- `fx_observe_compile_whole_budget` (Definition).
- `fx_observe_compile_whole_event_work` (Definition).
- `fx_observe_compile_whole_event_source` (Definition).
- `fx_observe_compile_whole_external_budget` (Definition).
- `fx_observe_compile_whole_source_statement` (Definition).
- `FxWholeNumber` (constructor).
- `FxWholeCompile` (constructor).

Future proof module: `FixpointAuditObserveCompileWholeAdequacy`.

- `fx_observe_compile_whole_source`: `fx_observe_compile_whole_source_statement`; owner
  AUD-FX-OBS-COMPILE.

## FixpointAuditObserveComponents

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_components_budget` (Definition).
- `fx_observe_component_event_work` (Definition).
- `fx_observe_components_work` (Definition).
- `fx_observe_component_event_source` (Definition).
- `fx_observe_component_external_budget` (Definition).
- `fx_observe_component_event` (Inductive).
- `fx_observe_components_source_statement` (Definition).
- `fx_component_in_classes` (Fixpoint).
- `fx_components_in_classes` (Fixpoint).
- `fx_components_nonempty` (Fixpoint).
- `fx_observe_components` (Definition).
- `fx_component_in_classes_budget` (Fixpoint).
- `fx_components_in_classes_budget` (Fixpoint).
- `FxComponentOrder` (constructor).
- `FxComponentDependency` (constructor).
- `FxComponentIndex` (constructor).
- `FxComponentForward` (constructor).
- `FxComponentCompare` (constructor).
- `FxComponentList` (constructor).
- `FxComponentCase` (constructor).

Future proof module: `FixpointAuditObserveComponentsAdequacy`.

- `fx_observe_components_source`: `fx_observe_components_source_statement`; owner AUD-FX-OBS-CHECK.

## FixpointAuditObserveExecute

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_execute` (Definition).
- `fx_observe_execute_erasure_statement` (Definition).
- `fx_observe_event_work` (Definition).
- `fx_observe_work` (Definition).
- `fx_observe_record_input_budget` (Fixpoint).
- `fx_observe_evict_input_budget` (Fixpoint).
- `fx_observe_tick_input_budget` (Definition).
- `fx_observe_event` (Inductive).
- `fx_observe_repeat_input_budget` (Fixpoint).
- `fx_observe_execute_input_budget` (Definition).
- `fx_observe_execute_input_bound_statement` (Definition).
- `fx_observe_map_entries` (Definition).
- `fx_observe_event_source` (Definition).
- `fx_observe_event_external_budget` (Definition).
- `fx_observe_schedule_targets_within` (Definition).
- `fx_observe_execute_source_statement` (Definition).
- `fx_observe_record` (Fixpoint).
- `fx_observe_evict` (Fixpoint).
- `fx_observe_tick` (Definition).
- `fx_observe_repeat` (Fixpoint).
- `FxObserveNested` (constructor).
- `FxObserveQuery` (constructor).
- `FxObserveMap` (constructor).
- `FxObserveCase` (constructor).

Future proof module: `FixpointAuditObserveExecuteAdequacy`.

- `fx_observe_execute_erasure`: `fx_observe_execute_erasure_statement`; owner AUD-FX-OBS-EXEC.
- `fx_observe_execute_input_bound`: `fx_observe_execute_input_bound_statement`; owner
  AUD-FX-OBS-EXEC.
- `fx_observe_execute_source`: `fx_observe_execute_source_statement`; owner AUD-FX-OBS-EXEC.

## FixpointAuditObserveExpireCheck

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_expire_check_directed_budget` (Definition).
- `fx_expire_check_budget` (Definition).
- `fx_expire_check_event` (Inductive).
- `fx_expire_check_statement` (Definition).
- `fx_expire_check_event_source` (Definition).
- `fx_expire_check_external_budget` (Definition).
- `fx_expire_check_source_statement` (Definition).
- `fx_expire_check_value` (Definition).
- `fx_expire_check_ne` (Fixpoint).
- `fx_expire_check_directed` (Definition).
- `fx_expire_check` (Definition).
- `fx_expire_check_work` (Definition).
- `fx_expire_check_ne_budget` (Fixpoint).
- `FxExpireCheckCase` (constructor).
- `FxExpireCheckCompare` (constructor).

Future proof module: `FixpointAuditObserveExpireCheckAdequacy`.

- `fx_expire_check_correct`: `fx_expire_check_statement`; owner AUD-FX-OBS-PRIMS.
- `fx_expire_check_source`: `fx_expire_check_source_statement`; owner AUD-FX-OBS-PRIMS.

## FixpointAuditObserveExpiry

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_expiry_event_work` (Definition).
- `fx_observe_expiry_work` (Definition).
- `fx_observe_expiry_set_budget` (Fixpoint).
- `fx_observe_reader_uses_budget` (Fixpoint).
- `fx_observe_component_uses_budget` (Definition).
- `fx_observe_last_reader_budget` (Fixpoint).
- `fx_observe_expiry_fold_budget` (Fixpoint).
- `fx_observe_expiry_event` (Inductive).
- `fx_observe_expiry_fold_bound_statement` (Definition).
- `fx_observe_expiry_event_source` (Definition).
- `fx_observe_expiry_source_laws` (Definition).
- `fx_observe_expiry_external_budget` (Definition).
- `fx_observe_expiry_fold_source_statement` (Definition).
- `fx_observe_reader_uses` (Fixpoint).
- `fx_observe_component_uses` (Definition).
- `fx_observe_last_reader` (Fixpoint).
- `fx_observe_expiry_fold` (Fixpoint).
- `fx_observe_expiry_fold_statement` (Definition).
- `FxExpirySet` (constructor).
- `FxExpiryReaders` (constructor).
- `FxExpiryMap` (constructor).
- `FxExpiryTarget` (constructor).
- `FxExpiryCase` (constructor).

Future proof module: `FixpointAuditObserveExpiryAdequacy`.

- `fx_observe_expiry_fold_bound`: `fx_observe_expiry_fold_bound_statement`; owner AUD-FX-OBS-CHECK.
- `fx_observe_expiry_fold_source`: `fx_observe_expiry_fold_source_statement`; owner
  AUD-FX-OBS-CHECK.
- `fx_observe_expiry_fold_correct`: `fx_observe_expiry_fold_statement`; owner AUD-FX-OBS-CHECK.

## FixpointAuditObserveForward

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_forward_constraints_budget` (Fixpoint).
- `fx_observe_forward_event` (Inductive).
- `fx_forward_boundary_budget` (Definition).
- `fx_observe_forward_budget` (Fixpoint).
- `fx_observe_forward_run` (Definition).
- `fx_observe_forward_event_source` (Definition).
- `fx_observe_forward_source_statement` (Definition).
- `fx_forward_deps` (Fixpoint).
- `fx_forward_constraints` (Fixpoint).
- `fx_forward_boundary` (Definition).
- `fx_observe_forward` (Fixpoint).
- `fx_observe_forward_event_work` (Definition).
- `fx_observe_forward_work` (Definition).
- `fx_forward_deps_budget` (Fixpoint).
- `FxForwardIndex` (constructor).
- `FxForwardSet` (constructor).
- `FxForwardConcat` (constructor).
- `FxForwardBuild` (constructor).
- `FxForwardCase` (constructor).

Future proof module: `FixpointAuditObserveForwardAdequacy`.

- `fx_observe_forward_source`: `fx_observe_forward_source_statement`; owner AUD-FX-OBS-PRIMS.

## FixpointAuditObserveInduced

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_induced_event_source` (Definition).
- `fx_induced_out_source_statement` (Definition).
- `fx_induced_event` (Inductive).
- `fx_induced_filter_vertices` (Fixpoint).
- `fx_induced_filter_edges` (Fixpoint).
- `fx_induced_out` (Definition).
- `fx_induced_encoder` (Definition).
- `fx_induced_prepare_cb` (Definition).
- `fx_induced_dfs_cb` (Definition).
- `fx_induced_event_work` (Definition).
- `fx_induced_work` (Definition).
- `fx_induced_vertices_budget` (Fixpoint).
- `fx_induced_out_budget` (Definition).
- `FxInducedDependency` (constructor).
- `FxInducedSet` (constructor).
- `FxInducedEncode` (constructor).
- `FxInducedCase` (constructor).

Future proof module: `FixpointAuditObserveInducedAdequacy`.

- `fx_induced_out_source`: `fx_induced_out_source_statement`; owner AUD-FX-OBS-COMPILE.

## FixpointAuditObserveNumber

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_number` (Fixpoint).
- `fx_observe_label` (Definition).
- `fx_observe_number_budget` (Fixpoint).
- `fx_observe_label_budget` (Definition).
- `fx_observe_number_source_statement` (Definition).
- `fx_observe_label_source_statement` (Definition).

Future proof module: `FixpointAuditObserveNumberAdequacy`.

- `fx_observe_number_source`: `fx_observe_number_source_statement`; owner AUD-FX-OBS-EXEC.
- `fx_observe_label_source`: `fx_observe_label_source_statement`; owner AUD-FX-OBS-EXEC.

## FixpointAuditObserveNumberCallbacks

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_numbered_target` (Definition).
- `fx_observe_numbered_rhs` (Definition).
- `fx_observe_numbered_source_laws` (Definition).
- `fx_observe_numbered_target_source_statement` (Definition).
- `fx_observe_numbered_rhs_source_statement` (Definition).

Future proof module: `FixpointAuditObserveNumberCallbacksAdequacy`.

- `fx_observe_numbered_target_source`: `fx_observe_numbered_target_source_statement`; owner
  AUD-FX-OBS-EXEC.
- `fx_observe_numbered_rhs_source`: `fx_observe_numbered_rhs_source_statement`; owner
  AUD-FX-OBS-EXEC.

## FixpointAuditObserveNumberExecute

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_number_execute_work` (Definition).
- `fx_number_execute_tick_budget` (Definition).
- `fx_number_execute_repeat_budget` (Fixpoint).
- `fx_number_execute_budget` (Definition).
- `fx_number_execute_event` (Inductive).
- `fx_number_execute_event_source` (Definition).
- `fx_number_execute_external_budget` (Definition).
- `fx_number_execute_source_statement` (Definition).
- `fx_number_execute_tick` (Definition).
- `fx_number_execute_repeat` (Fixpoint).
- `fx_number_execute` (Definition).
- `fx_number_execute_event_work` (Definition).
- `FxNumberExecuteMachine` (constructor).
- `FxNumberExecuteBoundary` (constructor).
- `FxNumberExecuteCase` (constructor).

Future proof module: `FixpointAuditObserveNumberExecuteAdequacy`.

- `fx_number_execute_source`: `fx_number_execute_source_statement`; owner AUD-FX-OBS-EXEC.

## FixpointAuditObserveNumberMachine

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_number_machine_external_budget` (Definition).
- `fx_number_machine_step_source_statement` (Definition).
- `fx_number_machine_event` (Inductive).
- `fx_number_system` (Definition).
- `fx_number_machine_step` (Definition).
- `fx_number_machine_event_work` (Definition).
- `fx_number_machine_work` (Definition).
- `fx_number_machine_step_budget` (Definition).
- `fx_number_passthrough_source` (Definition).
- `fx_number_passthrough_budget` (Definition).
- `fx_number_machine_event_source` (Definition).
- `FxNumberMachineNested` (constructor).
- `FxNumberMachineRhs` (constructor).
- `FxNumberMachineTarget` (constructor).

Future proof module: `FixpointAuditObserveNumberMachineAdequacy`.

- `fx_number_machine_step_source`: `fx_number_machine_step_source_statement`; owner AUD-FX-OBS-EXEC.

## FixpointAuditObserveNumberTargets

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_number_target_external_budget` (Definition).
- `fx_observe_numbered_targets_source_statement` (Definition).
- `fx_observe_numbered_system_targets` (Definition).
- `fx_observe_numbered_system_targets_source_statement` (Definition).
- `fx_observe_number_target_event` (Inductive).
- `fx_number_targets_fold` (Fixpoint).
- `fx_observe_numbered_targets` (Definition).
- `fx_number_target_event_work` (Definition).
- `fx_number_targets_work` (Definition).
- `fx_number_targets_fold_budget` (Fixpoint).
- `fx_observe_numbered_targets_budget` (Definition).
- `fx_number_target_event_source` (Definition).
- `FxNumberTable` (constructor).
- `FxNumberTarget` (constructor).
- `FxNumberIndex` (constructor).
- `FxNumberSeq` (constructor).
- `FxNumberCase` (constructor).

Future proof module: `FixpointAuditObserveNumberTargetsAdequacy`.

- `fx_observe_numbered_targets_source`: `fx_observe_numbered_targets_source_statement`; owner
  AUD-FX-OBS-COMPILE.
- `fx_observe_numbered_system_targets_source`:
  `fx_observe_numbered_system_targets_source_statement`; owner AUD-FX-OBS-COMPILE.

## FixpointAuditObserveOrder

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_order_event` (Inductive).
- `fx_observe_order` (Definition).
- `fx_observe_order_event_work` (Definition).
- `fx_observe_order_work` (Definition).
- `fx_observe_order_budget` (Definition).
- `fx_observe_order_statement` (Definition).
- `fx_observe_order_capture_source` (Definition).
- `fx_observe_order_event_source` (Definition).
- `fx_observe_order_source_statement` (Definition).
- `FxObserveOrderGraph` (constructor).
- `FxObserveOrderPrepare` (constructor).
- `FxObserveOrderScc` (constructor).
- `FxObserveOrderReverse` (constructor).

Future proof module: `FixpointAuditObserveOrderAdequacy`.

- `fx_observe_order_correct`: `fx_observe_order_statement`; owner AUD-FX-OBS-CHECK.
- `fx_observe_order_source`: `fx_observe_order_source_statement`; owner AUD-FX-OBS-CHECK.

## FixpointAuditObservePlanCheck

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_plan_check_source_statement` (Definition).
- `fx_observe_check_event` (Inductive).
- `fx_observe_plan_check` (Definition).
- `fx_observe_plan_check_budget` (Definition).
- `fx_observe_check_event_work` (Definition).
- `fx_observe_check_work` (Definition).
- `fx_observe_check_event_source` (Definition).
- `fx_observe_check_external_budget` (Definition).
- `FxCheckPrepare` (constructor).
- `FxCheckComponents` (constructor).
- `FxCheckExpiry` (constructor).
- `FxCheckCompare` (constructor).
- `FxCheckCase` (constructor).

Future proof module: `FixpointAuditObservePlanCheckAdequacy`.

- `fx_observe_plan_check_source`: `fx_observe_plan_check_source_statement`; owner AUD-FX-OBS-CHECK.

## FixpointAuditObservePrepare

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_prepare_event_work` (Definition).
- `fx_observe_prepare_work` (Definition).
- `fx_observe_prepare_event_source` (Definition).
- `fx_observe_prepare_event` (Inductive).
- `fx_observe_prepare_external_budget` (Definition).
- `fx_observe_prepare_source_statement` (Definition).
- `fx_observe_side_free` (Fixpoint).
- `fx_observe_roots_mem` (Fixpoint).
- `fx_observe_roots_check` (Definition).
- `fx_observe_prepare` (Definition).
- `fx_observe_roots_mem_budget` (Fixpoint).
- `fx_observe_prepare_budget` (Definition).
- `FxPrepareDependency` (constructor).
- `FxPrepareIndex` (constructor).
- `FxPrepareSet` (constructor).
- `FxPrepareOrder` (constructor).
- `FxPrepareExpiry` (constructor).
- `FxPrepareCase` (constructor).

Future proof module: `FixpointAuditObservePrepareAdequacy`.

- `fx_observe_prepare_source`: `fx_observe_prepare_source_statement`; owner AUD-FX-OBS-CHECK.

## FixpointAuditObserveWhole

Public package: `Galois.Fixpoint`.

Card: AUD-FX-MODELS

- `fx_observe_whole_core_budget` (Definition).
- `fx_observe_reference_budget` (Definition).
- `fx_observe_whole_event_source` (Definition).
- `fx_observe_whole_external_budget` (Definition).
- `fx_observe_whole_event` (Inductive).
- `fx_observe_full_reference_source_statement` (Definition).
- `fx_observe_run_source_statement` (Definition).
- `fx_observe_reference_source_statement` (Definition).
- `fx_observe_whole_core` (Definition).
- `fx_observe_full_reference` (Definition).
- `fx_observe_run` (Definition).
- `fx_observe_reference` (Definition).
- `fx_observe_whole_event_work` (Definition).
- `fx_observe_whole_work` (Definition).
- `FxObserveWholeCheck` (constructor).
- `FxObserveWholeNumber` (constructor).
- `FxObserveWholeCompile` (constructor).
- `FxObserveWholeExecute` (constructor).
- `FxObserveWholeProject` (constructor).
- `FxObserveWholeCase` (constructor).

Future proof module: `FixpointAuditObserveWholeAdequacy`.

- `fx_observe_full_reference_source`: `fx_observe_full_reference_source_statement`; owner
  AUD-FX-OBS-WHOLE.
- `fx_observe_run_source`: `fx_observe_run_source_statement`; owner AUD-FX-OBS-WHOLE.
- `fx_observe_reference_source`: `fx_observe_reference_source_statement`; owner AUD-FX-OBS-WHOLE.

<!-- AUD-API-OBS-NAMES-END -->

## FixpointAuditCost

Public package: `Galois.Fixpoint`.

Card: AUD-FX-COST

- `solver_preparation_cost_statement` (Definition).
- `solver_dependency_cost_statement` (Definition).
- `solver_full_source_family_statement` (Definition).

Future proof module: `FixpointAuditCost`.

- `solver_preparation_cost`: `solver_preparation_cost_statement`; owner AUD-FX-COST.
- `solver_dependency_cost`: `solver_dependency_cost_statement`; owner AUD-FX-COST.
- `solver_full_source_family`: `solver_full_source_family_statement`; owner AUD-FX-COST.

## AnalysesAuditCostBridge

Public package: `Galois.Analyses`.

Card: AUD-COST-BRIDGE

- `numeric_bodies_work` (Definition).
- `numeric_invariant_source_laws` (Definition).
- `numeric_trip_event_receipt` (Definition).
- `numeric_trip_callback_allowance` (Definition).
- `numeric_trip_full_source_statement` (Definition).
- `numeric_reduce_call_value` (Definition).
- `numeric_reduce_source_laws` (Definition).
- `numeric_reduce_event_receipt` (Definition).
- `numeric_reduce_full_source_statement` (Definition).
- `numeric_sr_call_value` (Definition).
- `numeric_sr_source_laws` (Definition).
- `numeric_sr_call_receipt` (Definition).
- `numeric_recognizer_full_source_statement` (Definition).
- `audit_core_nonrewrite_source_components_statement` (Definition).
- `numeric_core_canonical_source_family_statement` (Definition).
- `audit_core_nonrewrite_full_components_statement` (Definition).
- `audit_rewrite_full_source_family_statement` (Definition).
- `audit_core_full_source_bridge_statement` (Definition).
- `audit_core_full_source_bridge`: `audit_core_full_source_bridge_statement`; owner AUD-COST-BRIDGE.

## AnalysesAuditCostBridgeExamples

Test package: `Galois.Tests.Analyses`.

Card: AUD-COST-BRIDGE

Test destination: `tests/Analyses/AnalysesAuditCostBridgeExamples.v`.

- `audit_core_full_source_bridge_nonempty` (future Example); owner AUD-COST-BRIDGE.
- `audit_core_trip_source_fixture` and `bridge_invariant_source_adequate` (closed Examples);
  owner AUD-COST-BRIDGE.
- Test definitions: `bridge_trip_chain`, `bridge_invariant`, `bridge_invariant_counted`,
  `bridge_invariant_source` and `audit_core_full_source_bridge_nonempty_statement`.

## FloatAuditCostBridge

Public package: `Galois.Float`.

Card: AUD-COST-BRIDGE

- `bridge_audit_float_min_subnormal_correct_type` (Definition).
- `bridge_audit_float_split_candidate_sound_type` (Definition).
- `bridge_float_bin_select_legacy_type` (Definition).
- `bridge_float_bin_select_sound_type` (Definition).
- `bridge_float_bin_select_split_type` (Definition).
- `bridge_float_body_core_erases_type` (Definition).
- `bridge_float_body_round_erases_type` (Definition).
- `bridge_float_body_shift_bound_type` (Definition).
- `bridge_float_body_shift_count_type` (Definition).
- `bridge_float_div_split_precision_type` (Definition).
- `bridge_float_div_split_sound_type` (Definition).
- `bridge_float_div_split_source_bound_type` (Definition).
- `bridge_float_div_split_source_divides_type` (Definition).
- `bridge_float_div_split_source_erases_type` (Definition).
- `bridge_float_div_split_source_total_type` (Definition).
- `bridge_float_div_split_source_unique_type` (Definition).
- `bridge_float_pinned_division_body_correspondence_type` (Definition).
- `bridge_float_primitive_body_positive_type` (Definition).
- `bridge_float_zero_sign_sound_type` (Definition).
- `bridge_select_sound_type` (Definition).
- `bridge_split_sound_type` (Definition).
- `bridge_zero_sign_sound_type` (Definition).
- `numeric_float_source_family_statement` (Definition).
- `audit_float_div_round_input_size` (Definition).
- `audit_float_div_round_input_budget` (Definition).
- `audit_float_div_round_captured` (Definition).
- `audit_float_div_round_constructive_statement` (Definition).
- `audit_float_div_round_constructive` (future Theorem); owner AUD-COST-BRIDGE.
- `audit_float_full_source_bridge_statement` (Definition).
- `audit_float_full_source_bridge`: `audit_float_full_source_bridge_statement`; owner
  AUD-COST-BRIDGE.

## FloatAuditCostBridgeExamples

Test package: `Galois.Tests.Float`.

Card: AUD-COST-BRIDGE

Test destination: `tests/Float/FloatAuditCostBridgeExamples.v`.

- `audit_float_full_source_bridge_nonempty` (future Example); owner AUD-COST-BRIDGE.
- `audit_float_full_source_bridge_nonempty_statement` (Definition); owner AUD-COST-BRIDGE.
- `audit_float_div_round_finite_fixture` (closed Example); owner AUD-COST-BRIDGE.

## GraphDfs

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `dfs` and `rpo` (same-value source refinements).

## GraphScc

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `tarjan_result` (same-value source refinement).

## GraphWto

Public package: `Galois.Graph`.

Card: AUD-GR-MODELS

- `wto_unfold` (same-value source refinement).
<!-- AUD-API-RW-NAMES-BEGIN -->

# Rewrite audit names

## AnalysesAuditRewriteFacadeCheckedMaterialize

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_references_valid` (Fixpoint).
- `rw_facade_provenance_entries_valid` (Fixpoint).
- `rw_facade_materialize_shape_atomic` (Definition).
- `rw_facade_checked_materialize_run` (Inductive).
- `RPFCheckedMaterializeReject` (Constructor).
- `RPFCheckedMaterializeAccept` (Constructor).
- `rw_facade_checked_materialize_total_statement` (Definition).
- `rw_facade_checked_materialize_unique_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeCheckedMaterializeAdequacy`.

- `rw_facade_checked_materialize_total`:
  `AnalysesAuditRewriteFacadeCheckedMaterialize.rw_facade_checked_materialize_total_statement`;
  owner AUD-RP-FACADE.
- `rw_facade_checked_materialize_unique`:
  `AnalysesAuditRewriteFacadeCheckedMaterialize.rw_facade_checked_materialize_unique_statement`;
  owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeCheckerContracts

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_option_dimension` (Definition).
- `rw_facade_path_dimension` (Definition).
- `rw_facade_table_operand_dimension` (Definition).
- `rw_facade_guard_operand_dimension` (Definition).
- `rw_facade_gate_operand_dimension` (Definition).
- `rw_facade_subst_operand_dimension` (Definition).
- `rw_facade_code_operand_dimension` (Definition).
- `rw_facade_eq_operand_dimension` (Definition).
- `rw_facade_step_operand_dimension` (Definition).
- `rw_facade_replay_operand_dimension` (Definition).
- `rw_facade_checker_operand_dimension` (Definition).
- `rw_facade_steps_ops` (Definition).
- `rw_facade_checker_whole_bound_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeCheckerContractsAdequacy`.

- `rw_facade_checker_whole_bound`:
  `AnalysesAuditRewriteFacadeCheckerContracts.rw_facade_checker_whole_bound_statement`; owner
  AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeDimensions

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_term_dimension` (Fixpoint).
- `rw_facade_rule_dimension` (Definition).
- `rw_facade_core_dimension` (Fixpoint).
- `rw_facade_node_dimension` (Definition).
- `rw_facade_graph_dimension` (Definition).
- `rw_facade_index_dimension` (Definition).
- `rw_facade_reason_dimension` (Definition).
- `rw_facade_proof_dimension` (Definition).
- `rw_facade_witness_dimension` (Definition).
- `rw_facade_tracked_dimension` (Definition).
- `rw_facade_prepared_dimension` (Definition).
- `rw_facade_attempt_dimension` (Definition).
- `rw_facade_offers_dimension` (Definition).
- `rw_facade_N_dimension` (Definition).
- `rw_facade_dp_dimension` (Definition).
- `rw_facade_strategy_dimension` (Definition).
- `rw_facade_runner_dimension` (Definition).
- `rw_facade_once_dimension` (Definition).
- `rw_facade_step_dimension` (Definition).
- `rw_facade_leaves_dimension` (Definition).

## AnalysesAuditRewriteFacadeInterfaceFacadeOptimizerRealizesStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_optimizer_realizes_statement` (Definition).

## AnalysesAuditRewriteFacadeInterfaceFacadeSelectedRealizesStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_selected_realizes_statement` (Definition).

## AnalysesAuditRewriteFacadeInterfaceFacadeTrackedRealizesStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_tracked_realizes_statement` (Definition).

## AnalysesAuditRewriteFacadeInterfaceLegacyRunLinkStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_legacy_run_link_statement` (Definition).

## AnalysesAuditRewriteFacadeInterfaceSelectedExplanationAcceptsStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_selected_explanation_accepts_statement` (Definition).

## AnalysesAuditRewriteFacadeInterfaceTrackedOptimiseSelectedStatement

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_tracked_optimise_selected_statement` (Definition).

## AnalysesAuditRewriteFacadeMaterialize

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_materialize_project_atomic` (Fixpoint).
- `rw_facade_binding_max` (Fixpoint).
- `rw_facade_binding_range` (Fixpoint).
- `rw_facade_bindings_atomic` (Definition).
- `rw_facade_invert_onto` (Fixpoint).
- `rw_facade_prefix_atomic` (Fixpoint).
- `rw_facade_materialize_run` (Inductive).
- `RPFMaterializeRefl` (Constructor).
- `RPFMaterializeRule` (Constructor).
- `RPFMaterializeSym` (Constructor).
- `RPFMaterializeTrans` (Constructor).
- `RPFMaterializeCongruence` (Constructor).
- `RPFMaterializeChildrenNil` (Constructor).
- `RPFMaterializeChildrenCons` (Constructor).
- `rw_facade_materialize_total_statement` (Definition).
- `rw_facade_materialize_children_run` (Inductive).
- `rw_facade_bindings_erases_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeMaterializeAdequacy`.

- `rw_facade_materialize_total`:
  `AnalysesAuditRewriteFacadeMaterialize.rw_facade_materialize_total_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_bindings_erases` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeOffers

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_make_bindings_atomic` (Fixpoint).
- `rw_facade_rule_offers_atomic` (Definition).
- `rw_facade_offer_gate_atomic` (Definition).
- `rw_facade_choose_atomic` (Fixpoint).
- `rw_facade_strategy_run` (Inductive).
- `RPFStrategyEmpty` (Constructor).
- `RPFStrategyReady` (Constructor).

## AnalysesAuditRewriteFacadeOptimizer

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_legacy_dimension` (Definition).
- `rw_facade_dag_dimension` (Definition).
- `rw_facade_steps_dimension` (Definition).
- `rw_facade_explain_core_run` (Inductive).
- `RPFExplainMissing` (Constructor).
- `RPFExplainMalformed` (Constructor).
- `RPFExplainChecked` (Constructor).
- `rw_facade_selected_run` (Inductive).
- `RPFSelectedRun` (Constructor).
- `rw_facade_extract_run` (Inductive).
- `RPFExtractMissing` (Constructor).
- `RPFExtractMalformed` (Constructor).
- `RPFExtractFound` (Constructor).
- `rw_facade_optimizer_run` (Inductive).
- `RPFOptimizerNoTree` (Constructor).
- `RPFOptimizerSelected` (Constructor).

## AnalysesAuditRewriteFacadePlainContracts

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_tracked_realizes_fixed_type` (Definition).
- `rw_legacy_run_link_fixed_type` (Definition).
- `rw_facade_selected_realizes_fixed_type` (Definition).
- `rw_selected_explanation_accepts_fixed_type` (Definition).
- `rw_facade_optimizer_realizes_fixed_type` (Definition).
- `rw_tracked_optimise_selected_fixed_type` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeInterfaceFacadeOptimizerRealizesStatementAdequacy`.

- `rw_facade_optimizer_realizes` (future Theorem); owner AUD-RP-FACADE.

Future proof module: `AnalysesAuditRewriteFacadeInterfaceFacadeSelectedRealizesStatementAdequacy`.

- `rw_facade_selected_realizes` (future Theorem); owner AUD-RP-FACADE.

Future proof module: `AnalysesAuditRewriteFacadeInterfaceFacadeTrackedRealizesStatementAdequacy`.

- `rw_facade_tracked_realizes` (future Theorem); owner AUD-RP-FACADE.

Future proof module: `AnalysesAuditRewriteFacadeInterfaceLegacyRunLinkStatementAdequacy`.

- `rw_legacy_run_link` (future Theorem); owner AUD-RP-FACADE.

Future proof module:
  `AnalysesAuditRewriteFacadeInterfaceSelectedExplanationAcceptsStatementAdequacy`.

- `rw_selected_explanation_accepts` (future Theorem); owner AUD-RP-FACADE.

Future proof module: `AnalysesAuditRewriteFacadeInterfaceTrackedOptimiseSelectedStatementAdequacy`.

- `rw_tracked_optimise_selected` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadePlainExplain

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_plain_facade_explain_core` (Definition).
- `rw_legacy_selected_explanation_builder` (Definition).
- `rw_plain_facade_extract` (Definition).
- `rw_tracked_optimise_builder` (Definition).

## AnalysesAuditRewriteFacadePlainHelpers

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_plain_audit_finset_mem` (Definition).
- `rw_plain_audit_finset_add` (Definition).
- `rw_plain_audit_trie_elements` (Definition).
- `rw_plain_rw_facade_vars` (Definition).
- `rw_plain_rw_queue_append_atomic` (Definition).
- `rw_plain_rw_facade_unit_adapter` (Definition).
- `rw_plain_rw_facade_nat_adapter` (Definition).
- `rw_plain_rw_facade_pattern_atomic` (Fixpoint).
- `rw_plain_rw_facade_holes_atomic` (Fixpoint).
- `rw_plain_rw_facade_prepare_rule_atomic` (Definition).
- `rw_plain_rw_facade_prepare_atomic` (Fixpoint).
- `rw_plain_rw_facade_materialize_project_atomic` (Fixpoint).
- `rw_plain_rw_facade_binding_max` (Fixpoint).
- `rw_plain_rw_facade_binding_range` (Fixpoint).
- `rw_plain_rw_facade_bindings_atomic` (Definition).
- `rw_plain_rw_facade_invert_onto` (Fixpoint).
- `rw_plain_rw_facade_prefix_atomic` (Fixpoint).
- `rw_plain_rw_facade_capture_entries` (Fixpoint).
- `rw_plain_rw_facade_capture_atomic` (Definition).
- `rw_plain_rw_facade_references_valid` (Fixpoint).
- `rw_plain_rw_facade_provenance_entries_valid` (Fixpoint).
- `rw_plain_rw_facade_materialize_shape_atomic` (Definition).
- `rw_plain_rw_facade_local_callbacks` (Definition).
- `rw_plain_rw_facade_apply_atomic` (Definition).

## AnalysesAuditRewriteFacadePlainMaterializer

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_plain_materialize_call` (Inductive).
- `RWFacadePlainRoot` (Constructor).
- `RWFacadePlainChildren` (Constructor).
- `rw_facade_plain_materialize_descend` (Inductive).
- `RWFacadeDescendSym` (Constructor).
- `RWFacadeDescendFirst` (Constructor).
- `RWFacadeDescendSecond` (Constructor).
- `RWFacadeDescendCongruence` (Constructor).
- `RWFacadeDescendChild` (Constructor).
- `RWFacadeDescendTail` (Constructor).
- `rw_facade_plain_materialize_well_founded_type` (Definition).
- `rw_facade_plain_materialize_body` (Definition).
- `rw_facade_plain_materialize_execute` (Definition).
- `rw_facade_checked_materialize_builder` (Definition).
- `rw_facade_plain_materialize_source_erases_type` (Definition).
- `rw_facade_plain_materialize_realizes_type` (Definition).
- `rw_facade_plain_materialize_shape_erases_type` (Definition).
- `rw_facade_plain_materialize_source_bound_type` (Definition).

Future proof module: `AnalysesAuditRewriteFacadePlainMaterializerAdequacy`.

- `rw_facade_plain_materialize_well_founded`:
  `AnalysesAuditRewriteFacadePlainMaterializer.rw_facade_plain_materialize_well_founded_type`; owner
  AUD-RP-FACADE.
- `rw_facade_plain_materialize_source_erases` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_plain_materialize_realizes` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_plain_materialize_shape_erases`:
  `AnalysesAuditRewriteFacadePlainMaterializer.rw_facade_plain_materialize_shape_erases_type`; owner
  AUD-RP-FACADE.
- `rw_facade_plain_materialize_source_bound` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadePlainRun

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_plain_facade_make_bindings` (Fixpoint).
- `rw_plain_facade_rule_offers` (Definition).
- `rw_plain_facade_offer_gate` (Definition).
- `rw_plain_facade_choose` (Fixpoint).
- `rw_plain_facade_strategy` (Definition).
- `rw_plain_facade_once` (Definition).
- `rw_plain_facade_repeat` (Fixpoint).
- `rw_legacy_tracked_builder` (Definition).

## AnalysesAuditRewriteFacadePrepare

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_nat_adapter` (Definition).
- `rw_facade_unit_adapter` (Definition).
- `rw_facade_pattern_atomic` (Fixpoint).
- `rw_facade_holes_atomic` (Fixpoint).
- `rw_facade_prepared_rule` (Record).
- `rw_facade_original_rule` (Projection).
- `rw_facade_core_rule` (Projection).
- `rw_facade_hole_set` (Projection).
- `RwFacadePreparedRule` (Constructor).
- `rw_facade_prepare_rule_atomic` (Definition).
- `rw_facade_prepared` (Record).
- `rw_facade_rule_entries` (Projection).
- `rw_facade_rule_table` (Projection).
- `rw_facade_original_table` (Projection).
- `rw_facade_core_rules` (Projection).
- `RwFacadePrepared` (Constructor).
- `rw_facade_prepare_atomic` (Fixpoint).
- `rw_facade_guard_plain` (Fixpoint).
- `rw_facade_guard_program_laws` (Definition).
- `rw_facade_guard_add_work` (Definition).
- `rw_facade_lift_guard` (Fixpoint).
- `rw_facade_local_callbacks` (Definition).
- `rw_facade_prepare_agrees_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadePrepareAdequacy`.

- `rw_facade_prepare_agrees` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadePublic

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_strategy_total_statement` (Definition).
- `rw_facade_strategy_unique_statement` (Definition).
- `rw_facade_strategy_agrees_statement` (Definition).
- `rw_facade_capture_exact_statement` (Definition).
- `rw_facade_selected_checked_statement` (Definition).
- `rw_facade_optimizer_total_statement` (Definition).
- `rw_facade_optimizer_unique_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadePublicAdequacy`.

- `rw_facade_strategy_total`: `AnalysesAuditRewriteFacadePublic.rw_facade_strategy_total_statement`;
  owner AUD-RP-FACADE.
- `rw_facade_strategy_unique` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_strategy_agrees` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_capture_exact`: `AnalysesAuditRewriteFacadePublic.rw_facade_capture_exact_statement`;
  owner AUD-RP-FACADE.
- `rw_facade_selected_checked` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_optimizer_total` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_optimizer_unique` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeReference

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_table_call` (Inductive).
- `RWFacadeTableSet` (Constructor).
- `RWFacadeTableGet` (Constructor).
- `rw_facade_table_atomic` (Fixpoint).
- `rw_facade_lookup_atomic` (Definition).
- `rw_facade_nth` (Fixpoint).
- `rw_facade_subst_call` (Inductive).
- `RWFacadeNth` (Constructor).
- `rw_facade_subst_atomic` (Fixpoint).
- `rw_facade_binding_atomic` (Definition).
- `rw_facade_guard_action` (Inductive).
- `RWGuardExternal` (Constructor).
- `RWGuardSubstitution` (Constructor).
- `rw_facade_guard_program` (Inductive).
- `RWFacadeGuardReturn` (Constructor).
- `RWFacadeGuardLookup` (Constructor).
- `rw_facade_guard_adapter` (Record).
- `rw_facade_guard_program_of` (Projection).
- `RWFacadeGuardAdapter` (Constructor).
- `rw_facade_guard_interpret` (Fixpoint).
- `rw_facade_guard_run` (Definition).
- `rw_facade_guard_action_valid` (Definition).
- `rw_facade_guard_adapter_adequate` (Definition).
- `rw_facade_vars` (Fixpoint).
- `rw_facade_leb` (Fixpoint).
- `rw_facade_forallb` (Fixpoint).
- `rw_facade_gate_call` (Inductive).
- `RWFacadeGuard` (Constructor).
- `rw_facade_lift_unit` (Definition).
- `rw_facade_gate_atomic` (Definition).
- `rw_facade_embed_atomic` (Fixpoint).
- `rw_facade_project_atomic` (Fixpoint).
- `rw_facade_at_core` (Fixpoint).
- `rw_facade_set_nth` (Fixpoint).
- `rw_facade_replace_core` (Fixpoint).
- `rw_facade_at_atomic` (Definition).
- `rw_facade_replace_atomic` (Definition).
- `rw_facade_code_call` (Inductive).
- `RWCodeOp` (Constructor).
- `RWCodeNat` (Constructor).
- `RWCodeAppend` (Constructor).
- `RWCodeLength` (Constructor).
- `RWCodeList` (Constructor).
- `RWCodeEmbed` (Constructor).
- `rw_facade_tree_code_atomic` (Fixpoint).
- `rw_facade_code_atomic` (Definition).
- `rw_facade_positive_eqb` (Fixpoint).
- `rw_facade_eq_call` (Inductive).
- `RWFacadeCode` (Constructor).
- `RWFacadeEqBits` (Constructor).
- `rw_facade_eq_atomic` (Definition).
- `rw_facade_step_call` (Inductive).
- `RWFacadeLookup` (Constructor).
- `RWFacadeGate` (Constructor).
- `RWFacadeSubst` (Constructor).
- `RWFacadePosition` (Constructor).
- `RWFacadeEqual` (Constructor).
- `RWFacadeReplace` (Constructor).
- `rw_facade_step_atomic` (Definition).
- `rw_facade_replay_call` (Inductive).
- `RWFacadeReplayStep` (Constructor).
- `rw_facade_replay_atomic` (Fixpoint).
- `rw_facade_checker_call` (Inductive).
- `RWFacadeCheckerTable` (Constructor).
- `RWFacadeCheckerReplay` (Constructor).
- `RWFacadeCheckerEqual` (Constructor).
- `rw_facade_checker_atomic` (Definition).
- `rw_facade_checker_erases_statement` (Definition).
- `rw_facade_checker_erases_contract` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeReferenceAdequacy`.

- `rw_facade_checker_erases` (future Theorem); owner AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeReference2

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_legacy_binding_limit` (Definition).
- `rw_legacy_binding_value` (Definition).
- `rw_legacy_binding_list` (Definition).
- `rw_legacy_offer_gate` (Definition).
- `rw_legacy_prepared_gate` (Definition).
- `rw_legacy_prepared_gate_agrees_contract` (Definition).
- `rw_legacy_choose` (Definition).
- `rw_legacy_choose_sound_contract` (Definition).
- `rw_legacy_choose_complete_contract` (Definition).
- `rw_legacy_make_bindings` (Fixpoint).
- `rw_legacy_rule_offers` (Definition).
- `rw_legacy_offers` (Definition).
- `rw_legacy_strategy` (Definition).
- `rw_legacy_strategy_gate_contract` (Definition).
- `rw_legacy_strategy_complete_offers_contract` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeReference2Adequacy`.

- `rw_legacy_prepared_gate_agrees`:
  `AnalysesAuditRewriteFacadeReference2.rw_legacy_prepared_gate_agrees_contract`; owner
  AUD-RP-FACADE.
- `rw_legacy_choose_sound`: `AnalysesAuditRewriteFacadeReference2.rw_legacy_choose_sound_contract`;
  owner AUD-RP-FACADE.
- `rw_legacy_choose_complete` (future Theorem); owner AUD-RP-FACADE.
- `rw_legacy_strategy_gate` (future Theorem); owner AUD-RP-FACADE.
- `rw_legacy_strategy_complete_offers`:
  `AnalysesAuditRewriteFacadeReference2.rw_legacy_strategy_complete_offers_contract`; owner
  AUD-RP-FACADE.

## AnalysesAuditRewriteFacadeRun

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_apply_atomic` (Definition).
- `rw_facade_once_run` (Inductive).
- `RPFOnceAlreadyStopped` (Constructor).
- `RPFOnceStop` (Constructor).
- `RPFOnceReject` (Constructor).
- `RPFOnceAccept` (Constructor).
- `rw_facade_repeat_run` (Inductive).
- `RPFRepeatStopped` (Constructor).
- `RPFRepeatOne` (Constructor).
- `RPFRepeatEven` (Constructor).
- `RPFRepeatOdd` (Constructor).
- `rw_facade_capture_entries` (Fixpoint).
- `rw_facade_capture_atomic` (Definition).
- `rw_legacy_tracked_state` (Record).
- `rw_legacy_root` (Projection).
- `rw_legacy_core` (Projection).
- `rw_legacy_leaves` (Projection).
- `RWLegacyTrackedState` (Constructor).
- `rw_facade_tracked_run` (Inductive).
- `RPFTrackedRun` (Constructor).

## AnalysesAuditRewriteFacadeSourceWork

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_table_source_work` (Definition).
- `rw_facade_subst_source_work` (Definition).
- `rw_facade_guard_source_work` (Definition).
- `rw_facade_gate_source_work` (Definition).
- `rw_facade_code_source_work` (Definition).
- `rw_facade_eq_source_work` (Definition).
- `rw_facade_step_source_work` (Definition).
- `rw_facade_replay_source_work` (Definition).
- `rw_facade_checker_source_work` (Definition).

## AnalysesAuditRewriteFacadeWholeContracts

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_term_ops` (Fixpoint).
- `rw_facade_core_ops` (Fixpoint).
- `rw_facade_input_ops` (Definition).
- `rw_facade_binding_dimension` (Definition).
- `rw_facade_guard_control` (Fixpoint).
- `rw_facade_guard_query_bound` (Fixpoint).
- `rw_facade_foreign_envelope` (Record).
- `rw_facade_foreign_operator` (Projection).
- `rw_facade_foreign_weight` (Projection).
- `rw_facade_foreign_guard` (Projection).
- `RwFacadeForeignEnvelope` (Constructor).
- `rw_facade_whole_ceiling` (Definition).
- `rw_facade_prepare_bound_statement` (Definition).
- `rw_facade_capture_bound_statement` (Definition).
- `rw_facade_materialize_bound_statement` (Definition).
- `rw_facade_optimizer_whole_bound_statement` (Definition).
- `rw_facade_node_ops` (Definition).
- `rw_facade_reason_ops` (Definition).
- `rw_facade_selected_ops` (Definition).
- `rw_facade_selected_total_statement` (Definition).
- `rw_facade_selected_unique_statement` (Definition).
- `rw_facade_selected_whole_bound_statement` (Definition).
- `rw_facade_fixed_encoders_statement` (Definition).

Future proof module: `AnalysesAuditRewriteFacadeWholeContractsAdequacy`.

- `rw_facade_prepare_bound` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_capture_bound` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_materialize_bound`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_materialize_bound_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_optimizer_whole_bound`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_optimizer_whole_bound_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_selected_total`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_selected_total_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_selected_unique`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_selected_unique_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_selected_whole_bound`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_selected_whole_bound_statement`; owner
  AUD-RP-FACADE.
- `rw_facade_fixed_encoders`:
  `AnalysesAuditRewriteFacadeWholeContracts.rw_facade_fixed_encoders_statement`; owner
  AUD-RP-FACADE.

## AnalysesAuditRewritePublicFamily

Public package: `Galois.Analyses`.

Card: AUD-RW-MODELS

- `rw_facade_public_tracked_source_cost_type` (Definition).
- `rw_facade_public_selected_source_cost_type` (Definition).
- `rw_facade_public_optimizer_source_cost_type` (Definition).
- `rw_fixed_public_source_family_statement` (Definition).

Future proof module: `AnalysesAuditRewritePublicFamilyAdequacy`.

- `rw_facade_public_tracked_source_cost` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_public_selected_source_cost` (future Theorem); owner AUD-RP-FACADE.
- `rw_facade_public_optimizer_source_cost` (future Theorem); owner AUD-RP-FACADE.

## RewriteAuditIndexBucket

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_bucket_call` (Inductive).
- `RIBucketRead` (Constructor).
- `RIBucketMember` (Constructor).
- `RIBucketWrite` (Constructor).
- `rw_ri_bucket_event_cost` (Definition).
- `rw_ri_bucket_trace_cost` (Definition).
- `rw_ri_bucket_add_atomic` (Definition).
- `rw_ri_bucket_remove_atomic` (Definition).
- `rw_ri_bucket_atomic_budget` (Definition).
- `rw_ri_bucket_add_erases_contract` (Definition).
- `rw_ri_bucket_remove_erases_contract` (Definition).
- `rw_ri_bucket_add_bound_contract` (Definition).
- `rw_ri_bucket_remove_bound_contract` (Definition).

Future proof module: `RewriteAuditIndexBucketAdequacy`.

- `rw_ri_bucket_add_erases`: `RewriteAuditIndexBucket.rw_ri_bucket_add_erases_contract`; owner
  AUD-RI.
- `rw_ri_bucket_remove_erases`: `RewriteAuditIndexBucket.rw_ri_bucket_remove_erases_contract`; owner
  AUD-RI.
- `rw_ri_bucket_add_bound`: `RewriteAuditIndexBucket.rw_ri_bucket_add_bound_contract`; owner AUD-RI.
- `rw_ri_bucket_remove_bound`: `RewriteAuditIndexBucket.rw_ri_bucket_remove_bound_contract`; owner
  AUD-RI.

## RewriteAuditIndexBuild

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_build_acc` (Record).
- `rw_ri_build_ops` (Projection).
- `rw_ri_build_vars` (Projection).
- `rw_ri_build_parents` (Projection).
- `RwRiBuildAcc` (Constructor).
- `rw_ri_bucket_add` (Definition).
- `rw_ri_build_parent_nodes_value` (Fixpoint).
- `rw_ri_build_nodes_value` (Fixpoint).

## RewriteAuditIndexCompare

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_positive_call` (Inductive).
- `RIPositiveDecision` (Constructor).
- `RIPositiveFrame` (Constructor).
- `rw_ri_positive_dec_atomic` (Definition).
- `rw_ri_positive_dec_budget` (Definition).
- `rw_ri_positive_dec_erases_contract` (Definition).
- `rw_ri_positive_dec_bound_contract` (Definition).

Future proof module: `RewriteAuditIndexCompareAdequacy`.

- `rw_ri_positive_dec_erases`: `RewriteAuditIndexCompare.rw_ri_positive_dec_erases_contract`; owner
  AUD-RI.
- `rw_ri_positive_dec_bound`: `RewriteAuditIndexCompare.rw_ri_positive_dec_bound_contract`; owner
  AUD-RI.

## RewriteAuditIndexDimensions

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_term_dimension` (Fixpoint).
- `rw_whole_pattern_dimension` (Fixpoint).
- `rw_whole_ids_dimension` (Definition).
- `rw_whole_map_dimension` (Definition).
- `rw_whole_set_dimension` (Definition).
- `rw_whole_node_dimension` (Definition).
- `rw_whole_graph_dimension` (Definition).
- `rw_whole_forest_dimension` (Definition).
- `rw_whole_index_dimension` (Definition).
- `rw_whole_bindings_dimension` (Definition).
- `rw_whole_attempt_dimension` (Definition).
- `rw_whole_rules_dimension` (Definition).

## RewriteAuditIndexDimensions2

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_shared_node_dimension` (Definition).

## RewriteAuditIndexDimensions3

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_event_attempt_dimension` (Definition).

## RewriteAuditIndexDimensions4

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_source_ceiling` (Definition).

## RewriteAuditIndexDirty

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_node_event` (Definition).
- `rw_ri_node_encoder` (Definition).
- `rw_ri_node_encoding_work` (Definition).
- `rw_ri_dirty_call` (Inductive).
- `RIDirtySet` (Constructor).
- `RIDirtyNode` (Constructor).
- `RIDirtyOldKey` (Constructor).
- `RIDirtyBucket` (Constructor).
- `RIDirtyCanon` (Constructor).
- `RIDirtySignature` (Constructor).
- `RIDirtyPeers` (Constructor).
- `RIDirtyPairs` (Constructor).
- `RIDirtyPending` (Constructor).
- `RIDirtyKeySet` (Constructor).
- `rw_ri_dirty_event_cost` (Definition).
- `rw_ri_dirty_trace_cost` (Definition).
- `rw_ri_peer_pairs_atomic` (Fixpoint).
- `rw_ri_dirty_tick_atomic` (Definition).
- `rw_ri_dirty_tick_budget` (Definition).
- `rw_ri_dirty_client_statement` (Definition).
- `rw_ri_dirty_client_contract` (Definition).

Future proof module: `RewriteAuditIndexDirtyAdequacy`.

- `rw_ri_dirty_client`: `RewriteAuditIndexDirty.rw_ri_dirty_client_contract`; owner AUD-RI.

## RewriteAuditIndexEventEnvelope

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_event_external` (Definition).

## RewriteAuditIndexExternal

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_encoder_fits` (Definition).
- `rw_whole_term_atoms` (Fixpoint).
- `rw_whole_pattern_atoms` (Fixpoint).
- `rw_whole_node_atoms` (Definition).
- `rw_whole_graph_atoms` (Definition).
- `rw_whole_index_atoms` (Definition).
- `rw_whole_term_callbacks` (Fixpoint).
- `rw_whole_guard_control` (Fixpoint).
- `rw_whole_guard_queries` (Fixpoint).
- `rw_whole_rules_external` (Definition).
- `rw_whole_attempt_external` (Definition).
- `rw_whole_request_external` (Definition).
- `rw_whole_view_control` (Fixpoint).
- `rw_whole_view_queries` (Fixpoint).
- `rw_whole_strategy_external` (Definition).

## RewriteAuditIndexFind

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_find_call` (Inductive).
- `RIFindBase` (Constructor).
- `RIFindForest` (Constructor).
- `rw_ri_find_event_cost` (Definition).
- `rw_ri_find_trace_cost` (Definition).
- `rw_ri_find_atomic` (Definition).
- `rw_ri_find_fuel_budget` (Fixpoint).
- `rw_ri_find_budget` (Definition).
- `rw_ri_canon_call` (Inductive).
- `RICanonFind` (Constructor).
- `rw_ri_canon_event_cost` (Definition).
- `rw_ri_canon_trace_cost` (Definition).
- `rw_ri_canon_children` (Fixpoint).
- `rw_ri_canon_atomic` (Definition).
- `rw_ri_canon_children_budget` (Fixpoint).
- `rw_ri_canon_budget` (Definition).
- `rw_ri_find_erases_contract` (Definition).
- `rw_ri_find_bound_contract` (Definition).
- `rw_ri_canon_erases_contract` (Definition).
- `rw_ri_canon_bound_contract` (Definition).

Future proof module: `RewriteAuditIndexFindAdequacy`.

- `rw_ri_find_erases`: `RewriteAuditIndexFind.rw_ri_find_erases_contract`; owner AUD-RI.
- `rw_ri_find_bound`: `RewriteAuditIndexFind.rw_ri_find_bound_contract`; owner AUD-RI.
- `rw_ri_canon_erases`: `RewriteAuditIndexFind.rw_ri_canon_erases_contract`; owner AUD-RI.
- `rw_ri_canon_bound`: `RewriteAuditIndexFind.rw_ri_canon_bound_contract`; owner AUD-RI.

## RewriteAuditIndexInterfaceIndexRuleStepSupportedContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_rule_step_supported_contract` (Definition).

## RewriteAuditIndexInterfaceIndexRunCallbackBoundContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_run_callback_bound_contract` (Definition).

## RewriteAuditIndexInterfaceIndexRunCleanTraceContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_run_clean_trace_contract` (Definition).

## RewriteAuditIndexInterfaceIndexRunCorrectContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_run_correct_contract` (Definition).

## RewriteAuditIndexInterfaceIndexRunZeroContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_run_zero_contract` (Definition).

## RewriteAuditIndexInterfaceRiApplyRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_apply_realizes_statement` (Definition).

## RewriteAuditIndexInterfaceRiRuleStepRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_rule_step_realizes_statement` (Definition).

## RewriteAuditIndexInterfaceRiRunRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_run_realizes_statement` (Definition).

## RewriteAuditIndexMark

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_mark_call` (Inductive).
- `RIMarkMem` (Constructor).
- `RIMarkAdd` (Constructor).
- `rw_ri_mark_event_cost` (Definition).
- `rw_ri_mark_trace_cost` (Definition).
- `rw_ri_mark_dirty_atomic` (Fixpoint).
- `rw_ri_mark_budget` (Fixpoint).
- `rw_ri_mark_erases_contract` (Definition).
- `rw_ri_mark_bound_contract` (Definition).

Future proof module: `RewriteAuditIndexMarkAdequacy`.

- `rw_ri_mark_erases`: `RewriteAuditIndexMark.rw_ri_mark_erases_contract`; owner AUD-RI.
- `rw_ri_mark_bound`: `RewriteAuditIndexMark.rw_ri_mark_bound_contract`; owner AUD-RI.

## RewriteAuditIndexMatch

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_match_append` (Fixpoint).
- `rw_ri_bind_atomic` (Definition).
- `rw_ri_match_flat_map` (Fixpoint).
- `rw_ri_match_children_atomic` (Fixpoint).
- `rw_ri_match_candidates_atomic` (Definition).
- `rw_ri_match_on_atomic` (Fixpoint).
- `rw_ri_assignment_encode` (Definition).
- `rw_ri_assignment_encode_work` (Definition).
- `rw_ri_assignment_table_atomic` (Fixpoint).
- `rw_ri_distinct_assignments_atomic` (Definition).
- `rw_ri_match_atomic` (Definition).
- `rw_ri_match_erases_statement` (Definition).

Future proof module: `RewriteAuditIndexMatchAdequacy`.

- `rw_ri_match_erases`: `RewriteAuditIndexMatch.rw_ri_match_erases_statement`; owner AUD-RI.

## RewriteAuditIndexMatchReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_view_match_candidates` (Definition).
- `rw_view_same_class` (Definition).
- `rw_view_match_on` (Fixpoint).
- `rw_view_match` (Definition).
- `rw_view_match_sound_contract` (Definition).
- `rw_view_match_complete_contract` (Definition).
- `rw_view_match_assignment_contract` (Definition).
- `rw_view_match_nodup_contract` (Definition).

Future proof module: `RewriteAuditIndexMatchReferenceAdequacy`.

- `rw_view_match_sound`: `RewriteAuditIndexMatchReference.rw_view_match_sound_contract`; owner
  AUD-RI.
- `rw_view_match_complete`: `RewriteAuditIndexMatchReference.rw_view_match_complete_contract`; owner
  AUD-RI.
- `rw_view_match_assignment`: `RewriteAuditIndexMatchReference.rw_view_match_assignment_contract`;
  owner AUD-RI.
- `rw_view_match_nodup`: `RewriteAuditIndexMatchReference.rw_view_match_nodup_contract`; owner
  AUD-RI.

## RewriteAuditIndexMembership

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_encoded_equal` (Definition).
- `rw_ri_same_class_atomic` (Definition).
- `rw_ri_bucket_ids` (Definition).
- `rw_ri_member_atomic` (Fixpoint).
- `rw_ri_member_spec_statement` (Definition).

Future proof module: `RewriteAuditIndexMembershipAdequacy`.

- `rw_ri_member_spec`: `RewriteAuditIndexMembership.rw_ri_member_spec_statement`; owner AUD-RI.

## RewriteAuditIndexPair

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_pair_call` (Inductive).
- `RIPairNode` (Constructor).
- `RIPairFind` (Constructor).
- `RIPairCanon` (Constructor).
- `RIPairNodeCode` (Constructor).
- `RIPairDecision` (Constructor).
- `RIPairSort` (Constructor).
- `RIPairSortCode` (Constructor).
- `RIPairUnion` (Constructor).
- `RIPairForestFind` (Constructor).
- `RIPairParentMap` (Constructor).
- `RIPairSetUnion` (Constructor).
- `RIPairParentElements` (Constructor).
- `RIPairMark` (Constructor).
- `rw_ri_pair_event_cost` (Definition).
- `rw_ri_pair_trace_cost` (Definition).
- `rw_ri_pair_skip` (Definition).
- `rw_ri_pair_merge_atomic` (Definition).
- `rw_ri_pair_atomic` (Definition).

## RewriteAuditIndexPlainContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_rule_step_realizes_fixed_type` (Definition).
- `rw_ri_apply_realizes_fixed_type` (Definition).
- `rw_ri_run_realizes_fixed_type` (Definition).
- `rw_index_run_clean_trace_fixed_type` (Definition).
- `rw_index_run_zero_fixed_type` (Definition).
- `rw_index_run_correct_fixed_type` (Definition).
- `rw_index_run_callback_bound_fixed_type` (Definition).
- `rw_index_rule_step_supported_fixed_type` (Definition).

Future proof module: `RewriteAuditIndexInterfaceIndexRuleStepSupportedContractAdequacy`.

- `rw_index_rule_step_supported` (future Theorem); owner AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceIndexRunCallbackBoundContractAdequacy`.

- `rw_index_run_callback_bound` (future Theorem); owner AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceIndexRunCleanTraceContractAdequacy`.

- `rw_index_run_clean_trace`: `RewriteAuditIndexPlainContracts.rw_index_run_clean_trace_fixed_type`;
  owner AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceIndexRunCorrectContractAdequacy`.

- `rw_index_run_correct`: `RewriteAuditIndexPlainContracts.rw_index_run_correct_fixed_type`; owner
  AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceIndexRunZeroContractAdequacy`.

- `rw_index_run_zero`: `RewriteAuditIndexPlainContracts.rw_index_run_zero_fixed_type`; owner AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceRiApplyRealizesStatementAdequacy`.

- `rw_ri_apply_realizes`: `RewriteAuditIndexPlainContracts.rw_ri_apply_realizes_fixed_type`; owner
  AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceRiRuleStepRealizesStatementAdequacy`.

- `rw_ri_rule_step_realizes`: `RewriteAuditIndexPlainContracts.rw_ri_rule_step_realizes_fixed_type`;
  owner AUD-RI.

Future proof module: `RewriteAuditIndexInterfaceRiRunRealizesStatementAdequacy`.

- `rw_ri_run_realizes`: `RewriteAuditIndexPlainContracts.rw_ri_run_realizes_fixed_type`; owner
  AUD-RI.

## RewriteAuditIndexPlainPublic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_rule_step` (Definition).
- `rw_index_run` (Definition).
- `rw_index_apply` (Definition).

## RewriteAuditIndexPreparationContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_prepare_once_bound_statement` (Definition).

Future proof module: `RewriteAuditIndexPreparationContractsAdequacy`.

- `rw_ri_prepare_once_bound` (future Theorem); owner AUD-RI.

## RewriteAuditIndexPrepare

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_prepare_receipt` (Inductive).
- `RIPrepareBlock` (Constructor).
- `RIPrepareNodeRead` (Constructor).
- `RIPrepareRootRead` (Constructor).
- `RIPrepareOperatorOnce` (Constructor).
- `RIPrepareVariableOnce` (Constructor).
- `RIPrepareParentOnce` (Constructor).
- `RIPrepareDirtyOnce` (Constructor).
- `RIPrepareFreshOnce` (Constructor).
- `rw_ri_prepare_receipt_work` (Definition).
- `rw_ri_prepare_once_work` (Definition).
- `rw_ri_prepare_parents_once` (Fixpoint).
- `rw_ri_prepare_nodes_once` (Fixpoint).
- `rw_ri_prepare_once` (Definition).
- `rw_ri_prepare_once_erases_statement` (Definition).
- `rw_ri_prepare_once_receipts_statement` (Definition).

Future proof module: `RewriteAuditIndexPrepareAdequacy`.

- `rw_ri_prepare_once_erases`: `RewriteAuditIndexPrepare.rw_ri_prepare_once_erases_statement`; owner
  AUD-RI.
- `rw_ri_prepare_once_receipts`: `RewriteAuditIndexPrepare.rw_ri_prepare_once_receipts_statement`;
  owner AUD-RI.

## RewriteAuditIndexPrepareReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_fresh_call` (Inductive).
- `RIFreshRoots` (Constructor).
- `RIFreshNodes` (Constructor).
- `RIFreshMax` (Constructor).
- `RIFreshSucc` (Constructor).
- `rw_ri_fresh_event_cost` (Definition).
- `rw_ri_fresh_trace_cost` (Definition).
- `rw_ri_max_entries_atomic` (Fixpoint).
- `rw_ri_fresh_atomic` (Definition).
- `rw_ri_fresh_value` (Definition).
- `rw_index_build` (Definition).

## RewriteAuditIndexProgramLaws

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_callbacks_agree` (Definition).
- `rw_rp_query_agrees` (Definition).
- `rw_rp_strategy_adapter_laws` (Definition).

## RewriteAuditIndexPrograms

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_query` (Inductive).
- `RPQueryFind` (Constructor).
- `RPQuerySort` (Constructor).
- `RPQueryNode` (Constructor).
- `RPQueryOperator` (Constructor).
- `RPQueryVariable` (Constructor).
- `RPQueryParents` (Constructor).
- `RPQueryRoots` (Constructor).
- `RPQueryNodes` (Constructor).
- `RPQueryGraph` (Constructor).
- `rw_rp_view_request` (Inductive).
- `RPRequestFind` (Constructor).
- `RPRequestSort` (Constructor).
- `RPRequestNode` (Constructor).
- `RPRequestOperator` (Constructor).
- `RPRequestVariable` (Constructor).
- `RPRequestParents` (Constructor).
- `RPRequestRoots` (Constructor).
- `RPRequestNodes` (Constructor).
- `RPRequestGraph` (Constructor).
- `rw_rp_view_program` (Inductive).
- `RPViewReturn` (Constructor).
- `RPViewAsk` (Constructor).
- `rw_rp_provider_trace` (Inductive).
- `RPProviderFind` (Constructor).
- `RPProviderPositive` (Constructor).
- `RPProviderOperator` (Constructor).
- `RPProviderVariable` (Constructor).
- `RPProviderElements` (Constructor).
- `RPProviderGraph` (Constructor).
- `rw_rp_provider_trace_work` (Definition).
- `rw_rp_query_receipt` (Record).
- `rw_rp_query_observation` (Projection).
- `rw_rp_query_sources` (Projection).
- `RwRpQueryReceipt` (Constructor).
- `rw_rp_query_receipt_work` (Definition).
- `rw_rp_view_plain_request` (Definition).
- `rw_rp_view_plain` (Fixpoint).
- `rw_rp_view_execute_request` (Definition).
- `rw_rp_view_execute` (Fixpoint).
- `rw_rp_strategy_adapter` (Record).
- `rw_rp_strategy_program` (Projection).
- `RwRpStrategyAdapter` (Constructor).
- `rw_rp_strategy_run` (Definition).

## RewriteAuditIndexPublic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_index_clean_trace` (Inductive).
- `RWIndexCleanTraceNil` (Constructor).
- `RWIndexCleanTraceReject` (Constructor).
- `RWIndexCleanTraceAccept` (Constructor).
- `rw_index_result` (Definition).
- `rw_index_clean_contract` (Definition).
- `rw_index_sound_contract` (Definition).
- `rw_index_witness_contract` (Definition).
- `index_nonempty_buckets` (Definition).
- `index_parent_support` (Definition).
- `index_supported_valid` (Definition).
- `index_support_cardinality_type` (Definition).
- `index_supported_cardinality_contract` (Definition).
- `bucket_member_count` (Definition).
- `bucket_node_support` (Definition).
- `index_bucket_node_support` (Definition).
- `index_member_node_bound_contract` (Definition).
- `rw_index_build_supported_contract` (Definition).
- `rw_index_tick_supported_contract` (Definition).

Future proof module: `RewriteAuditIndexPublicAdequacy`.

- `rw_index_clean`: `RewriteAuditIndexPublic.rw_index_clean_contract`; owner AUD-RI.
- `rw_index_sound`: `RewriteAuditIndexPublic.rw_index_sound_contract`; owner AUD-RI.
- `rw_index_witness`: `RewriteAuditIndexPublic.rw_index_witness_contract`; owner AUD-RI.
- `index_supported_cardinality`: `RewriteAuditIndexPublic.index_supported_cardinality_contract`;
  owner AUD-RI.
- `index_member_node_bound`: `RewriteAuditIndexPublic.index_member_node_bound_contract`; owner
  AUD-RI.
- `rw_index_build_supported`: `RewriteAuditIndexPublic.rw_index_build_supported_contract`; owner
  AUD-RI.
- `rw_index_tick_supported`: `RewriteAuditIndexPublic.rw_index_tick_supported_contract`; owner
  AUD-RI.

## RewriteAuditIndexPublicSource

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_public_source_cost_statement` (Definition).

Future proof module: `RewriteAuditIndexPublicSourceAdequacy`.

- `rw_ri_public_source_cost`: `RewriteAuditIndexPublicSource.rw_ri_public_source_cost_statement`;
  owner AUD-RI.

## RewriteAuditIndexRebuild

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_tick_call` (Inductive).
- `RITickDirty` (Constructor).
- `RITickPop` (Constructor).
- `RITickPair` (Constructor).
- `rw_ri_tick_event_cost` (Definition).
- `rw_ri_tick_trace_cost` (Definition).
- `rw_ri_tick_atomic` (Definition).
- `rw_ri_tick_erases_statement` (Definition).
- `rw_ri_repeat_call` (Inductive).
- `RIRepeatTick` (Constructor).
- `rw_ri_repeat_event_cost` (Definition).
- `rw_ri_repeat_trace_cost` (Definition).
- `rw_ri_repeat_once` (Definition).
- `rw_ri_repeat_atomic` (Fixpoint).
- `rw_ri_repeat_erases_statement` (Definition).
- `rw_ri_reverse_onto` (Fixpoint).
- `rw_ri_repeat_tick_count` (Definition).
- `rw_ri_repeat_tick_bound_statement` (Definition).
- `rw_ri_forest_root_atomic` (Definition).
- `rw_ri_roots_atomic` (Fixpoint).
- `rw_ri_graph_atomic` (Definition).
- `rw_ri_rebuild_fuel_atomic` (Definition).
- `rw_ri_rebuild_atomic` (Definition).
- `rw_ri_graph_erases_statement` (Definition).
- `rw_ri_rebuild_fuel_erases_statement` (Definition).
- `rw_ri_rebuild_erases_statement` (Definition).
- `rw_ri_pair_erases_statement` (Definition).
- `rw_ri_pair_node_read_count` (Definition).

Future proof module: `RewriteAuditIndexRebuildAdequacy`.

- `rw_ri_tick_erases`: `RewriteAuditIndexRebuild.rw_ri_tick_erases_statement`; owner AUD-RI.
- `rw_ri_repeat_erases`: `RewriteAuditIndexRebuild.rw_ri_repeat_erases_statement`; owner AUD-RI.
- `rw_ri_repeat_tick_bound`: `RewriteAuditIndexRebuild.rw_ri_repeat_tick_bound_statement`; owner
  AUD-RI.
- `rw_ri_graph_erases`: `RewriteAuditIndexRebuild.rw_ri_graph_erases_statement`; owner AUD-RI.
- `rw_ri_rebuild_fuel_erases`: `RewriteAuditIndexRebuild.rw_ri_rebuild_fuel_erases_statement`; owner
  AUD-RI.
- `rw_ri_rebuild_erases`: `RewriteAuditIndexRebuild.rw_ri_rebuild_erases_statement`; owner AUD-RI.
- `rw_ri_pair_erases`: `RewriteAuditIndexRebuild.rw_ri_pair_erases_statement`; owner AUD-RI.

## RewriteAuditIndexReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_phase_view` (Record).
- `rw_view_find` (Projection).
- `rw_view_sort` (Projection).
- `rw_view_node` (Projection).
- `rw_view_operator_nodes` (Projection).
- `rw_view_variable_nodes` (Projection).
- `rw_view_parent_nodes` (Projection).
- `rw_view_roots` (Projection).
- `rw_view_nodes` (Projection).
- `RwPhaseView` (Constructor).
- `rw_snapshot_view` (Record).
- `rw_snapshot_base` (Projection).
- `rw_snapshot_graph` (Projection).
- `RwSnapshotView` (Constructor).
- `rw_view_agrees` (Definition).
- `rw_phase_ordered` (Definition).
- `rw_snapshot_agrees` (Definition).
- `rw_snapshot_extract` (Definition).
- `rw_snapshot_extract_agrees_contract` (Definition).
- `rw_index_event` (Inductive).
- `RWIndexDirty` (Constructor).
- `RWIndexSkipped` (Constructor).
- `RWIndexCongruence` (Constructor).
- `rw_run_event` (Inductive).
- `RWRunRejected` (Constructor).
- `RWRunAccepted` (Constructor).
- `rw_index_state` (Record).
- `rw_index_base` (Projection).
- `rw_index_forest` (Projection).
- `rw_index_parent_buckets` (Projection).
- `rw_index_signatures` (Projection).
- `rw_index_node_keys` (Projection).
- `rw_index_dirty_order` (Projection).
- `rw_index_dirty_set` (Projection).
- `rw_index_pending` (Projection).
- `rw_index_operators` (Projection).
- `rw_index_variables` (Projection).
- `rw_index_fresh` (Projection).
- `RWIndexState` (Constructor).
- `rw_index_find` (Definition).
- `rw_index_graph` (Definition).
- `rw_index_bucket` (Definition).
- `rw_index_view` (Definition).
- `rw_index_canonical_node` (Definition).
- `rw_index_phase_clean` (Definition).
- `rw_index_valid` (Definition).

Future proof module: `RewriteAuditIndexReferenceAdequacy`.

- `rw_snapshot_extract_agrees`: `RewriteAuditIndexReference.rw_snapshot_extract_agrees_contract`;
  owner AUD-RI.

## RewriteAuditIndexRuleTableContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_rule_table_bound_statement` (Definition).

Future proof module: `RewriteAuditIndexRuleTableContractsAdequacy`.

- `rw_rp_rule_table_bound`: `RewriteAuditIndexRuleTableContracts.rw_rp_rule_table_bound_statement`;
  owner AUD-RI.

## RewriteAuditIndexRules

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_guard_program` (Inductive).
- `RPGuardReturn` (Constructor).
- `RPGuardLookup` (Constructor).
- `rw_rp_guard_plain` (Fixpoint).
- `rw_rp_guard_execute` (Fixpoint).
- `rw_rp_rule_callbacks` (Record).
- `rw_rp_var_sort` (Projection).
- `rw_rp_operator_shape` (Projection).
- `rw_rp_hole_sort` (Projection).
- `rw_rp_guard` (Projection).
- `RwRpRuleCallbacks` (Constructor).
- `rw_rp_term_sorts` (Fixpoint).
- `rw_rp_type_atomic` (Fixpoint).
- `rw_rp_sub_check_atomic` (Fixpoint).
- `rw_rp_guard_atomic` (Definition).
- `rw_rp_instantiate_atomic` (Fixpoint).
- `rw_rp_rule_lookup` (Fixpoint).
- `rw_rp_rule_table_atomic` (Fixpoint).
- `rw_rp_rule_body_gate_atomic` (Definition).
- `rw_rp_rule_gate_prepared_atomic` (Definition).
- `rw_rp_rule_gate_atomic` (Definition).
- `rw_rp_rule_table_erases_statement` (Definition).
- `rw_rp_instantiate_erases_statement` (Definition).
- `rw_rp_guard_adapter_laws` (Definition).

Future proof module: `RewriteAuditIndexRulesAdequacy`.

- `rw_rp_rule_table_erases`: `RewriteAuditIndexRules.rw_rp_rule_table_erases_statement`; owner
  AUD-RI.
- `rw_rp_instantiate_erases`: `RewriteAuditIndexRules.rw_rp_instantiate_erases_statement`; owner
  AUD-RI.

## RewriteAuditIndexRun

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_grow_node` (Definition).
- `rw_ri_grow_term` (Fixpoint).
- `rw_ri_accept_atomic` (Definition).
- `rw_ri_rule_step_prepared_atomic` (Definition).
- `rw_ri_rule_step_atomic` (Definition).
- `rw_ri_apply_prepared_atomic` (Definition).
- `rw_ri_apply_atomic` (Definition).
- `rw_ri_runner` (Record).
- `rw_ri_runner_state` (Projection).
- `rw_ri_runner_stopped` (Projection).
- `rw_ri_runner_events` (Projection).
- `RwRiRunner` (Constructor).
- `rw_ri_run_once` (Definition).
- `rw_ri_run_repeat` (Fixpoint).
- `rw_ri_run_atomic` (Definition).
- `rw_ri_run_zero_source_statement` (Definition).
- `rw_ri_run_semantic_statement` (Definition).

Future proof module: `RewriteAuditIndexRunAdequacy`.

- `rw_ri_run_zero_source`: `RewriteAuditIndexRun.rw_ri_run_zero_source_statement`; owner AUD-RI.
- `rw_ri_run_semantic`: `RewriteAuditIndexRun.rw_ri_run_semantic_statement`; owner AUD-RI.

## RewriteAuditIndexTickReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_state_update` (Definition).
- `rw_ri_bucket_remove` (Definition).
- `rw_ri_mark_dirty` (Fixpoint).
- `rw_ri_dirty_tick` (Definition).
- `rw_ri_pair_tick` (Definition).
- `rw_index_tick` (Definition).
- `rw_ri_rebuild_done` (Definition).
- `rw_ri_rebuild_step` (Definition).
- `rw_ri_rebuild_fuel` (Definition).
- `rw_index_rebuild` (Definition).

## RewriteAuditIndexWholeContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_ri_whole_operand_dimension` (Definition).
- `rw_ri_whole_invocation` (Record).
- `rw_ri_whole_input_atoms` (Projection).
- `rw_ri_whole_output_atoms` (Projection).
- `rw_ri_whole_rules_external` (Projection).
- `rw_ri_whole_event_external` (Projection).
- `rw_ri_whole_strategy_external` (Projection).
- `RwRiWholeInvocation` (Constructor).
- `rw_ri_whole_bound_statement` (Definition).
- `rw_ri_match_bound_statement` (Definition).

Future proof module: `RewriteAuditIndexWholeContractsAdequacy`.

- `rw_ri_whole_bound`: `RewriteAuditIndexWholeContracts.rw_ri_whole_bound_statement`; owner AUD-RI.
- `rw_ri_match_bound`: `RewriteAuditIndexWholeContracts.rw_ri_match_bound_statement`; owner AUD-RI.

## RewriteAuditPlainCore1

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_rw_ri_encoded_equal` (Definition).
- `rw_plain_rw_ri_same_class_atomic` (Definition).
- `rw_plain_rw_ri_member_atomic` (Fixpoint).
- `rw_plain_rw_ri_grow_node` (Definition).
- `rw_plain_rw_ri_grow_term` (Fixpoint).
- `rw_plain_rw_ri_accept_atomic` (Definition).
- `rw_plain_rw_rp_term_sorts` (Fixpoint).
- `rw_plain_rw_rp_type_atomic` (Fixpoint).
- `rw_plain_rw_rp_sub_check_atomic` (Fixpoint).
- `rw_plain_rw_rp_instantiate_atomic` (Fixpoint).
- `rw_plain_rw_rp_rule_body_gate_atomic` (Definition).
- `rw_plain_rw_rp_rule_gate_prepared_atomic` (Definition).
- `rw_plain_rw_ri_rule_step_prepared_atomic` (Definition).
- `rw_plain_rw_rp_rule_table_atomic` (Fixpoint).
- `rw_plain_rw_ri_rule_step_atomic` (Definition).
- `rw_plain_rw_ri_apply_prepared_atomic` (Definition).
- `rw_plain_rw_ri_run_once` (Definition).
- `rw_plain_rw_ri_run_repeat` (Fixpoint).
- `rw_plain_rw_ri_run_atomic` (Definition).
- `rw_plain_rw_rp_append` (Fixpoint).

## RewriteAuditPlainCore2

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_rw_rp_term_tokens` (Fixpoint).
- `rw_plain_rw_rp_term_key` (Definition).
- `rw_plain_rw_rp_fresh_loop` (Fixpoint).
- `rw_plain_rw_rp_proof_get` (Definition).
- `rw_plain_rw_rp_proof_put` (Definition).
- `rw_plain_rw_rp_add_evidence` (Definition).
- `rw_plain_rw_rp_index_existing` (Fixpoint).
- `rw_plain_rw_rp_try_symmetry` (Definition).
- `rw_plain_rw_rp_try_transitivity` (Fixpoint).
- `rw_plain_rw_rp_children_evidence` (Fixpoint).
- `rw_plain_rw_rp_try_congruence` (Definition).
- `rw_plain_rw_rp_close_pair` (Definition).
- `rw_plain_rw_rp_close_row` (Fixpoint).
- `rw_plain_rw_rp_close_pass` (Fixpoint).
- `rw_plain_rw_rp_close_rounds` (Fixpoint).
- `rw_plain_rw_rp_subterms` (Fixpoint).
- `rw_plain_rw_rp_nat_compare` (Fixpoint).
- `rw_plain_rw_rp_evidence_terms` (Fixpoint).
- `rw_plain_rw_rp_connect_atomic` (Definition).
- `rw_plain_rw_rp_stamp_put` (Definition).
- `rw_plain_rw_shared_unfold_atomic` (Definition).

## RewriteAuditPlainCore3

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_rw_rp_witness_merge` (Definition).
- `rw_plain_rw_rp_witness_read` (Definition).
- `rw_plain_rw_rp_connect_at_atomic` (Definition).
- `rw_plain_rw_rp_record_connection` (Definition).
- `rw_plain_rw_rp_tick_atomic` (Definition).
- `rw_plain_rw_rp_seed_node` (Definition).
- `rw_plain_rw_rp_seed_term` (Fixpoint).
- `rw_plain_rw_rp_seed_atomic` (Definition).
- `rw_plain_rw_rp_rebuild_done` (Definition).
- `rw_plain_rw_rp_rebuild_once` (Definition).
- `rw_plain_rw_rp_rebuild_repeat` (Fixpoint).
- `rw_plain_rw_ri_reverse_onto` (Fixpoint).
- `rw_plain_rw_rp_rebuild_atomic` (Definition).
- `rw_plain_rw_rp_rule_gate_atomic` (Definition).
- `rw_plain_rw_rp_accept_atomic` (Definition).
- `rw_plain_rw_rp_rule_step_prepared_atomic` (Definition).
- `rw_plain_rw_rp_rule_step_atomic` (Definition).
- `rw_plain_rw_rp_apply_prepared_atomic` (Definition).
- `rw_plain_rw_rp_apply_atomic` (Definition).
- `rw_plain_rw_rp_run_once` (Definition).

## RewriteAuditPlainCore4

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_rw_rp_run_repeat` (Fixpoint).
- `rw_plain_rw_rp_run_atomic` (Definition).
- `rw_plain_rw_rp_fact_run_once` (Definition).
- `rw_plain_rw_rp_fact_run_repeat` (Fixpoint).
- `rw_plain_rw_rp_fact_run_atomic` (Definition).
- `rw_plain_rw_rp_selected_atomic` (Definition).
- `rw_plain_rw_rp_repr_emit` (Definition).
- `rw_plain_rw_rp_repr_term_atomic` (Fixpoint).
- `rw_plain_rw_rp_repr_find_atomic` (Definition).

## RewriteAuditPlainPrimitives

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_audit_positive_encode` (Definition).
- `rw_plain_audit_nat_encode` (Definition).
- `rw_plain_audit_pair_encode` (Definition).
- `rw_plain_rw_rd_pair_encode` (Definition).
- `rw_plain_rw_rp_stamp_encode` (Definition).
- `rw_plain_rw_queue_encoder_run` (Definition).
- `rw_plain_rw_external_encoding_events` (Definition).
- `rw_plain_rw_external_events_work` (Definition).
- `rw_plain_audit_map_get` (Definition).
- `rw_plain_audit_map_set` (Definition).
- `rw_plain_audit_map_remove` (Definition).
- `rw_plain_audit_map_elements` (Definition).
- `rw_plain_audit_list_encode` (Definition).
- `rw_plain_audit_positive_eqb` (Definition).
- `rw_plain_rw_fuel_pos_succ` (Definition).
- `rw_plain_rw_fuel_length` (Definition).
- `rw_plain_rw_fuel_add` (Definition).
- `rw_plain_rw_fuel_mul` (Definition).
- `rw_plain_rw_fuel_to_positive` (Definition).
- `rw_plain_rw_rd_positive_compare_cont` (Definition).
- `rw_plain_rw_ri_positive_dec_atomic` (Definition).
- `rw_plain_rw_ri_find_atomic` (Definition).
- `rw_plain_rw_ri_canon_atomic` (Definition).
- `rw_plain_rw_ri_graph_atomic` (Definition).
- `rw_plain_rw_ri_tick_atomic` (Definition).
- `rw_plain_rw_ri_rebuild_atomic` (Definition).
- `rw_plain_rw_ri_rebuild_fuel_atomic` (Definition).
- `rw_plain_rw_ri_bucket_ids` (Definition).
- `rw_plain_rw_ri_prepare_once` (Definition).
- `rw_plain_rw_ri_max_entries_atomic` (Fixpoint).
- `rw_plain_rw_ri_pair_merge_atomic` (Definition).
- `rw_plain_callbacks` (Record).
- `rw_plain_rw_rp_var_sort` (Projection).
- `rw_plain_rw_rp_operator_shape` (Projection).
- `rw_plain_rw_rp_hole_sort` (Projection).
- `rw_plain_guard` (Projection).
- `RwPlainCallbacks` (Constructor).
- `rw_plain_callbacks_of` (Definition).
- `rw_plain_rw_rp_guard_atomic` (Definition).
- `rw_plain_strategy` (Definition).
- `rw_plain_rw_rp_strategy_run` (Definition).
- `rw_plain_fact_strategy` (Definition).
- `rw_plain_rw_rp_fact_strategy_run` (Definition).

## RewriteAuditProofApply

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_accept_atomic` (Definition).
- `rw_rp_rule_step_prepared_atomic` (Definition).
- `rw_rp_rule_step_atomic` (Definition).
- `rw_rp_apply_prepared_atomic` (Definition).
- `rw_rp_apply_atomic` (Definition).

## RewriteAuditProofCarrier

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_evidence_reason` (Inductive).
- `RWEvidenceRefl` (Constructor).
- `RWEvidenceRule` (Constructor).
- `RWEvidenceSym` (Constructor).
- `RWEvidenceTrans` (Constructor).
- `RWEvidenceCongruence` (Constructor).
- `rw_evidence_node` (Record).
- `rw_evidence_left` (Projection).
- `rw_evidence_right` (Projection).
- `rw_evidence_reason_of` (Projection).
- `rw_evidence_time` (Projection).
- `RWEvidenceNode` (Constructor).
- `rw_provenance` (Record).
- `rw_provenance_ids` (Projection).
- `rw_provenance_nodes` (Projection).
- `RWProvenance` (Constructor).
- `rw_reason_references` (Definition).
- `rw_evidence_time_le` (Definition).
- `rw_evidence_time_lt` (Definition).
- `rw_evidence_reason_valid` (Definition).
- `rw_provenance_valid` (Definition).
- `rw_provenance_sound_contract` (Definition).

Future proof module: `RewriteAuditProofCarrierAdequacy`.

- `rw_provenance_sound`: `RewriteAuditProofCarrier.rw_provenance_sound_contract`; owner AUD-RP-CORE.

## RewriteAuditProofClosure

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_append` (Fixpoint).
- `rw_rp_term_tokens` (Fixpoint).
- `rw_rp_term_key` (Definition).
- `rw_rp_fresh_loop` (Fixpoint).
- `rw_rp_proof_index` (Definition).
- `rw_rp_proof_get` (Definition).
- `rw_rp_proof_put` (Definition).
- `rw_rp_connection_state` (Record).
- `rw_rp_proof` (Projection).
- `rw_rp_index` (Projection).
- `RwRpConnectionState` (Constructor).
- `rw_rp_add_evidence` (Definition).
- `rw_rp_index_existing` (Fixpoint).
- `rw_rp_try_symmetry` (Definition).
- `rw_rp_try_transitivity` (Fixpoint).
- `rw_rp_term_key_agrees_statement` (Definition).
- `rw_rp_children_evidence` (Fixpoint).
- `rw_rp_try_congruence` (Definition).
- `rw_rp_close_pair` (Definition).
- `rw_rp_close_row` (Fixpoint).
- `rw_rp_close_pass` (Fixpoint).
- `rw_rp_close_rounds` (Fixpoint).
- `rw_rp_subterms` (Fixpoint).
- `rw_rp_nat_compare` (Fixpoint).
- `rw_rp_evidence_terms` (Fixpoint).
- `rw_rp_connect_atomic` (Definition).
- `rw_rp_generated` (Inductive).
- `RPGeneratedLeaf` (Constructor).
- `RPGeneratedRefl` (Constructor).
- `RPGeneratedSym` (Constructor).
- `RPGeneratedTrans` (Constructor).
- `RPGeneratedCongruence` (Constructor).
- `rw_rp_connect_complete_statement` (Definition).
- `rw_rp_connect_sound_statement` (Definition).

Future proof module: `RewriteAuditProofClosureAdequacy`.

- `rw_rp_term_key_agrees`: `RewriteAuditProofClosure.rw_rp_term_key_agrees_statement`; owner
  AUD-RP-CORE.
- `rw_rp_connect_complete`: `RewriteAuditProofClosure.rw_rp_connect_complete_statement`; owner
  AUD-RP-CORE.
- `rw_rp_connect_sound`: `RewriteAuditProofClosure.rw_rp_connect_sound_statement`; owner
  AUD-RP-CORE.

## RewriteAuditProofDimensions

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_reason_dimension` (Definition).
- `rw_whole_provenance_dimension` (Definition).

## RewriteAuditProofDimensions2

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_witness_dimension` (Definition).
- `rw_whole_tracked_dimension` (Definition).

## RewriteAuditProofDimensions3

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_whole_operand_dimension` (Definition).

## RewriteAuditProofFactPublic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_fact_plain` (Fixpoint).
- `rw_rp_fact_strategy_agrees` (Definition).
- `rw_rp_fact_run_valid_statement` (Definition).
- `rw_rp_fact_callback_bound_statement` (Definition).

Future proof module: `RewriteAuditProofFactPublicAdequacy`.

- `rw_rp_fact_run_valid`: `RewriteAuditProofFactPublic.rw_rp_fact_run_valid_statement`; owner
  AUD-RP-CORE.
- `rw_rp_fact_callback_bound`: `RewriteAuditProofFactPublic.rw_rp_fact_callback_bound_statement`;
  owner AUD-RP-CORE.

## RewriteAuditProofFactWholeContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_fact_control` (Fixpoint).
- `rw_whole_fact_queries` (Fixpoint).
- `rw_fact_whole_operand_dimension` (Definition).
- `rw_whole_fact_strategy_external` (Definition).
- `rw_whole_tracked_atoms` (Definition).
- `rw_fact_whole_invocation` (Record).
- `rw_fact_whole_initial_atoms` (Projection).
- `rw_fact_whole_final_atoms` (Projection).
- `rw_fact_whole_rules_external` (Projection).
- `rw_fact_whole_events_external` (Projection).
- `rw_fact_whole_strategy_external` (Projection).
- `RwFactWholeInvocation` (Constructor).
- `rw_rp_fact_whole_bound_statement` (Definition).

Future proof module: `RewriteAuditProofFactWholeContractsAdequacy`.

- `rw_rp_fact_whole_bound`: `RewriteAuditProofFactWholeContracts.rw_rp_fact_whole_bound_statement`;
  owner AUD-RP-CORE.

## RewriteAuditProofFacts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_fact_program` (Inductive).
- `RPFactReturn` (Constructor).
- `RPFactView` (Constructor).
- `RPFactLookup` (Constructor).
- `rw_rp_fact_receipt` (Inductive).
- `RPFactSnapshot` (Constructor).
- `RPFactRead` (Constructor).
- `rw_rp_fact_strategy_adapter` (Record).
- `rw_rp_fact_strategy_program` (Projection).
- `RwRpFactStrategyAdapter` (Constructor).
- `rw_rp_fact_execute` (Fixpoint).
- `rw_rp_fact_strategy_run` (Definition).
- `rw_rp_fact_run_once` (Definition).
- `rw_rp_fact_run_repeat` (Fixpoint).
- `rw_rp_fact_run_atomic` (Definition).
- `rw_rp_fact_initial_invalidation_statement` (Definition).

Future proof module: `RewriteAuditProofFactsAdequacy`.

- `rw_rp_fact_initial_invalidation` (future Theorem); owner AUD-RP-CORE.

## RewriteAuditProofInterfaceFactfulRunCallbackBoundContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_factful_run_callback_bound_contract` (Definition).

## RewriteAuditProofInterfaceFactfulRunValidContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_factful_run_valid_contract` (Definition).

## RewriteAuditProofInterfaceFactfulRunZeroContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_factful_run_zero_contract` (Definition).

## RewriteAuditProofInterfaceReprFindSpecContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_repr_find_spec_contract` (Definition).

## RewriteAuditProofInterfaceRpApplyRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_apply_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpConnectRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_connect_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpFactRunRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_fact_run_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpFactfulApplyRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_factful_apply_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpRebuildRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_rebuild_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpReprRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_repr_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpRuleStepRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_rule_step_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpRunRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_run_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpSelectedRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_selected_realizes_statement` (Definition).

## RewriteAuditProofInterfaceRpTickRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_tick_realizes_statement` (Definition).

## RewriteAuditProofInterfaceTrackedApplyProjectsContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_apply_projects_contract` (Definition).

## RewriteAuditProofInterfaceTrackedExtractableContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_extractable_contract` (Definition).

## RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_factful_apply_accept_contract` (Definition).

## RewriteAuditProofInterfaceTrackedFactfulApplyRejectContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_factful_apply_reject_contract` (Definition).

## RewriteAuditProofInterfaceTrackedPhaseValid

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_phase_valid` (Definition).

## RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_rebuild_trace_correct_contract` (Definition).

## RewriteAuditProofInterfaceTrackedRunInvariantsContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_run_invariants_contract` (Definition).

## RewriteAuditProofInterfaceTrackedSelectedContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_selected_contract` (Definition).

## RewriteAuditProofInterfaceTrackedTickCongruenceContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_tick_congruence_contract` (Definition).

## RewriteAuditProofInterfaceTrackedTickProjectionContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_tick_projection_contract` (Definition).

## RewriteAuditProofPlainContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_run_realizes_fixed_type` (Definition).
- `rw_rp_selected_realizes_fixed_type` (Definition).
- `rw_repr_find_spec_fixed_type` (Definition).
- `rw_tracked_extractable_fixed_type` (Definition).
- `rw_tracked_selected_fixed_type` (Definition).
- `rw_tracked_run_invariants_fixed_type` (Definition).
- `rw_tracked_tick_projection_fixed_type` (Definition).
- `rw_tracked_tick_congruence_fixed_type` (Definition).
- `rw_tracked_rebuild_trace_correct_fixed_type` (Definition).
- `rw_tracked_apply_projects_fixed_type` (Definition).
- `rw_tracked_factful_apply_reject_fixed_type` (Definition).
- `rw_tracked_factful_apply_accept_fixed_type` (Definition).
- `rw_factful_run_zero_fixed_type` (Definition).
- `rw_factful_run_valid_fixed_type` (Definition).
- `rw_factful_run_callback_bound_fixed_type` (Definition).
- `rw_rp_repr_realizes_fixed_type` (Definition).
- `rw_rp_connect_realizes_fixed_type` (Definition).
- `rw_rp_tick_realizes_fixed_type` (Definition).
- `rw_rp_rebuild_realizes_fixed_type` (Definition).
- `rw_rp_rule_step_realizes_fixed_type` (Definition).
- `rw_rp_apply_realizes_fixed_type` (Definition).
- `rw_rp_factful_apply_realizes_fixed_type` (Definition).
- `rw_rp_fact_run_realizes_fixed_type` (Definition).

Future proof module: `RewriteAuditProofInterfaceFactfulRunCallbackBoundContractAdequacy`.

- `rw_factful_run_callback_bound` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceFactfulRunValidContractAdequacy`.

- `rw_factful_run_valid`: `RewriteAuditProofPlainContracts.rw_factful_run_valid_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceFactfulRunZeroContractAdequacy`.

- `rw_factful_run_zero`: `RewriteAuditProofPlainContracts.rw_factful_run_zero_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceReprFindSpecContractAdequacy`.

- `rw_repr_find_spec`: `RewriteAuditProofPlainContracts.rw_repr_find_spec_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpApplyRealizesStatementAdequacy`.

- `rw_rp_apply_realizes`: `RewriteAuditProofPlainContracts.rw_rp_apply_realizes_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpConnectRealizesStatementAdequacy`.

- `rw_rp_connect_realizes`: `RewriteAuditProofPlainContracts.rw_rp_connect_realizes_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpFactRunRealizesStatementAdequacy`.

- `rw_rp_fact_run_realizes`: `RewriteAuditProofPlainContracts.rw_rp_fact_run_realizes_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpFactfulApplyRealizesStatementAdequacy`.

- `rw_rp_factful_apply_realizes` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpRebuildRealizesStatementAdequacy`.

- `rw_rp_rebuild_realizes`: `RewriteAuditProofPlainContracts.rw_rp_rebuild_realizes_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpReprRealizesStatementAdequacy`.

- `rw_rp_repr_realizes`: `RewriteAuditProofPlainContracts.rw_rp_repr_realizes_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpRuleStepRealizesStatementAdequacy`.

- `rw_rp_rule_step_realizes`: `RewriteAuditProofPlainContracts.rw_rp_rule_step_realizes_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpRunRealizesStatementAdequacy`.

- `rw_rp_run_realizes`: `RewriteAuditProofPlainContracts.rw_rp_run_realizes_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpSelectedRealizesStatementAdequacy`.

- `rw_rp_selected_realizes`: `RewriteAuditProofPlainContracts.rw_rp_selected_realizes_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceRpTickRealizesStatementAdequacy`.

- `rw_rp_tick_realizes`: `RewriteAuditProofPlainContracts.rw_rp_tick_realizes_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedApplyProjectsContractAdequacy`.

- `rw_tracked_apply_projects` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedExtractableContractAdequacy`.

- `rw_tracked_extractable`: `RewriteAuditProofPlainContracts.rw_tracked_extractable_fixed_type`;
  owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedFactfulApplyAcceptContractAdequacy`.

- `rw_tracked_factful_apply_accept` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedFactfulApplyRejectContractAdequacy`.

- `rw_tracked_factful_apply_reject` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedRebuildTraceCorrectContractAdequacy`.

- `rw_tracked_rebuild_trace_correct` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedRunInvariantsContractAdequacy`.

- `rw_tracked_run_invariants` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedSelectedContractAdequacy`.

- `rw_tracked_selected`: `RewriteAuditProofPlainContracts.rw_tracked_selected_fixed_type`; owner
  AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedTickCongruenceContractAdequacy`.

- `rw_tracked_tick_congruence` (future Theorem); owner AUD-RP-CORE.

Future proof module: `RewriteAuditProofInterfaceTrackedTickProjectionContractAdequacy`.

- `rw_tracked_tick_projection` (future Theorem); owner AUD-RP-CORE.

## RewriteAuditProofPlainPublic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_plain_repr_term_view` (Fixpoint).
- `rw_plain_repr_find_view` (Definition).
- `rw_repr_find` (Definition).
- `rw_connect_class` (Definition).
- `rw_tracked_tick` (Definition).
- `rw_tracked_rebuild` (Definition).
- `rw_tracked_rule_step` (Definition).
- `rw_tracked_run` (Definition).
- `rw_selected_explanation` (Definition).
- `rw_factful_run` (Definition).
- `rw_tracked_apply` (Definition).
- `rw_tracked_factful_apply` (Definition).

## RewriteAuditProofPublic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_run_callback_bound_statement` (Definition).
- `rw_rp_run_zero_statement` (Definition).

Future proof module: `RewriteAuditProofPublicAdequacy`.

- `rw_rp_run_callback_bound`: `RewriteAuditProofPublic.rw_rp_run_callback_bound_statement`; owner
  AUD-RP-CORE.
- `rw_rp_run_zero`: `RewriteAuditProofPublic.rw_rp_run_zero_statement`; owner AUD-RP-CORE.

## RewriteAuditProofPublicSource

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_public_source_cost_statement` (Definition).
- `rw_rp_public_selected_source_cost_statement` (Definition).
- `rw_rp_public_fact_source_cost_statement` (Definition).

Future proof module: `RewriteAuditProofPublicSourceAdequacy`.

- `rw_rp_public_source_cost`: `RewriteAuditProofPublicSource.rw_rp_public_source_cost_statement`;
  owner AUD-RP-CORE.
- `rw_rp_public_selected_source_cost` (future Theorem); owner AUD-RP-CORE.
- `rw_rp_public_fact_source_cost` (future Theorem); owner AUD-RP-CORE.

## RewriteAuditProofRealizations

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_factful_apply_atomic` (Definition).

## RewriteAuditProofRebuild

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_rebuild_done` (Definition).
- `rw_rp_rebuild_once` (Definition).
- `rw_rp_rebuild_repeat` (Fixpoint).
- `rw_rp_rebuild_atomic` (Definition).
- `rw_rp_phase_connected` (Definition).
- `rw_rp_rebuild_projects_statement` (Definition).

Future proof module: `RewriteAuditProofRebuildAdequacy`.

- `rw_rp_rebuild_projects`: `RewriteAuditProofRebuild.rw_rp_rebuild_projects_statement`; owner
  AUD-RP-CORE.

## RewriteAuditProofRepresentation

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_repr_node` (Record).
- `rw_repr_class` (Projection).
- `rw_repr_graph_node` (Projection).
- `rw_repr_term` (Projection).
- `rw_repr_children` (Projection).
- `RWReprNode` (Constructor).
- `rw_repr_witness` (Record).
- `rw_repr_root` (Projection).
- `rw_repr_ids` (Projection).
- `rw_repr_nodes` (Projection).
- `RWReprWitness` (Constructor).
- `rw_repr_node_valid` (Definition).
- `rw_repr_witness_valid` (Definition).
- `rw_rp_repr_acc` (Record).
- `rw_rp_repr_ids` (Projection).
- `rw_rp_repr_nodes` (Projection).
- `rw_rp_repr_next` (Projection).
- `RwRpReprAcc` (Constructor).
- `rw_rp_repr_emit` (Definition).
- `rw_rp_repr_term_atomic` (Fixpoint).
- `rw_rp_repr_find_atomic` (Definition).
- `rw_rp_repr_find_spec_statement` (Definition).

Future proof module: `RewriteAuditProofRepresentationAdequacy`.

- `rw_rp_repr_find_spec`: `RewriteAuditProofRepresentation.rw_rp_repr_find_spec_statement`; owner
  AUD-RP-CORE.

## RewriteAuditProofRun

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_run_state` (Record).
- `rw_rp_current` (Projection).
- `rw_rp_stopped` (Projection).
- `rw_rp_position` (Projection).
- `rw_rp_events` (Projection).
- `RwRpRunState` (Constructor).
- `rw_rp_run_once` (Definition).
- `rw_rp_run_repeat` (Fixpoint).
- `rw_tracked_output` (Record).
- `rw_tracked_final` (Projection).
- `rw_tracked_stop` (Projection).
- `rw_tracked_initial` (Projection).
- `rw_tracked_events` (Projection).
- `RwTrackedOutput` (Constructor).
- `rw_rp_run_atomic` (Definition).

## RewriteAuditProofSeed

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_seed_acc` (Record).
- `rw_rp_seed_graph` (Projection).
- `rw_rp_seed_witnesses` (Projection).
- `rw_rp_seed_next` (Projection).
- `rw_rp_seed_witness_next` (Projection).
- `RwRpSeedAcc` (Constructor).
- `rw_rp_seed_empty` (Definition).
- `rw_rp_seed_node` (Definition).
- `rw_rp_seed_term` (Fixpoint).
- `rw_rp_seed_atomic` (Definition).
- `rw_rp_seed_represents_statement` (Definition).

Future proof module: `RewriteAuditProofSeedAdequacy`.

- `rw_rp_seed_represents`: `RewriteAuditProofSeed.rw_rp_seed_represents_statement`; owner
  AUD-RP-CORE.

## RewriteAuditProofSelected

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_selected_atomic` (Definition).
- `rw_rp_run_semantic_statement` (Definition).
- `rw_rp_selected_complete_statement` (Definition).

Future proof module: `RewriteAuditProofSelectedAdequacy`.

- `rw_rp_run_semantic`: `RewriteAuditProofSelected.rw_rp_run_semantic_statement`; owner AUD-RP-CORE.
- `rw_rp_selected_complete`: `RewriteAuditProofSelected.rw_rp_selected_complete_statement`; owner
  AUD-RP-CORE.

## RewriteAuditProofSelectedContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rp_selected_bound_statement` (Definition).
- `rw_rp_repr_find_bound_statement` (Definition).

Future proof module: `RewriteAuditProofSelectedContractsAdequacy`.

- `rw_rp_selected_bound`: `RewriteAuditProofSelectedContracts.rw_rp_selected_bound_statement`; owner
  AUD-RP-CORE.
- `rw_rp_repr_find_bound`: `RewriteAuditProofSelectedContracts.rw_rp_repr_find_bound_statement`;
  owner AUD-RP-CORE.

## RewriteAuditProofSemantic

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_tracked_graph` (Definition).
- `rw_class_witnesses_valid` (Definition).
- `rw_provenance_extends` (Definition).
- `rw_provenance_rule_stable` (Definition).
- `rw_class_connected` (Definition).
- `rw_tracked_event_index_valid` (Definition).
- `rw_tracked_rule_nodes_covered` (Definition).
- `rw_tracked_stamp_fresh` (Definition).
- `rw_tracked_rebuild_trace` (Inductive).
- `RWTrackedRebuildDone` (Constructor).
- `RWTrackedRebuildStep` (Constructor).
- `rw_facts_invalidate` (Definition).
- `rw_fact_store_valid` (Definition).
- `rw_facts_invalidate_sound_contract` (Definition).
- `rw_fact_store_total` (Definition).
- `rw_fact_store_total_valid_contract` (Definition).
- `rw_fact_store_total_after_invalidate_contract` (Definition).
- `rw_fact_view` (Record).
- `rw_fact_snapshot` (Projection).
- `rw_fact_lookup` (Projection).
- `RWFactView` (Constructor).
- `rw_fact_observe` (Definition).
- `rw_fact_observe_valid_contract` (Definition).

Future proof module: `RewriteAuditProofSemanticAdequacy`.

- `rw_facts_invalidate_sound`: `RewriteAuditProofSemantic.rw_facts_invalidate_sound_contract`; owner
  AUD-RP-CORE.
- `rw_fact_store_total_valid`: `RewriteAuditProofSemantic.rw_fact_store_total_valid_contract`; owner
  AUD-RP-CORE.
- `rw_fact_store_total_after_invalidate` (future Theorem); owner AUD-RP-CORE.
- `rw_fact_observe_valid`: `RewriteAuditProofSemantic.rw_fact_observe_valid_contract`; owner
  AUD-RP-CORE.

## RewriteAuditProofTick

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_class_witness_store` (Record).
- `rw_class_witness_nodes` (Projection).
- `rw_class_witness_roots` (Projection).
- `RWClassWitnessStore` (Constructor).
- `rw_tracked_state` (Record).
- `rw_tracked_machine` (Projection).
- `rw_tracked_provenance` (Projection).
- `rw_tracked_witnesses` (Projection).
- `rw_tracked_event_nodes` (Projection).
- `RWTrackedState` (Constructor).
- `rw_rp_stamp_encode` (Definition).
- `rw_rp_stamp_work` (Definition).
- `rw_rp_stamp_put` (Definition).
- `rw_rp_witness_merge` (Definition).
- `rw_rp_witness_read` (Definition).
- `rw_rp_restate` (Definition).
- `rw_rp_connect_at_atomic` (Definition).
- `rw_rp_record_connection` (Definition).
- `rw_rp_tick_atomic` (Definition).
- `rw_rp_tick_captures_statement` (Definition).

Future proof module: `RewriteAuditProofTickAdequacy`.

- `rw_rp_tick_captures`: `RewriteAuditProofTick.rw_rp_tick_captures_statement`; owner AUD-RP-CORE.

## RewriteAuditProofWholeContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_whole_provenance_atoms` (Definition).
- `rw_whole_witness_atoms` (Definition).
- `rw_rp_whole_invocation` (Record).
- `rw_rp_whole_seed_atoms` (Projection).
- `rw_rp_whole_rules_external` (Projection).
- `rw_rp_whole_event_external` (Projection).
- `rw_rp_whole_index_atoms` (Projection).
- `rw_rp_whole_proof_atoms` (Projection).
- `rw_rp_whole_witness_atoms` (Projection).
- `rw_rp_whole_strategy_external` (Projection).
- `RwRpWholeInvocation` (Constructor).
- `rw_rp_whole_bound_statement` (Definition).

Future proof module: `RewriteAuditProofWholeContractsAdequacy`.

- `rw_rp_whole_bound`: `RewriteAuditProofWholeContracts.rw_rp_whole_bound_statement`; owner
  AUD-RP-CORE.

## RewriteAuditQueueCollections

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_insert_source` (Definition).
- `rw_rq_prepend_source` (Definition).
- `rw_rq_pop_source` (Definition).
- `rw_rq_id_member_source` (Fixpoint).
- `rw_rq_id_nodup_source` (Fixpoint).
- `rw_rq_remove_ids_source` (Fixpoint).
- `rw_rq_bucket_add_source` (Definition).
- `rw_rq_bucket_remove_source` (Definition).
- `rw_rq_table_add_source` (Definition).
- `rw_rq_table_remove_source` (Definition).
- `rw_rq_positive_encode` (Definition).
- `rw_rq_find_source` (Definition).
- `rw_rq_node_source` (Definition).
- `rw_rq_sort_source` (Definition).
- `rw_rq_canon_node_source` (Definition).
- `rw_rq_root_filter_source` (Fixpoint).
- `rw_rq_merge_source` (Definition).
- `rw_rq_union_source` (Definition).

## RewriteAuditQueueContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_external_body` (Definition).
- `rw_rq_variable_pair_external` (Definition).
- `rw_rq_operator_pair_external` (Definition).
- `rw_rq_application_pair_external` (Definition).
- `rw_rq_node_external_execution` (Definition).
- `rw_rq_receipt_external_execution` (Definition).
- `rw_rq_rebuild_source_external_statement` (Definition).
- `rw_rq_rebuild_source_complete_contract_statement` (Definition).
- `rw_rq_input_structure` (Definition).
- `rw_rq_receipt_foreign_work` (Definition).
- `rw_rq_receipt_dimension` (Definition).
- `rw_rq_run_dimension` (Definition).
- `rw_rq_run_foreign_work` (Definition).
- `rw_rq_whole_input_budget` (Definition).
- `rw_rq_source_call_count_statement` (Definition).
- `rw_rq_rebuild_input_bound_statement` (Definition).

Future proof module: `RewriteAuditQueueContractsAdequacy`.

- `rw_rq_rebuild_source_external` (future Theorem); owner AUD-RQ.
- `rw_rq_rebuild_source_complete_contract` (future Theorem); owner AUD-RQ.
- `rw_rq_source_call_count`: `RewriteAuditQueueContracts.rw_rq_source_call_count_statement`; owner
  AUD-RQ.
- `rw_rq_rebuild_input_bound`: `RewriteAuditQueueContracts.rw_rq_rebuild_input_bound_statement`;
  owner AUD-RQ.

## RewriteAuditQueueIndex

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_operator_keys_source` (Definition).
- `rw_rq_child_keys_source` (Definition).
- `rw_rq_root_keys_source` (Definition).
- `rw_rq_variable_keys_source` (Definition).
- `rw_rq_build_table_source` (Definition).
- `rw_rq_prepare_source` (Definition).
- `rw_rq_partners_source` (Definition).
- `rw_rq_initial_source` (Definition).
- `rw_rq_parent_source` (Definition).
- `rw_rq_index_update_source` (Definition).
- `rw_rq_change_keys_source` (Definition).
- `rw_rq_change_table_source` (Definition).
- `rw_rq_change_index_source` (Definition).
- `rw_rq_final_one_source` (Definition).
- `rw_rq_final_all_source` (Fixpoint).

## RewriteAuditQueueKernel

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_node_event` (Definition).
- `rw_rq_receipt` (Inductive).
- `RQSourceBlock` (Constructor).
- `RQSourceGet` (Constructor).
- `RQSourceUpdate` (Constructor).
- `RQSourceOperator` (Constructor).
- `RQSourceSort` (Constructor).
- `RQSourceVariable` (Constructor).
- `RQSourcePair` (Constructor).
- `RQSourceNode` (Constructor).
- `RQSourceDecision` (Constructor).
- `RQSourceCollapse` (Constructor).
- `RQSourceFuel` (Constructor).
- `rw_rq_receipt_work` (Definition).
- `rw_rq_receipts_work` (Definition).
- `rw_rq_source` (Record).
- `rw_rq_value` (Projection).
- `rw_rq_receipts` (Projection).
- `RwRqSource` (Constructor).
- `rw_rq_return` (Definition).
- `rw_rq_bind` (Definition).
- `rw_rq_code_get` (Definition).
- `rw_rq_map_code_get` (Definition).
- `rw_rq_code_set` (Definition).
- `rw_rq_code_remove` (Definition).
- `rw_rq_operator_encode` (Definition).
- `rw_rq_sort_encode` (Definition).
- `rw_rq_variable_encode` (Definition).
- `rw_rq_pair_encode` (Definition).
- `rw_rq_node_encode` (Definition).
- `rw_rq_decision` (Definition).
- `rw_rq_collapse_source_child` (Definition).
- `rw_rq_collapse_source` (Definition).
- `rw_rq_source_append` (Fixpoint).
- `rw_rq_source_fold_right` (Fixpoint).
- `rw_rq_source_map` (Fixpoint).
- `rw_rq_source_flat_map` (Fixpoint).
- `rw_rq_get_receipt_statement` (Definition).
- `rw_rq_pair_external` (Fixpoint).
- `rw_rq_node_external` (Definition).
- `rw_rq_receipt_budget` (Definition).
- `rw_rq_receipts_budget` (Definition).
- `rw_rq_receipt_valid` (Inductive).
- `RQValidBlock` (Constructor).
- `RQValidGet` (Constructor).
- `RQValidUpdate` (Constructor).
- `RQValidOperator` (Constructor).
- `RQValidSort` (Constructor).
- `RQValidVariable` (Constructor).
- `RQValidPair` (Constructor).
- `RQValidNode` (Constructor).
- `RQValidDecision` (Constructor).
- `RQValidCollapse` (Constructor).
- `RQValidFuel` (Constructor).
- `rw_rq_receipt_bound_statement` (Definition).
- `rw_rq_receipts_bound_statement` (Definition).

Future proof module: `RewriteAuditQueueKernelAdequacy`.

- `rw_rq_get_receipt`: `RewriteAuditQueueKernel.rw_rq_get_receipt_statement`; owner AUD-RQ.
- `rw_rq_receipt_bound`: `RewriteAuditQueueKernel.rw_rq_receipt_bound_statement`; owner AUD-RQ.
- `rw_rq_receipts_bound`: `RewriteAuditQueueKernel.rw_rq_receipts_bound_statement`; owner AUD-RQ.

## RewriteAuditQueuePositive

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_decision_frame` (Inductive).
- `RQDecBuildCase` (Constructor).
- `RQDecBuildRecursive` (Constructor).
- `RQDecClosure` (Constructor).
- `RQDecApply` (Constructor).
- `RQDecInspect` (Constructor).
- `RQDecReturn` (Constructor).
- `rw_rq_decision_build` (Fixpoint).
- `rw_rq_decision_atomic` (Definition).
- `rw_rq_decision_source_erases_statement` (Definition).
- `rw_rq_decision_build_count_statement` (Definition).
- `rw_rq_decision_source_bound_statement` (Definition).

Future proof module: `RewriteAuditQueuePositiveAdequacy`.

- `rw_rq_decision_source_erases` (future Theorem); owner AUD-RQ.
- `rw_rq_decision_build_count`: `RewriteAuditQueuePositive.rw_rq_decision_build_count_statement`;
  owner AUD-RQ.
- `rw_rq_decision_source_bound`: `RewriteAuditQueuePositive.rw_rq_decision_source_bound_statement`;
  owner AUD-RQ.

## RewriteAuditQueueRebuild

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rq_enqueue_source` (Definition).
- `rw_rq_step_source` (Definition).
- `rw_rq_repeat_source` (Fixpoint).
- `rw_rq_fuel_source` (Definition).
- `rw_rq_rebuild_source` (Definition).
- `rw_rq_rebuild_source_run` (Inductive).
- `RQRebuildSourceRun` (Constructor).
- `rw_rq_rebuild_source_erases_statement` (Definition).
- `rw_rq_rebuild_source_valid_statement` (Definition).
- `rw_rq_rebuild_source_bound_statement` (Definition).
- `rw_rq_prepend_source_linear_statement` (Definition).

Future proof module: `RewriteAuditQueueRebuildAdequacy`.

- `rw_rq_rebuild_source_erases`: `RewriteAuditQueueRebuild.rw_rq_rebuild_source_erases_statement`;
  owner AUD-RQ.
- `rw_rq_rebuild_source_valid`: `RewriteAuditQueueRebuild.rw_rq_rebuild_source_valid_statement`;
  owner AUD-RQ.
- `rw_rq_rebuild_source_bound`: `RewriteAuditQueueRebuild.rw_rq_rebuild_source_bound_statement`;
  owner AUD-RQ.
- `rw_rq_prepend_source_linear`: `RewriteAuditQueueRebuild.rw_rq_prepend_source_linear_statement`;
  owner AUD-RQ.

## RewriteAuditQueueReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_pending_queue` (Record).
- `rw_pending_sequence` (Projection).
- `rw_pending_members` (Projection).
- `RwPendingQueue` (Constructor).
- `rw_pending_pair_encoding` (Definition).
- `rw_pending_pair_key_bits` (Definition).
- `rw_pending_pair_key_bits_exact_contract` (Definition).
- `rw_pending_valid` (Definition).
- `rw_pending_empty` (Definition).
- `rw_pending_insert` (Definition).
- `rw_pending_prepend` (Definition).
- `rw_pending_pop` (Definition).
- `rw_pending_initial` (Definition).
- `rw_pending_initial_with_count` (Definition).
- `rw_queue_state` (Record).
- `rw_queue_graph` (Projection).
- `rw_queue_index` (Projection).
- `rw_queue_pending` (Projection).
- `RwQueueState` (Constructor).
- `rw_queue_project` (Definition).
- `rw_queue_step` (Definition).
- `rw_pending_rebuild` (Definition).
- `rw_pending_initial_with_count_correct_contract` (Definition).
- `rw_queue_step_agrees_contract` (Definition).
- `rw_pending_empty_valid_contract` (Definition).
- `rw_pending_insert_order_contract` (Definition).
- `rw_pending_membership_contract` (Definition).
- `rw_pending_pop_agrees_contract` (Definition).
- `rw_pending_prepend_agrees_contract` (Definition).
- `rw_pair_universe_refines_contract` (Definition).
- `rw_pending_rebuild_agrees_contract` (Definition).
- `rw_pending_charge` (Record).
- `rw_pending_probes` (Projection).
- `rw_pending_updates` (Projection).
- `rw_pending_key_steps` (Projection).
- `RwPendingCharge` (Constructor).
- `rw_pending_charge_insert` (Definition).
- `rw_pending_initial_counted` (Definition).
- `rw_pending_key_budget` (Definition).
- `rw_pending_initial_counted_correct_contract` (Definition).
- `rw_queue_insert_call` (Inductive).
- `RWQueuePairCode` (Constructor).
- `RWQueueGet` (Constructor).
- `RWQueueSet` (Constructor).
- `RWQueueRemove` (Constructor).
- `rw_queue_insert_event_cost` (Definition).
- `rw_queue_insert_model_cost` (Definition).
- `rw_queue_insert_atomic` (Definition).
- `rw_queue_encoder_adapter` (Record).
- `rw_queue_encoder_run` (Projection).
- `RwQueueEncoderAdapter` (Constructor).
- `rw_queue_encoder_adapter_laws` (Record).
- `rw_queue_encoder_agrees` (Projection).
- `rw_queue_encoder_adequate` (Projection).
- `rw_queue_pop_atomic` (Definition).
- `rw_queue_prepend_atomic` (Fixpoint).
- `rw_queue_append_atomic` (Fixpoint).
- `rw_fuel_length` (Fixpoint).
- `rw_fuel_add` (Fixpoint).
- `rw_fuel_mul` (Fixpoint).
- `rw_fuel_pos_succ` (Fixpoint).
- `rw_fuel_to_positive` (Fixpoint).
- `rw_rebuild_fuel_atomic` (Definition).
- `rw_rebuild_fuel_work` (Definition).
- `rw_node_encode_atomic` (Definition).
- `rw_node_encode_trace_cost` (Definition).
- `rw_external_encoding_events` (Definition).
- `rw_external_events_work` (Definition).
- `rw_queue_insert_trie_work` (Definition).
- `rw_queue_insert_trie_trace_work` (Definition).
- `rw_queue_insert_expanded_work` (Definition).
- `rw_queue_prepend_expanded_budget` (Definition).

Future proof module: `RewriteAuditQueueReferenceAdequacy`.

- `rw_pending_pair_key_bits_exact` (future Theorem); owner AUD-RQ.
- `rw_pending_initial_with_count_correct` (future Theorem); owner AUD-RQ.
- `rw_queue_step_agrees`: `RewriteAuditQueueReference.rw_queue_step_agrees_contract`; owner AUD-RQ.
- `rw_pending_empty_valid`: `RewriteAuditQueueReference.rw_pending_empty_valid_contract`; owner
  AUD-RQ.
- `rw_pending_insert_order`: `RewriteAuditQueueReference.rw_pending_insert_order_contract`; owner
  AUD-RQ.
- `rw_pending_membership`: `RewriteAuditQueueReference.rw_pending_membership_contract`; owner
  AUD-RQ.
- `rw_pending_pop_agrees`: `RewriteAuditQueueReference.rw_pending_pop_agrees_contract`; owner
  AUD-RQ.
- `rw_pending_prepend_agrees`: `RewriteAuditQueueReference.rw_pending_prepend_agrees_contract`;
  owner AUD-RQ.
- `rw_pair_universe_refines`: `RewriteAuditQueueReference.rw_pair_universe_refines_contract`; owner
  AUD-RQ.
- `rw_pending_rebuild_agrees`: `RewriteAuditQueueReference.rw_pending_rebuild_agrees_contract`;
  owner AUD-RQ.
- `rw_pending_initial_counted_correct` (future Theorem); owner AUD-RQ.

## RewriteAuditSharedBoundsContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_source_node` (Definition).
- `rw_rd_callback_weight` (Definition).
- `rw_rd_extract_input_weight` (Definition).
- `rw_rd_extract_budget` (Definition).
- `rw_rd_extract_bound_statement` (Definition).
- `rw_rd_extract_storage_statement` (Definition).
- `rw_rd_scalar_input_weight` (Definition).
- `rw_rd_scalar_budget` (Definition).
- `rw_rd_scalar_bound_statement` (Definition).
- `rw_rd_unary_cost_bound_statement` (Definition).

Future proof module: `RewriteAuditSharedBoundsContractsAdequacy`.

- `rw_rd_extract_bound`: `RewriteAuditSharedBoundsContracts.rw_rd_extract_bound_statement`; owner
  AUD-RD.
- `rw_rd_extract_storage`: `RewriteAuditSharedBoundsContracts.rw_rd_extract_storage_statement`;
  owner AUD-RD.
- `rw_rd_scalar_bound`: `RewriteAuditSharedBoundsContracts.rw_rd_scalar_bound_statement`; owner
  AUD-RD.
- `rw_rd_unary_cost_bound`: `RewriteAuditSharedBoundsContracts.rw_rd_unary_cost_bound_statement`;
  owner AUD-RD.

## RewriteAuditSharedCompare

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_memo` (Definition).
- `rw_rd_pair_encode` (Definition).
- `rw_rd_pair_encoding_work` (Definition).
- `rw_rd_memo_get` (Definition).
- `rw_rd_memo_set` (Definition).
- `rw_rd_node_get` (Definition).
- `rw_rd_positive_compare_cont` (Fixpoint).
- `rw_rd_headers_compare` (Fixpoint).
- `rw_rd_children` (Definition).
- `rw_rd_header` (Definition).
- `rw_rd_compare_run` (Inductive).
- `RDRootCached` (Constructor).
- `RDRootDifferent` (Constructor).
- `RDRootChildren` (Constructor).
- `RDChildrenEmpty` (Constructor).
- `RDChildrenLeftEmpty` (Constructor).
- `RDChildrenRightEmpty` (Constructor).
- `RDChildrenDifferent` (Constructor).
- `RDChildrenEqual` (Constructor).
- `rw_shared_compare_run` (Inductive).
- `RDCompareInvalid` (Constructor).
- `RDCompareValid` (Constructor).
- `rw_rd_compare_total_statement` (Definition).
- `rw_rd_compare_unique_statement` (Definition).
- `rw_rd_compare_children_run` (Inductive).

Future proof module: `RewriteAuditSharedCompareAdequacy`.

- `rw_rd_compare_total`: `RewriteAuditSharedCompare.rw_rd_compare_total_statement`; owner AUD-RD.
- `rw_rd_compare_unique`: `RewriteAuditSharedCompare.rw_rd_compare_unique_statement`; owner AUD-RD.

## RewriteAuditSharedExtract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_positive_add` (Fixpoint).
- `rw_rd_N_add` (Definition).
- `rw_rd_N_compare` (Definition).
- `rw_rd_nat_to_N` (Fixpoint).
- `rw_rd_candidate` (Record).
- `rw_rd_pointer` (Projection).
- `rw_rd_cost` (Projection).
- `rw_rd_size` (Projection).
- `RwRdCandidate` (Constructor).
- `rw_rd_store` (Record).
- `rw_rd_nodes` (Projection).
- `rw_rd_next` (Projection).
- `RwRdStore` (Constructor).
- `rw_rd_table` (Definition).
- `rw_rd_candidate_get` (Definition).
- `rw_rd_gather` (Fixpoint).
- `rw_rd_allocate` (Definition).
- `rw_rd_production` (Definition).
- `rw_rd_choose_run` (Inductive).
- `RDChooseCost` (Constructor).
- `RDChooseSize` (Constructor).
- `RDChooseCode` (Constructor).
- `rw_rd_insert_run` (Inductive).
- `RDInsertAbsent` (Constructor).
- `RDInsertPresent` (Constructor).
- `rw_rd_round_run` (Inductive).
- `RDRoundNil` (Constructor).
- `RDRoundSkip` (Constructor).
- `RDRoundInsert` (Constructor).
- `rw_rd_rounds_run` (Inductive).
- `RDRoundsOne` (Constructor).
- `RDRoundsEven` (Constructor).
- `RDRoundsOdd` (Constructor).
- `rw_shared_extract_run` (Inductive).
- `RDExtractEmpty` (Constructor).
- `RDExtractMissing` (Constructor).
- `RDExtractFound` (Constructor).
- `rw_rd_node_input_weight` (Definition).
- `rw_rd_graph_input_weight` (Definition).
- `rw_rd_compare_budget` (Definition).
- `rw_rd_compare_bound_statement` (Definition).
- `rw_rd_extract_agrees_statement` (Definition).
- `rw_rd_extract_total_statement` (Definition).
- `rw_rd_extract_unique_statement` (Definition).

Future proof module: `RewriteAuditSharedExtractAdequacy`.

- `rw_rd_compare_bound`: `RewriteAuditSharedExtract.rw_rd_compare_bound_statement`; owner AUD-RD.
- `rw_rd_extract_agrees`: `RewriteAuditSharedExtract.rw_rd_extract_agrees_statement`; owner AUD-RD.
- `rw_rd_extract_total`: `RewriteAuditSharedExtract.rw_rd_extract_total_statement`; owner AUD-RD.
- `rw_rd_extract_unique`: `RewriteAuditSharedExtract.rw_rd_extract_unique_statement`; owner AUD-RD.

## RewriteAuditSharedFixedContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_compare_realizes_fixed_type` (Definition).
- `rw_rd_extract_realizes_fixed_type` (Definition).
- `rw_rd_scalar_realizes_fixed_type` (Definition).
- `rw_shared_compare_agrees_fixed_type` (Definition).
- `rw_shared_compare_reject_fixed_type` (Definition).
- `rw_shared_extract_unfold_fixed_type` (Definition).
- `rw_shared_tree_cost_agrees_fixed_type` (Definition).
- `rw_shared_tree_cost_binary_agrees_fixed_type` (Definition).
- `rw_shared_tree_size_binary_agrees_fixed_type` (Definition).
- `rw_shared_observers_reject_fixed_type` (Definition).

Future proof module: `RewriteAuditSharedInterfaceRdCompareRealizesStatementAdequacy`.

- `rw_rd_compare_realizes` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceRdExtractRealizesStatementAdequacy`.

- `rw_rd_extract_realizes` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceRdScalarRealizesStatementAdequacy`.

- `rw_rd_scalar_realizes`: `RewriteAuditSharedFixedContracts.rw_rd_scalar_realizes_fixed_type`;
  owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedCompareAgreesContractAdequacy`.

- `rw_shared_compare_agrees` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedCompareRejectContractAdequacy`.

- `rw_shared_compare_reject` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedExtractUnfoldContractAdequacy`.

- `rw_shared_extract_unfold` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedObserversRejectContractAdequacy`.

- `rw_shared_observers_reject` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedTreeCostAgreesContractAdequacy`.

- `rw_shared_tree_cost_agrees` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContractAdequacy`.

- `rw_shared_tree_cost_binary_agrees` (future Theorem); owner AUD-RD.

Future proof module: `RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContractAdequacy`.

- `rw_shared_tree_size_binary_agrees` (future Theorem); owner AUD-RD.

## RewriteAuditSharedInterfaceRdCompareRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_compare_realizes_statement` (Definition).

## RewriteAuditSharedInterfaceRdExtractRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_extract_realizes_statement` (Definition).

## RewriteAuditSharedInterfaceRdScalarRealizesStatement

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_scalar_realizes_statement` (Definition).

## RewriteAuditSharedInterfaceSharedCompareAgreesContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_compare_agrees_contract` (Definition).

## RewriteAuditSharedInterfaceSharedCompareRejectContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_compare_reject_contract` (Definition).

## RewriteAuditSharedInterfaceSharedExtractUnfoldContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_extract_unfold_contract` (Definition).

## RewriteAuditSharedInterfaceSharedObserversRejectContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_observers_reject_contract` (Definition).

## RewriteAuditSharedInterfaceSharedTreeCostAgreesContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_tree_cost_agrees_contract` (Definition).

## RewriteAuditSharedInterfaceSharedTreeCostBinaryAgreesContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_tree_cost_binary_agrees_contract` (Definition).

## RewriteAuditSharedInterfaceSharedTreeSizeBinaryAgreesContract

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_tree_size_binary_agrees_contract` (Definition).

## RewriteAuditSharedObservers

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_shared_gather` (Fixpoint).
- `rw_rd_scalar_node` (Definition).
- `rw_rd_scalar_pass` (Fixpoint).
- `rw_rd_scalar_rounds` (Fixpoint).
- `rw_rd_scalar_observe` (Definition).
- `rw_rd_positive_to_nat` (Fixpoint).
- `rw_rd_N_to_nat` (Definition).
- `rw_shared_tree_cost_binary_atomic` (Definition).
- `rw_shared_tree_size_binary_atomic` (Definition).
- `rw_shared_tree_cost_atomic` (Definition).
- `rw_rd_scalar_agrees_statement` (Definition).
- `rw_rd_scalar_reject_statement` (Definition).

Future proof module: `RewriteAuditSharedObserversAdequacy`.

- `rw_rd_scalar_agrees`: `RewriteAuditSharedObservers.rw_rd_scalar_agrees_statement`; owner AUD-RD.
- `rw_rd_scalar_reject`: `RewriteAuditSharedObservers.rw_rd_scalar_reject_statement`; owner AUD-RD.

## RewriteAuditSharedPlain

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rd_plain_pos_succ` (Fixpoint).
- `rd_plain_nat_positive` (Fixpoint).
- `rd_plain_pos_add` (Fixpoint).
- `rd_plain_N_add` (Definition).
- `rd_plain_nat_N` (Fixpoint).
- `rd_plain_pos_nat` (Fixpoint).
- `rd_plain_N_nat` (Definition).
- `rd_plain_pos_compare` (Fixpoint).
- `rd_plain_N_compare` (Definition).
- `rd_plain_headers_compare` (Fixpoint).
- `rd_plain_header` (Definition).
- `rd_plain_compare_call` (Inductive).
- `RDPlainRoot` (Constructor).
- `RDPlainChildren` (Constructor).
- `rd_plain_compare_descend` (Inductive).
- `RDPlainDescendChildren` (Constructor).
- `RDPlainDescendHead` (Constructor).
- `RDPlainDescendTail` (Constructor).
- `rw_rd_plain_compare_well_founded_type` (Definition).
- `rd_plain_compare_body` (Definition).
- `rd_plain_compare_execute` (Definition).
- `rw_shared_compare_builder` (Definition).
- `rd_plain_candidate_get` (Definition).
- `rd_plain_gather` (Fixpoint).
- `rd_plain_allocate` (Definition).
- `rd_plain_production` (Definition).
- `rd_plain_choose` (Definition).
- `rd_plain_insert` (Definition).
- `rd_plain_round` (Fixpoint).
- `rd_plain_rounds` (Fixpoint).
- `rw_shared_extract_builder` (Definition).
- `rd_plain_shared_gather` (Fixpoint).
- `rd_plain_scalar_node` (Definition).
- `rd_plain_scalar_pass` (Fixpoint).
- `rd_plain_scalar_rounds` (Fixpoint).
- `rd_plain_scalar_observe` (Definition).
- `rw_shared_tree_cost_binary` (Definition).
- `rw_shared_tree_size_binary` (Definition).
- `rw_shared_tree_cost` (Definition).

Future proof module: `RewriteAuditSharedPlainAdequacy`.

- `rw_rd_plain_compare_well_founded` (future Theorem); owner AUD-RD.

## RewriteAuditSharedPlainContracts

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_rd_plain_compare_realizes_type` (Definition).
- `rw_rd_plain_extract_realizes_type` (Definition).
- `rw_rd_plain_scalar_realizes_type` (Definition).
- `rw_rd_plain_compare_agrees_type` (Definition).
- `rw_rd_plain_compare_reject_type` (Definition).
- `rw_rd_plain_extract_unfold_type` (Definition).
- `rw_rd_plain_tree_cost_agrees_type` (Definition).
- `rw_rd_plain_tree_cost_binary_agrees_type` (Definition).
- `rw_rd_plain_tree_size_binary_agrees_type` (Definition).
- `rw_rd_plain_observers_reject_type` (Definition).
- `rw_rd_plain_compare_source_erases_type` (Definition).
- `rw_rd_plain_extract_source_erases_type` (Definition).
- `rw_rd_plain_production_source_erases_type` (Definition).

Future proof module: `RewriteAuditSharedPlainAdequacy`.

- `rw_rd_plain_compare_source_erases` (future Theorem); owner AUD-RD.
- `rw_rd_plain_extract_source_erases` (future Theorem); owner AUD-RD.
- `rw_rd_plain_production_source_erases` (future Theorem); owner AUD-RD.

## RewriteAuditSharedReference

Public package: `Galois.Rewrite`.

Card: AUD-RW-MODELS

- `rw_shared_node` (Inductive).
- `RWSharedVar` (Constructor).
- `RWSharedApp` (Constructor).
- `rw_shared_tree` (Record).
- `rw_shared_root` (Projection).
- `rw_shared_nodes` (Projection).
- `RwSharedTree` (Constructor).
- `rw_shared_wf` (Definition).
- `rw_shared_validation_call` (Inductive).
- `RWSharedEnumerate` (Constructor).
- `RWSharedKeyCheck` (Constructor).
- `RWSharedRootRead` (Constructor).
- `RWSharedLength` (Constructor).
- `RWSharedReadyRead` (Constructor).
- `RWSharedReadyAdd` (Constructor).
- `rw_shared_validation_event_cost` (Definition).
- `rw_shared_validation_trace_cost` (Definition).
- `rw_shared_length_atomic` (Fixpoint).
- `rw_shared_children_ready` (Fixpoint).
- `rw_shared_validation_pass` (Fixpoint).
- `rw_shared_validation_rounds` (Fixpoint).
- `rw_shared_validation_keys` (Fixpoint).
- `rw_shared_validation_all_ready` (Fixpoint).
- `rw_shared_validate_atomic` (Definition).
- `rw_shared_children_ready_value` (Fixpoint).
- `rw_shared_validation_pass_value` (Fixpoint).
- `rw_shared_validation_rounds_value` (Fixpoint).
- `rw_shared_validation_keys_value` (Fixpoint).
- `rw_shared_validation_all_ready_value` (Fixpoint).
- `rw_shared_validate` (Definition).
- `rw_shared_children_bits` (Fixpoint).
- `rw_shared_validate_spec_contract` (Definition).
- `rw_shared_validate_atomic_erases_contract` (Definition).
- `rw_shared_unfold_call` (Inductive).
- `RWUnfoldValidate` (Constructor).
- `RWUnfoldEnumerate` (Constructor).
- `RWUnfoldLength` (Constructor).
- `RWUnfoldRead` (Constructor).
- `rw_shared_unfold_event_cost` (Definition).
- `rw_shared_unfold_trace_cost` (Definition).
- `rw_shared_unfold_fuel_atomic` (Fixpoint).
- `rw_shared_unfold_atomic` (Definition).
- `rw_shared_unfold_fuel_value` (Fixpoint).
- `rw_shared_unfold` (Definition).
- `rw_shared_unfold_total_statement` (Definition).
- `rw_shared_unfold_valid_statement` (Definition).
- `rw_shared_unfold_erases_statement` (Definition).
- `rw_shared_unfold_total_contract` (Definition).
- `rw_shared_unfold_valid_contract` (Definition).
- `rw_shared_unfold_atomic_erases_contract` (Definition).

Future proof module: `RewriteAuditSharedReferenceAdequacy`.

- `rw_shared_validate_spec`: `RewriteAuditSharedReference.rw_shared_validate_spec_contract`; owner
  AUD-RD.
- `rw_shared_validate_atomic_erases` (future Theorem); owner AUD-RD.
- `rw_shared_unfold_erases`: `RewriteAuditSharedReference.rw_shared_unfold_erases_statement`; owner
  AUD-RD.
- `rw_shared_unfold_total`: `RewriteAuditSharedReference.rw_shared_unfold_total_contract`; owner
  AUD-RD.
- `rw_shared_unfold_valid`: `RewriteAuditSharedReference.rw_shared_unfold_valid_contract`; owner
  AUD-RD.
- `rw_shared_unfold_atomic_erases` (future Theorem); owner AUD-RD.

<!-- AUD-API-RW-NAMES-END -->


<!-- AUD-API-RW-INSTALL-NAMES-BEGIN -->

# Fixed public producer installation names

## AnalysesAuditRewriteFacadePlainAdequacy

Public package: `Galois.Analyses`.

- `rw_legacy_tracked` (future Definition); owner AUD-RP-FACADE.
- `rw_legacy_selected_explanation` (future Definition); owner AUD-RP-FACADE.
- `rw_tracked_optimise` (future Definition); owner AUD-RP-FACADE.

## RewriteAuditSharedPlainAdequacy

Public package: `Galois.Rewrite`.

- `rw_shared_compare` (future Definition); owner AUD-RD.
- `rw_shared_extract` (future Definition); owner AUD-RD.

<!-- AUD-API-RW-INSTALL-NAMES-END -->

<!-- AUD-API-RW-TESTS-NAMES-BEGIN -->

# Rewrite finite test names

## AnalysesAuditRewriteFacadeExamples

Test package: `Galois.Tests.Analyses`.

Card: AUD-RP-FACADE

- `rw_facade_guard_action_cost` (Definition).
- `rw_facade_guard_actions_cost` (Definition).
- `rw_facade_fixture_op` (Definition).
- `rw_facade_fixture_guard` (Definition).
- `rw_facade_fixture_nested_guard_rule` (Definition).
- `rw_facade_fixture_nested_guard` (Definition).
- `rw_facade_source_example_rule` (Definition).
- `rw_facade_checker_source_fixture` (Example).
- `rw_facade_nested_source_fixture` (Example).

## AnalysesAuditRewriteFacadePlainMaterializerExamples

Test package: `Galois.Tests.Analyses`.

Card: AUD-RP-FACADE

- `facade_plain_fixture_bindings` (Definition).
- `facade_plain_fixture_rule` (Definition).
- `facade_plain_fixture_sym` (Definition).
- `facade_plain_fixture_congruence` (Definition).
- `facade_plain_fixture` (Definition).
- `facade_plain_rule_accessible` (Definition).
- `facade_plain_sym_accessible` (Definition).
- `facade_plain_children_accessible` (Definition).
- `facade_plain_congruence_accessible` (Definition).
- `facade_plain_full_shape_closed` (Example).
- `facade_plain_recursive_replay_closed` (Example).
- `facade_plain_reverse_order_closed` (Example).
- `facade_plain_cycle` (Definition).
- `facade_plain_cycle_rejected_closed` (Example).
- `facade_plain_unreachable_cycle` (Definition).
- `facade_plain_unreachable_cycle_rejected_closed` (Example).
- `facade_plain_bad_stored_key` (Definition).
- `facade_plain_bad_key_rejected_closed` (Example).

## RewriteAuditIndexExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RI

- `rw_index_congruence_fixture` (Definition).
- `rw_ri_fixture_adapter` (Definition).
- `rw_ri_rebuild_source_nonempty_statement` (Definition).
- `rw_ri_pair_first_missing_fixture` (Example).
- `rw_ri_rebuild_source_fixture` (Example).

## RewriteAuditPlainExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RP-CORE

- `rw_plain_fixture_signature` (Definition).
- `rw_plain_seed_same_source_fixture` (Example).
- `rw_plain_accepted_same_source_fixture` (Example).
- `rw_plain_stopped_run_same_source_fixture` (Example).
- `rw_plain_representation_same_source_fixture` (Example).

## RewriteAuditProofExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RP-CORE

- `rw_rp_seed_nonempty_fixture` (Example).
- `rw_rp_fixture_rule` (Definition).
- `rw_rp_fixture_callbacks` (Definition).
- `rw_rp_fixture_attempt` (Definition).
- `rw_rp_accepted_source_fixture` (Example).

## RewriteAuditQueueExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RQ

- `rw_rebuild_fixture_adapter` (Definition).
- `rw_rebuild_fixture_graph` (Definition).
- `rw_rq_decision_first_mismatch_fixture` (Example).
- `rw_rq_source_nonempty_fixture` (Example).

## RewriteAuditSharedExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RD

- `rw_shared_validation_fixture_nodes` (Definition).
- `rw_shared_fan_fixture_nodes` (Definition).
- `rw_shared_fan_fixture` (Definition).
- `rw_rd_extract_nonempty_statement` (Definition).
- `rw_rd_scalar_fan_fixture` (Example).
- `rw_rd_extract_source_fixture` (Example).

## RewriteAuditSharedPlainExamples

Test package: `Galois.Tests.Rewrite`.

Card: AUD-RD

- `rd_plain_variable_nodes` (Definition).
- `rd_plain_fan_nodes` (Definition).
- `rd_plain_fan` (Definition).
- `rd_plain_repeated_tree_objective_closed` (Example).
- `rd_plain_unreachable_cycle` (Definition).
- `rd_plain_unreachable_cycle_rejected_closed` (Example).
- `rd_plain_bad_stored_key` (Definition).
- `rd_plain_stored_key_rejected_closed` (Example).
- `rd_plain_variable_accessible` (Definition).
- `rd_plain_comparator_recursive_kernel_closed` (Example).
- `rd_plain_comparator_order_kernel_closed` (Example).
- `rd_plain_variable_graph` (Definition).
- `rd_plain_real_backpointer_allocation_closed` (Example).

<!-- AUD-API-RW-TESTS-NAMES-END -->

## AnalysesAuditMemoryPhiOperandQuery

Public package: `Galois.Analyses`.

Public module: `Galois.Analyses.AnalysesAuditMemoryPhiOperandQuery`.

Card: PHI-OUTPUT-MODEL

- `audit_phi_operand_code_mem` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_guard_frames` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_event` (Inductive);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_output_operand_call` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_source_work` (Fixpoint);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_direct_work` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_input_budget` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_output_operand_erases_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_trace_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_source_adequate_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_whole_input_bound_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_version_sources` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_callbacks` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_adapted_source_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_output_index` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_saved_query` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_saved_index_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_output_saved_query_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_producer_saved_query_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_public_source_bridge_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_saved_queries_bound_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `audit_phi_operand_query_contract_statement` (Definition);
  [canonical API](analyses.md#phi-operand-query-contract).
- `AuditPhiOperandProbe` (constructor);
  [canonical API](analyses.md#phi-operand-query-contract).
- `AuditPhiOperandBody` (constructor);
  [canonical API](analyses.md#phi-operand-query-contract).
- `AuditPhiOperandAbsent` (constructor);
  [canonical API](analyses.md#phi-operand-query-contract).

Future proof module: `Galois.Analyses.AnalysesAuditMemoryPhiOperandQueryAdequacy`.

- `audit_phi_output_operand_erases` (future Theorem);
  type `audit_phi_output_operand_erases_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.
- `audit_phi_operand_query_trace` (future Theorem);
  type `audit_phi_operand_query_trace_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.
- `audit_phi_operand_query_source_adequate` (future Theorem);
  type `audit_phi_operand_query_source_adequate_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.
- `audit_phi_operand_query_whole_input_bound` (future Theorem);
  type `audit_phi_operand_query_whole_input_bound_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.
- `audit_phi_operand_query_adapted_source` (future Theorem);
  type `audit_phi_operand_query_adapted_source_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.
- `audit_phi_operand_saved_queries_bound` (future Theorem);
  type `audit_phi_operand_saved_queries_bound_statement`;
  [canonical API](analyses.md#phi-operand-query-adequacy); owner PHI-OUTPUT-QUERY-PROOF.

Future proof module: `Galois.Analyses.AnalysesAuditMemoryPhiOperandQuerySourceAdequacy`.

- `audit_phi_operand_saved_index` (future Theorem);
  type `audit_phi_operand_saved_index_statement`;
  [canonical API](analyses.md#phi-operand-query-source-adequacy); owner PHI-OUTPUT-SOURCE-PROOF.
- `audit_phi_operand_output_saved_query` (future Theorem);
  type `audit_phi_operand_output_saved_query_statement`;
  [canonical API](analyses.md#phi-operand-query-source-adequacy); owner PHI-OUTPUT-SOURCE-PROOF.
- `audit_phi_operand_producer_saved_query` (future Theorem);
  type `audit_phi_operand_producer_saved_query_statement`;
  [canonical API](analyses.md#phi-operand-query-source-adequacy); owner PHI-OUTPUT-SOURCE-PROOF.
- `audit_phi_operand_public_source_bridge` (future Theorem);
  type `audit_phi_operand_public_source_bridge_statement`;
  [canonical API](analyses.md#phi-operand-query-source-adequacy); owner PHI-OUTPUT-SOURCE-PROOF.
- `audit_phi_operand_query_contract` (future Theorem);
  type `audit_phi_operand_query_contract_statement`;
  [canonical API](analyses.md#phi-operand-query-source-adequacy); owner PHI-OUTPUT-SOURCE-PROOF.
