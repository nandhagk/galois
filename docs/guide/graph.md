# Graph

Graph supplies costed graph callbacks, interned adjacency and mathematical contracts for later
algorithms. A client builds a [`Graph.t`](../../theories/Graph/GraphModel.v#L15) from its node and
edge types. The fields `out_c`, `source_c` and `target_c` return `Cost.t` values.
The pure accessors observe those values. `Graph.of_pure` charges one tick per primitive call.
Use costed callbacks when a call traverses client data.

The separate predicate `graph_wf` requires distinct nodes, listed entries, correctly sourced
edges and target closure. Readiness also requires duplicate-free outgoing edge lists.
Entries may repeat and several entries are allowed. `reachable_iff_path` relates inductive
reachability to edge-list paths. An empty path includes its starting node.
`dominates` quantifies over paths from every entry, so adding an entry can remove dominance.

## Prepare once

[`Prepared.prepare`](../../theories/Graph/GraphPrepared.v#L104) interns the listed nodes in
first-occurrence order and builds both adjacency indexes. Each successor stores an edge and
its target ID. Each predecessor stores an edge and its source ID.
The indexes are `Map.t positive (list (E * positive))`.
The prepared record carries its node encoding so `id_of` always uses the table's dictionary.
`id_of` and `name_of` return `None` for missing names and IDs.
Absent-ID adjacency is empty.

`Prepared.prepare_ready` requires `encoding_laws enc`, `graph_wf g` and duplicate-free outgoing
lists. Its result proves the graph domain, inverse observations, adjacency, map invariants and
fuel formula. Dense IDs are precisely the positive IDs below `Intern.next (Prepared.names p)`.
No encoding law or graph proof is needed to compute a prepared value.
The laws do not treat an arbitrary encoding dictionary as injective.

The formula for `Pos.to_nat (Prepared.fuel p)` is `2 * n + m + 2`, where `n` is the length of the
node list and `m` is `edge_count` of the source graph.
<!-- Source: GraphPrepared.v, Prepared.laws.fuel_value. -->
`Prepared.reverse p exits` swaps indexes, retains names and fuel, and reverses endpoint
callbacks. Its readiness theorem requires every exit ID to denote a graph node.
Duplicate exits are permitted.

Preparation is a pure reference computation. It has no runtime or asymptotic cost claim.
`GRAPH-SEARCH` adds `GraphPreparedCost.prepare_c`, its value equation to this reference and a
proved cost bound. Public preparation equations expose the reference construction through
public Base operations. Consumers use those equations and semantic laws without unfolding
Map, Intern or Cost implementations. Reversed adjacency callbacks retain lookup and list
projection costs. The mathematical deletion view also has costed outgoing filtering.

## Results and visitors

[`Scope.t`](../../theories/Graph/GraphVisitor.v#L14) excludes blocked IDs and optionally restricts
search to a set. Visitors receive entry, edge and exit events. Entry events carry an optional
tree edge and source. `Visitor.pair` keeps independent product state and retains both charges.
`Visitor.apply_c` includes its event-dispatch tick.
`Visitor.amortised` states `ticks + Phi after <= k + Phi before` over every event and state.
The additive form avoids truncated subtraction.

The result contracts describe source-graph properties through prepared IDs.
Each algorithm card must prove its output meets the corresponding contract.

| Vocabulary | Producer card |
| --- | --- |
| `Search.result`, `Search.exact`, `Search.classify` | `GRAPH-SEARCH` |
| `Scc.result`, `Scc.exact`, `Condensation.t`, `Condensation.exact` | `GRAPH-SCC` |
| `Hier.tree`, `Hier.forest`, `Hier.exact`, `Wto.valid`, `Loops.exact`, `reducible` | `GRAPH-HIERARCHY` |
| `Dom.tree`, `Dom.exact`, dominance and post-dominance | `GRAPH-DOM` |
| `in_df`, `in_idf`, `control_dependent`, `edge_dominates` | `GRAPH-FRONTIER` |
| `Weight.t`, `Dag.outcome`, `Dag.cyclic_witness`, `Chain.outcome`, `Chain.spec` | `GRAPH-PATHS` |
| `Interference.t`, `Colour.problem`, `Colour.result`, `Colour.proper` | `GRAPH-COLOUR` |

`Wto.of_forest` flattens a hierarchy and has a proved balance theorem.
An empty-body component emits an opening and closing token, so it represents a self-loop.
`Condensation.count` is a natural number because an empty graph has no components.
`Chain.ForwardingCycle` carries prefix and cycle data.
Its separate spec requires that the cycle is nonempty and reachable by forwarding.
Running a computation never requires a cycle proof.
`Wto.valid_within` describes scoped hierarchy projections.
`Wto.valid` specializes that contract to an unrestricted outer run.
`Search.classify r u v` classifies endpoint relations.
Parallel edge events must distinguish the actual recorded tree edge separately.

`GRAPH-CHECK` adds the reference reachability closure, the immediate-dominator checker and the
weak-order checker. These checkers let other packages certify hand-written results before the
algorithm cards land. This card proves no later producer's exactness.

The [fixtures](../../tests/Graph/GraphPreparedTest.v#L20) compute diamond, self-loop, multiple-entry,
empty and absent-ID observations. Other Graph tests check visitor state and ticks, hierarchy
flattening, edge classes and the dominance fact invalidated by a second entry.
