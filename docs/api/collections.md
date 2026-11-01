# Galois.Collections

## Dense finite-universe set backend (COL-3)

`CollectionsDenseSet.v` defines a separate set carrier for a fixed finite universe; it does not
change `FinSet.t` or C4. Its bitset is a nonnegative `N`, and its operations ignore all bits at
positions at or above the universe length. `universe` has no duplicate keys. Index lookup is built
once as a `Map.t K N` and retains the exact positions in `universe`; no operation scans `universe`
except conversion to a list or `FinSet` and initial index construction. All operations take the
same prepared universe and reject keys outside it by leaving the set unchanged.

```coq
Record dense_universe (K : Type) : Type := DenseUniverse {
  dense_keys : list K;
  dense_index : Map.t K N;
  dense_length : N
}.
Definition dense_universe_wf {K} (E : encoding K) (u : dense_universe K) : Prop :=
  NoDup (dense_keys u) /\ Map.wf E (dense_index u) /\
  dense_length u = N.of_nat (List.length (dense_keys u)) /\
  (forall k i, Map.get E k (dense_index u) = Some i <->
    nth_error (dense_keys u) (N.to_nat i) = Some k).
Definition dense_prepare {K} (E : encoding K) (keys : list K) : dense_universe K.
(* Keep the first occurrence of each key, in input order; construct dense_index and
   dense_length once. *)
Definition dense_set := N.
Definition dense_empty : dense_set := 0%N.
Definition dense_mem {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) : bool.
Definition dense_add {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) :
  dense_set.
Definition dense_remove {K} (E : encoding K) (u : dense_universe K) (k : K) (s : dense_set) :
  dense_set.
Definition dense_union {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_inter {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_diff {K} (u : dense_universe K) (a b : dense_set) : dense_set.
Definition dense_subset {K} (u : dense_universe K) (a b : dense_set) : bool.
Definition dense_to_finset {K} (E : encoding K) (u : dense_universe K) (s : dense_set) : FinSet.t K.
Definition dense_of_finset {K} (E : encoding K) (u : dense_universe K) (s : FinSet.t K) : dense_set.
(* Bit i corresponds to nth_error (dense_keys u) i. Binary operations first mask to the cached
   dense_length; dense_to_finset enumerates dense_keys in order, retaining precisely its set bits.
   The length cache agrees with the keys when dense_universe_wf holds. *)

Theorem dense_prepare_wf {K} (E : encoding K) (keys : list K) :
  dense_universe_wf E (dense_prepare E keys).
Theorem dense_mem_refines {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k : K) :
  dense_universe_wf E u ->
  dense_mem E u k s = FinSet.mem E k (dense_to_finset E u s).
Theorem dense_roundtrip {K} (E : encoding K) (u : dense_universe K) (s : FinSet.t K) (k : K) :
  dense_universe_wf E u -> FinSet.wf E s ->
  dense_mem E u k (dense_of_finset E u s) =
    (FinSet.mem E k s && existsb (fun x => Pos.eqb (encode E x) (encode E k)) (dense_keys u)).
Theorem dense_union_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_union u a b) =
    (dense_mem E u k a || dense_mem E u k b).
Theorem dense_inter_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_inter u a b) =
    (dense_mem E u k a && dense_mem E u k b).
Theorem dense_diff_mem {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) (k : K) :
  dense_universe_wf E u -> dense_mem E u k (dense_diff u a b) =
    (dense_mem E u k a && negb (dense_mem E u k b)).
Theorem dense_subset_spec {K} (E : encoding K) (u : dense_universe K) (a b : dense_set) :
  dense_universe_wf E u ->
  (dense_subset u a b = true <-> forall k, dense_mem E u k a = true -> dense_mem E u k b = true).
Theorem dense_add_mem {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_add E u k s) =
    (dense_mem E u x s ||
      (Pos.eqb (encode E x) (encode E k) &&
       existsb (fun y => Pos.eqb (encode E y) (encode E k)) (dense_keys u))).
Theorem dense_remove_mem {K} (E : encoding K) (u : dense_universe K) (s : dense_set) (k x : K) :
  dense_universe_wf E u -> dense_mem E u x (dense_remove E u k s) =
    (dense_mem E u x s && negb (Pos.eqb (encode E x) (encode E k))).
```

The bounds on the bitset operations count arbitrary-precision bit operations, not machine-word
O(1). Dense sets and FinSet have the same membership for keys in the prepared universe; they do
not promise the same enumeration order. Card: COL-3.

Collections provides the data structures every other package builds on: encodings that turn any
key type into `positive`, canonical binary tries, maps and sets over encodable keys, a priority
queue, a persistent union-find, and tables keyed by lists of numbers. A client never sees a trie;
it passes an `encoding K` to each map operation. For example, with `E := pair_encoding
positive_encoding positive_encoding`:

```coq
Definition m : Map.t (positive * positive) nat := Map.set E (1%positive, 2%positive) 7 Map.empty.
(* Map.get E (1%positive, 2%positive) m = Some 7  and  Map.get E (2%positive, 1%positive) m = None *)
```

Conventions of this document. A theorem written `Theorem M.name` is declared as `name` inside
`Module M`. Statements sit in `Section`s that declare the variables they mention. Record
projections take their parameters implicitly (`Arguments encode {K}`). Stdlib imports
(`ZArith`, `List`, `Bool`, `Sorting.Sorted`, `Relations.Relation_Definitions`,
`Relations.Relation_Operators`) are implicit. The set module is `FinSet`, because `Set` is a Rocq
keyword. A law holds for every trie, well formed or not, unless its statement says `wf`. The
position-level API (`Map.code_get` and its laws, `FinSet.subset_code`) states what holds position
by position, so that Order proves its lattice laws for every trie without a `wf` premise.

## Files

| File | Contents | Card |
|---|---|---|
| `CollectionsEncoding.v` | `encoding`, the ten provided encodings, their codes | COL-1a |
| `CollectionsTrie.v` | `Trie`: canonical binary tries, traversal and extensionality | COL-1b |
| `CollectionsMap.v` | `Map`: maps, well-formedness, position API and equality | COL-1c |
| `CollectionsFinSet.v` | `FinSet`: sets, set algebra and size lemmas | COL-1c |
| `CollectionsHeap.v` | `PQueue`: min-priority queue with membership | COL-2 |
| `CollectionsUnionFind.v` | `UnionFind`: persistent union-find, rank, path compression | COL-2 |
| `CollectionsTable.v` | `Table`: maps keyed by `list positive`, as a flat `Map` | COL-2 |
| `CollectionsDenseSet.v` | Prepared finite universes and packed set refinement | COL-3 |

## Definitions

### Encodings (`CollectionsEncoding.v`)

```coq
Record encoding (K : Type) : Type := Encoding {
  encode : K -> positive;
  encode_injective : forall x y, encode x = encode y -> x = y
}.
Definition positive_encoding : encoding positive.   (* encode p = p *)
Definition N_encoding : encoding N.                 (* encode n = N.succ_pos n *)
Definition nat_encoding : encoding nat.             (* encode n = Pos.of_succ_nat n *)
Definition Z_encoding : encoding Z.                 (* 0 -> 1, Zpos p -> p~0, Zneg p -> p~1 *)
Definition bool_encoding : encoding bool.           (* false -> 1, true -> 2 *)
Definition unit_encoding : encoding unit.           (* tt -> 1 *)
Definition option_encoding {A} (EA : encoding A) : encoding (option A).
(* None -> 1, Some a -> (encode a)~0 *)
Definition sum_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A + B).
(* inl a -> (encode a)~0, inr b -> (encode b)~1 *)
Definition pair_encoding {A B} (EA : encoding A) (EB : encoding B) : encoding (A * B).
Definition list_encoding {A} (EA : encoding A) : encoding (list A).
```

The codes of `positive`, `N`, `nat`, `Z`, `bool`, `unit`, `option` and `sum` are exactly those
shown, so that element order is predictable. `pair_encoding` and `list_encoding` fix only
injectivity. Build both through `list bool`: write each code's bits below its leading 1, doubling
each bit (`0` as `00`, `1` as `11`) and ending each code with `01`. Concatenate the two encoded
codes for a pair or the encoded codes of all list elements, then convert the complete bit list to
`positive` once, with a leading 1. Use accumulators or another linear construction, so encoding
takes time linear in the total number of emitted bits. Card: COL-1a. COL-1a also removes the
temporary `(allow_empty)` from `dune-project`. COL-1c depends on COL-1a and COL-1b.

### Tries (`CollectionsTrie.v`)

A trie is canonical by construction: there is no representation of an empty subtree, so two tries
with the same bindings are equal. Suggested representation (internal; clients never match on it):

```coq
Inductive ne (A : Type) : Type :=              (* non-empty trees: 7 shapes *)
  | N001 (r : ne A) | N010 (v : A) | N011 (v : A) (r : ne A)
  | N100 (l : ne A) | N101 (l r : ne A) | N110 (l : ne A) (v : A) | N111 (l : ne A) (v : A) (r : ne A).
Inductive t (A : Type) : Type := Empty | Nodes (n : ne A).
```

A key is read least-significant bit first: `xH` is the root, `xO p` goes left, `xI p` goes right.

```coq
Definition Trie.empty {A} : Trie.t A.
Definition Trie.is_empty {A} (t : Trie.t A) : bool.
Definition Trie.get {A} (p : positive) (t : Trie.t A) : option A.
Definition Trie.set {A} (p : positive) (v : A) (t : Trie.t A) : Trie.t A.
Definition Trie.remove {A} (p : positive) (t : Trie.t A) : Trie.t A.
Definition Trie.map {A B} (f : A -> B) (t : Trie.t A) : Trie.t B.
Definition Trie.combine {A B C} (f : option A -> option B -> option C)
  (t1 : Trie.t A) (t2 : Trie.t B) : Trie.t C.    (* pointwise when f None None = None *)
Definition Trie.fold {A B} (f : B -> positive -> A -> B) (t : Trie.t A) (b : B) : B.
Definition Trie.elements {A} (t : Trie.t A) : list (positive * A).
Definition Trie.size {A} (t : Trie.t A) : nat.
Definition Trie.beq {A} (eqb : A -> A -> bool) (t1 t2 : Trie.t A) : bool.
Definition Trie.forall2 {A B} (r : A -> option B -> bool) (t1 : Trie.t A) (t2 : Trie.t B) : bool.
Definition Trie.union_opt {A} (f : A -> A -> A) (a b : option A) : option A :=
  match a, b with
  | Some x, Some y => Some (f x y) | Some x, None => Some x
  | None, Some y => Some y | None, None => None
  end.
Definition Trie.union_with {A} (f : A -> A -> A) (t1 t2 : Trie.t A) : Trie.t A.
```

`Trie.elements` and `Trie.fold` visit keys in the in-order of the trie: left subtree, root,
right subtree. That order is the strict order `Trie.key_lt`:

```coq
Fixpoint Trie.key_lt (p q : positive) {struct p} : Prop :=
  match p, q with
  | xO p', xO q' => Trie.key_lt p' q'
  | xI p', xI q' => Trie.key_lt p' q'
  | xO _, xH | xO _, xI _ | xH, xI _ => True
  | _, _ => False
  end.
```

When `f None None = None`, `Trie.combine f t1 t2` binds `p` to
`f (Trie.get p t1) (Trie.get p t2)` whenever that is `Some`. It visits only the paths present in
`t1` or `t2` (cost linear in their sizes, no key enumeration).
`Trie.forall2 r t1 t2` is true when `r a (Trie.get p t2) = true` for every binding `(p, a)` of `t1`;
it stops at the first failure and follows `t2` only along the paths of `t1`. `Trie.union_with f t1
t2` binds `p` to `Trie.union_opt f (Trie.get p t1) (Trie.get p t2)`; a subtree present in one trie
only is shared, never rebuilt. `combine` is the general operation (it rebuilds one-sided subtrees
through `f`); `forall2` and `union_with` are the cheap cases that subset tests and unions need.

### Maps (`CollectionsMap.v`)

```coq
Definition Map.t (K V : Type) : Type := Trie.t (K * V).   (* the key is stored at its code *)
Definition Map.empty {K V} : Map.t K V := Trie.empty.
Definition Map.wf {K V} (E : encoding K) (m : Map.t K V) : Prop :=
  forall p k v, Trie.get p m = Some (k, v) -> encode E k = p.
Definition Map.code_get {K V} (p : positive) (m : Map.t K V) : option V := option_map snd (Trie.get p m).
(* the value at a position, whatever key is stored there: the position-level API *)
Definition Map.get {K V} (E : encoding K) (k : K) (m : Map.t K V) : option V :=
  Map.code_get (encode E k) m.
Definition Map.set {K V} (E : encoding K) (k : K) (v : V) (m : Map.t K V) : Map.t K V.
Definition Map.remove {K V} (E : encoding K) (k : K) (m : Map.t K V) : Map.t K V.
Definition Map.map {K V W} (f : V -> W) (m : Map.t K V) : Map.t K W.
Definition Map.combine {K V W U} (E : encoding K) (f : option V -> option W -> option U)
  (m1 : Map.t K V) (m2 : Map.t K W) : Map.t K U.   (* pointwise when f None None = None *)
Definition Map.fold {K V B} (f : B -> K -> V -> B) (m : Map.t K V) (b : B) : B.
Definition Map.elements {K V} (m : Map.t K V) : list (K * V).     (* Trie order of the codes *)
Definition Map.size {K V} (m : Map.t K V) : nat.
Definition Map.is_empty {K V} (m : Map.t K V) : bool.
Definition Map.mem {K V} (E : encoding K) (k : K) (m : Map.t K V) : bool.
Definition Map.of_list {K V} (E : encoding K) (l : list (K * V)) : Map.t K V.
(* fold_left of Map.set from Map.empty: a later binding replaces an earlier one *)
Definition Map.beq {K V} (eqb : V -> V -> bool) (m1 m2 : Map.t K V) : bool.   (* values only *)
Definition Map.forall2 {K V W} (r : V -> option W -> bool) (m1 : Map.t K V) (m2 : Map.t K W) : bool.
(* Trie.forall2 on the stored pairs: r is applied to the value of m1 and the value (if any) of m2 *)
Definition Map.union_with {K V} (f : V -> V -> V) (m1 m2 : Map.t K V) : Map.t K V.
(* Trie.union_with on the stored pairs; a position bound in both keeps the key of m1 *)
```

`Map.get E k m` reads the trie at `encode E k` and drops the stored key. `Map.set E k v m` stores
`(k, v)` at `encode E k`. `Map.map f` maps values and keeps keys. `Map.combine` keeps, at each
position it binds, the key stored in `m1` if present and otherwise the key stored in `m2`.
`Map.size`, `Map.is_empty` and `Map.mem` are defined from `Trie.size`, `Trie.is_empty` and
`Map.get`.
`Map.beq eqb` is `Trie.beq` on the stored pairs comparing values only, which is sound for
well-formed
maps because stored keys at equal codes are equal.

`Map.code_get p m` reads the trie at the code `p` and never decodes a key; `Map.get E k m` is
`Map.code_get (encode E k) m` by definition. `Map.forall2` and `Map.union_with` are the map forms of
`Trie.forall2` and `Trie.union_with`; Order's pointwise comparison and join, and `FinSet.subset` and
`FinSet.union`, are defined through them.

### Finite sets (`CollectionsFinSet.v`)

```coq
Definition FinSet.t (K : Type) : Type := Map.t K unit.
Definition FinSet.wf {K} (E : encoding K) (s : FinSet.t K) : Prop := Map.wf E s.
Definition FinSet.empty {K} : FinSet.t K := Map.empty.
Definition FinSet.mem {K} (E : encoding K) (k : K) (s : FinSet.t K) : bool.
Definition FinSet.add {K} (E : encoding K) (k : K) (s : FinSet.t K) : FinSet.t K := Map.set E k tt s.
Definition FinSet.remove {K} (E : encoding K) (k : K) (s : FinSet.t K) : FinSet.t K := Map.remove E k s.
Definition FinSet.union {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.union_with (fun a _ => a) s1 s2.
Definition FinSet.inter {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.combine E (fun a b => match a, b with Some _, Some _ => Some tt | _, _ => None end) s1 s2.
Definition FinSet.diff {K} (E : encoding K) (s1 s2 : FinSet.t K) : FinSet.t K :=
  Map.combine E (fun a b => match a, b with Some _, None => Some tt | _, _ => None end) s1 s2.
Definition FinSet.subset {K} (E : encoding K) (s1 s2 : FinSet.t K) : bool :=
  Map.forall2 (fun _ o => match o with Some _ => true | None => false end) s1 s2.
Definition FinSet.elements {K} (s : FinSet.t K) : list K := List.map fst (Map.elements s).
Definition FinSet.size {K} (s : FinSet.t K) : nat := Map.size s.
Definition FinSet.is_empty {K} (s : FinSet.t K) : bool := Map.is_empty s.
Definition FinSet.of_list {K} (E : encoding K) (l : list K) : FinSet.t K.     (* fold of FinSet.add *)
```

`FinSet.union`, `FinSet.inter`, `FinSet.diff` and `FinSet.subset` are position-wise: they compare
codes and
never decode keys, so they are correct for every trie, well-formed or not; the specification
theorems below add `FinSet.wf` only where they speak about keys.
`FinSet.subset` stops at the first binding of `s1` that `s2` lacks, and `FinSet.union` shares the
subtrees
that only one operand has; neither builds an intermediate trie.

### Priority queue (`CollectionsHeap.v`)

`PQueue.t K` holds each key at most once, with one priority. The pop order is the lexicographic
order on `(priority, encode key)`, so ties between keys of equal priority are broken by code and a
run is deterministic.

```coq
Definition PQueue.t (K : Type) : Type.
Definition PQueue.empty {K} : PQueue.t K.
Definition PQueue.is_empty {K} (q : PQueue.t K) : bool.
Definition PQueue.size {K} (q : PQueue.t K) : nat.        (* number of keys held; O(1) *)
Definition PQueue.push {K} (E : encoding K) (p : positive) (k : K) (q : PQueue.t K) : PQueue.t K.
(* absent key: inserted with priority p; present key: priority becomes Pos.min p old *)
Definition PQueue.pop {K} (E : encoding K) (q : PQueue.t K) : option (positive * K * PQueue.t K).
(* None on an empty queue; else the minimal (priority, code) key with its priority, and the rest *)
Definition PQueue.priority {K} (E : encoding K) (k : K) (q : PQueue.t K) : option positive.
Definition PQueue.members {K} (q : PQueue.t K) : list (K * positive).   (* the held pairs *)
Definition PQueue.wf {K} (E : encoding K) (q : PQueue.t K) : Prop.
Definition PQueue.before (p1 c1 p2 c2 : positive) : Prop :=
  (p1 < p2)%positive \/ (p1 = p2 /\ (c1 <= c2)%positive).
```

The specification is the finite map `key -> priority` that `PQueue.priority` reads and
`PQueue.members` lists. Use a persistent rank-position binomial heap of entries
`(priority, code, key)`, a `Map.t K positive` of live priorities, and cached live and pending
entry counts. A push that lowers a priority inserts a new entry and leaves the old entry stale;
`pop` discards an entry
whose priority differs from the live one, including when its key is absent from the live map.
`PQueue.wf` says the heap order holds, every entry's code is `encode E key`, the live map satisfies
`Map.wf E`, every live key has an entry with its live priority, and the counters agree with the
live keys and pending entries. Heap ranks are represented by position, so linking and merging do
not compare rank values. `pop` uses the cached entry count as fuel, decreasing it for each
discarded entry.

### Union-find (`CollectionsUnionFind.v`)

Every key starts alone in its own class, so `UnionFind.make` needs no key list. The structure is a
record that lives in its own module, so that its field names never clash with Order's `rank`:

```coq
Record UnionFind.t (K : Type) : Type := Forest {
  parents : Map.t K K;                         (* absent: the key is a root *)
  ranks : Map.t K nat;                         (* absent: rank 0 *)
  max_rank : nat                               (* an upper bound on every rank *)
}.
Definition UnionFind.make {K} : UnionFind.t K := Forest Map.empty Map.empty 0.
Definition UnionFind.find {K} (E : encoding K) (x : K) (uf : UnionFind.t K) : K * UnionFind.t K.
(* the representative of x, and uf with the path from x compressed *)
Definition UnionFind.union {K} (E : encoding K) (x y : K) (uf : UnionFind.t K) : UnionFind.t K.
Definition UnionFind.equiv {K} (E : encoding K) (uf : UnionFind.t K) (x y : K) : Prop :=
  fst (UnionFind.find E x uf) = fst (UnionFind.find E y uf).
Definition UnionFind.equivb {K} (E : encoding K) (x y : K) (uf : UnionFind.t K) :
  bool * UnionFind.t K.                       (* the test, and the compressed structure *)
Definition UnionFind.keys {K} (E : encoding K) (uf : UnionFind.t K) : list K.
(* the support: the keys with a parent or a rank entry, each once; the FinSet.elements of the union
   of the key sets of parents and ranks *)
Definition UnionFind.wf {K} (E : encoding K) (uf : UnionFind.t K) : Prop.
Definition UnionFind.of_unions {K} (E : encoding K) (l : list (K * K)) : UnionFind.t K :=
  List.fold_left (fun uf xy => UnionFind.union E (fst xy) (snd xy) uf) l UnionFind.make.
```

`UnionFind.find` follows parent links with fuel `S (max_rank uf)`. A key with no parent is a root.
Otherwise it recurses with one unit less and, on return, sets the parent of the current key to the
root found (path compression). When the fuel runs out it returns the current key and the structure
unchanged; a well-formed structure never runs out, because ranks strictly increase along parent
links and are at most `max_rank`, so a path has at most `max_rank` links. `UnionFind.wf E uf`
says: `Map.wf E` holds for `parents uf` and for `ranks uf`; every rank is at most `max_rank uf`;
and, reading an absent rank as 0, the rank of a key is strictly below the rank of its parent
(acyclicity follows).

`UnionFind.union E x y uf` finds both representatives `rx` and `ry`. If they are equal it records
`rx` in the support (rank 0 if new) and returns the structure after the two finds. Otherwise it
links by rank: the lower rank goes below the higher; on equal ranks `ry` goes below `rx` and the
rank of `rx` grows by one, so the representative is a deterministic function of the call
sequence. `max_rank` becomes the larger of its old value and any rank written.

### Tables (`CollectionsTable.v`)

A table maps a `list positive` to a value; hash-consing uses it to map an operator code followed by
operand numbers to a node number. It is a flat `Map` keyed by the list encoding, and every
operation is the `Map` operation at that encoding:

```coq
Definition Table.key : encoding (list positive) := list_encoding positive_encoding.
Definition Table.t (V : Type) : Type := Map.t (list positive) V.
Definition Table.empty {V} : Table.t V := Map.empty.
Definition Table.wf {V} (t : Table.t V) : Prop := Map.wf Table.key t.
(* a flat map has no nodes, so there is no root to exempt: the empty list is an ordinary key *)
Definition Table.get {V} (k : list positive) (t : Table.t V) : option V := Map.get Table.key k t.
Definition Table.set {V} (k : list positive) (v : V) (t : Table.t V) : Table.t V :=
  Map.set Table.key k v t.
Definition Table.remove {V} (k : list positive) (t : Table.t V) : Table.t V :=
  Map.remove Table.key k t.
Definition Table.is_empty {V} (t : Table.t V) : bool := Map.is_empty t.
Definition Table.fold {V B} (f : B -> list positive -> V -> B) (t : Table.t V) (b : B) : B :=
  Map.fold f t b.
Definition Table.elements {V} (t : Table.t V) : list (list positive * V) := Map.elements t.
Definition Table.size {V} (t : Table.t V) : nat := Map.size t.
```

`Table.elements` lists the bindings in the trie order of the list codes, not in lexicographic order
of the keys. Keys that share a prefix share no structure.

## Theorems

Each group sits in a `Section` whose `Context` and `Variables` lines declare the types and
variables it mentions; a theorem is generalised over exactly the ones it uses, in declaration
order. A `(* Proof idea ... Card ... *)` line follows each group of theorems.

### Tries

```coq
Section TrieLaws.
Context {A B C : Type}.
Variables (t t1 t2 : Trie.t A) (u : Trie.t B) (p q : positive) (v : A)
  (f : option A -> option B -> option C).

(** Two tries with the same bindings are equal: the representation is canonical. *)
Theorem Trie.extensionality : (forall p, Trie.get p t1 = Trie.get p t2) -> t1 = t2.
(* Proof idea: induction on both trees; the seven shapes are fixed by get at xH, xO _, xI _.
   Card: COL-1b. *)

(** An empty trie binds nothing, and a trie that binds nothing is the empty trie. *)
Theorem Trie.get_empty : Trie.get p (@Trie.empty A) = None.
Theorem Trie.is_empty_spec : Trie.is_empty t = true <-> t = Trie.empty.
(* Proof idea: unfolding; the second by canonicity. Card: COL-1b. *)

(** Lookup after update. *)
Theorem Trie.get_set_same : Trie.get p (Trie.set p v t) = Some v.
Theorem Trie.get_set_other : p <> q -> Trie.get q (Trie.set p v t) = Trie.get q t.
Theorem Trie.get_remove_same : Trie.get p (Trie.remove p t) = None.
Theorem Trie.get_remove_other : p <> q -> Trie.get q (Trie.remove p t) = Trie.get q t.
(* Proof idea: induction on the path p, splitting on the node shape. Card: COL-1b. *)

(** Mapping and combining act position by position; combining needs f None None = None. *)
Theorem Trie.get_map : forall (g : A -> B), Trie.get p (Trie.map g t) = option_map g (Trie.get p t).
Theorem Trie.get_combine : f None None = None ->
  Trie.get p (Trie.combine f t u) = f (Trie.get p t) (Trie.get p u).
(* Proof idea: induction on both tries, rebuilding through a constructor that drops empty subtrees.
   Card: COL-1b. *)

(** The elements are the bindings, each once, in trie order. *)
Theorem Trie.elements_sound : In (p, v) (Trie.elements t) -> Trie.get p t = Some v.
Theorem Trie.elements_complete : Trie.get p t = Some v -> In (p, v) (Trie.elements t).
Theorem Trie.elements_nodup : NoDup (List.map fst (Trie.elements t)).
Theorem Trie.elements_sorted :
  StronglySorted (fun a b => Trie.key_lt (fst a) (fst b)) (Trie.elements t).
(* Proof idea: induction on the shapes; xO-keys precede the root key, which precedes xI-keys.
   Card: COL-1b. *)

(** Folding visits the elements in order; the size counts them. *)
Theorem Trie.fold_elements : forall (g : B -> positive -> A -> B) (b : B),
  Trie.fold g t b = List.fold_left (fun acc pv => g acc (fst pv) (snd pv)) (Trie.elements t) b.
Theorem Trie.size_elements : Trie.size t = List.length (Trie.elements t).
(* Proof idea: induction on the shapes, with an accumulator for the fold. Card: COL-1b. *)

(** Structural comparison compares the bindings position by position, whatever `eqb` is; with an
    `eqb` that decides equality it is equality of tries. *)
Theorem Trie.beq_pointwise : forall (eqb : A -> A -> bool),
  Trie.beq eqb t1 t2 = true <-> forall p, match Trie.get p t1, Trie.get p t2 with
    | None, None => True | Some a, Some b => eqb a b = true | _, _ => False end.
Theorem Trie.beq_correct : forall (eqb : A -> A -> bool),
  (forall a b, eqb a b = true <-> a = b) -> (Trie.beq eqb t1 t2 = true <-> t1 = t2).
(* Proof idea: beq_pointwise by induction on both trees, with no assumption on eqb; beq_correct
   from beq_pointwise and Trie.extensionality. Card: COL-1b. *)

(** Subset tests and unions without rebuilding: `forall2` tests the bindings of the first trie
    against the second; `union_with` binds each position by `union_opt`, sharing one-sided subtrees. *)
Theorem Trie.forall2_spec : forall (r : A -> option B -> bool),
  Trie.forall2 r t u = true <-> forall (p : positive) (a : A), Trie.get p t = Some a ->
  r a (Trie.get p u) = true.
Theorem Trie.get_union_with : forall (f : A -> A -> A),
  Trie.get p (Trie.union_with f t t1) = Trie.union_opt f (Trie.get p t) (Trie.get p t1).
Theorem Trie.union_with_combine : forall (f : A -> A -> A),
  Trie.union_with f t t1 = Trie.combine (Trie.union_opt f) t t1.
(* Proof idea: induction on both tries; the last by Trie.extensionality, since union_opt f None None
   is None. Card: COL-1b. *)
End TrieLaws.
```

### Maps

```coq
Section MapLaws.
Context {K V W U : Type} (E : encoding K).
Variables (k k1 k2 : K) (v : V) (m m' : Map.t K V) (n : Map.t K W).

(** The position-level API: it reads the trie by code and never decodes a key, so these laws hold
    for every map, well formed or not. `Map.get` is `Map.code_get` at the code of the key. *)
Theorem Map.get_code : Map.get E k m = Map.code_get (encode E k) m.
Theorem Map.code_get_empty : forall p, Map.code_get p (@Map.empty K V) = None.
Theorem Map.code_get_combine : forall (f : option V -> option W -> option U) (p : positive),
  f None None = None ->
  Map.code_get p (Map.combine E f m n) = f (Map.code_get p m) (Map.code_get p n).
Theorem Map.code_get_union_with : forall (f : V -> V -> V) (p : positive),
  Map.code_get p (Map.union_with f m m') = Trie.union_opt f (Map.code_get p m) (Map.code_get p m').
Theorem Map.forall2_spec : forall (r : V -> option W -> bool),
  Map.forall2 r m n = true <-> forall (p : positive) (v : V), Map.code_get p m = Some v ->
  r v (Map.code_get p n) = true.
Theorem Map.wf_union_with : forall (f : V -> V -> V), Map.wf E m -> Map.wf E m' ->
  Map.wf E (Map.union_with f m m').
Theorem Map.mem_spec : Map.mem E k m = true <-> Map.get E k m <> None.
Theorem Map.is_empty_spec : Map.wf E m -> (Map.is_empty m = true <-> forall k, Map.get E k m = None).
(* Proof idea: Map.get_code is the definition; the others are Trie.get_combine, Trie.get_union_with
   and Trie.forall2_spec on the stored pairs, with the key dropped by snd; is_empty_spec by
   Trie.is_empty_spec, since wf puts a stored key at its code. Card: COL-1c. *)

(** Every operation keeps stored keys at their codes. *)
Theorem Map.wf_empty : Map.wf E (@Map.empty K V).
Theorem Map.wf_set : Map.wf E m -> Map.wf E (Map.set E k v m).
Theorem Map.wf_remove : Map.wf E m -> Map.wf E (Map.remove E k m).
Theorem Map.wf_map : forall (f : V -> W), Map.wf E m -> Map.wf E (Map.map f m).
Theorem Map.wf_combine : forall (f : option V -> option W -> option U),
  Map.wf E m -> Map.wf E n -> Map.wf E (Map.combine E f m n).
Theorem Map.wf_of_list : forall (l : list (K * V)), Map.wf E (Map.of_list E l).
(* Proof idea: Trie.get_set_*, Trie.get_combine at a position, then encode_injective.
   Card: COL-1c. *)

(** Lookup after update; these hold for every map, well-formed or not. *)
Theorem Map.get_empty : Map.get E k (@Map.empty K V) = None.
Theorem Map.get_set_same : Map.get E k (Map.set E k v m) = Some v.
Theorem Map.get_set_other : k1 <> k2 -> Map.get E k1 (Map.set E k2 v m) = Map.get E k1 m.
Theorem Map.get_remove_same : Map.get E k (Map.remove E k m) = None.
Theorem Map.get_remove_other : k1 <> k2 -> Map.get E k1 (Map.remove E k2 m) = Map.get E k1 m.
Theorem Map.get_map : forall (f : V -> W), Map.get E k (Map.map f m) = option_map f (Map.get E k m).
Theorem Map.get_combine : forall (f : option V -> option W -> option U), f None None = None ->
  Map.get E k (Map.combine E f m n) = f (Map.get E k m) (Map.get E k n).
Theorem Map.get_of_list : forall (l : list (K * V)), Map.get E k (Map.of_list E l) =
  option_map snd (List.find (fun kv => Pos.eqb (encode E (fst kv)) (encode E k)) (List.rev l)).
(* Proof idea: unfold to Trie.get at encode E k; the _other laws use encode_injective.
   Card: COL-1c. *)

(** Well-formed maps with the same lookups are equal. *)
Theorem Map.extensionality :
  Map.wf E m -> Map.wf E m' -> (forall k, Map.get E k m = Map.get E k m') -> m = m'.
(* Proof idea: a stored (k, v) sits at encode E k, so the other map stores the same pair
   there; then Trie.extensionality. Card: COL-1c. *)

(** Elements list each binding of a well-formed map once; fold is a fold over them. *)
Theorem Map.elements_sound : Map.wf E m -> In (k, v) (Map.elements m) -> Map.get E k m = Some v.
Theorem Map.elements_complete : Map.wf E m -> Map.get E k m = Some v -> In (k, v) (Map.elements m).
Theorem Map.elements_nodup : Map.wf E m -> NoDup (List.map fst (Map.elements m)).
Theorem Map.fold_elements : forall (B : Type) (f : B -> K -> V -> B) (b : B),
  Map.fold f m b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (Map.elements m) b.
Theorem Map.size_elements : Map.size m = List.length (Map.elements m).
(* Proof idea: from the Trie versions; well-formedness identifies stored keys with codes.
   Card: COL-1c. *)

(** Comparing values position by position is equality of lookups, for well-formed maps. *)
Theorem Map.beq_correct : forall (eqb : V -> V -> bool), (forall a b, eqb a b = true <-> a = b) ->
  Map.wf E m -> Map.wf E m' -> (Map.beq eqb m m' = true <-> forall k, Map.get E k m = Map.get E k m').
(* Proof idea: Trie.beq_pointwise on the stored pairs; wf puts every stored key at its code, so a
   position bound in one map is bound in the other with the same lookups. Card: COL-1c. *)
End MapLaws.
```

### Finite sets

```coq
Section FinSetLaws.
Context {K : Type} (E : encoding K).
Variables (k k1 k2 : K) (s s1 s2 s3 : FinSet.t K) (l : list K) (p : positive).

(** Membership laws, each unconditional. *)
Theorem FinSet.mem_empty : FinSet.mem E k (@FinSet.empty K) = false.
Theorem FinSet.mem_add : FinSet.mem E k1 (FinSet.add E k2 s) = true <-> k1 = k2 \/ FinSet.mem E k1 s = true.
Theorem FinSet.mem_remove : FinSet.mem E k1 (FinSet.remove E k2 s) = true <-> k1 <> k2 /\ FinSet.mem E k1 s = true.
Theorem FinSet.mem_union : FinSet.mem E k (FinSet.union E s1 s2) = true <->
  FinSet.mem E k s1 = true \/ FinSet.mem E k s2 = true.
Theorem FinSet.mem_inter : FinSet.mem E k (FinSet.inter E s1 s2) = true <->
  FinSet.mem E k s1 = true /\ FinSet.mem E k s2 = true.
Theorem FinSet.mem_diff : FinSet.mem E k (FinSet.diff E s1 s2) = true <->
  FinSet.mem E k s1 = true /\ FinSet.mem E k s2 = false.
Theorem FinSet.of_list_spec : FinSet.mem E k (FinSet.of_list E l) = true <-> In k l.
(* Proof idea: the Map.get_* laws and encode_injective. Card: COL-1c. *)

(** Every set operation keeps well-formedness. *)
Theorem FinSet.wf_ops : FinSet.wf E s1 -> FinSet.wf E s2 ->
  FinSet.wf E (@FinSet.empty K) /\ FinSet.wf E (FinSet.add E k s1) /\ FinSet.wf E (FinSet.remove E k s1) /\
  FinSet.wf E (FinSet.union E s1 s2) /\ FinSet.wf E (FinSet.inter E s1 s2) /\ FinSet.wf E (FinSet.diff E s1 s2) /\
  FinSet.wf E (FinSet.of_list E l).
(* Proof idea: the Map.wf_* theorems. Card: COL-1c. *)

(** Well-formed sets with the same members are equal; subset is inclusion of members. *)
Theorem FinSet.extensionality :
  FinSet.wf E s1 -> FinSet.wf E s2 -> (forall k, FinSet.mem E k s1 = FinSet.mem E k s2) -> s1 = s2.
Theorem FinSet.subset_spec : FinSet.wf E s1 ->
  (FinSet.subset E s1 s2 = true <-> forall k, FinSet.mem E k s1 = true -> FinSet.mem E k s2 = true).
(* Proof idea: Map.extensionality (unit has one value); subset_spec from FinSet.subset_code,
   since wf puts every stored key of s1 at its code.
   Card: COL-1c. *)

(** Elements are the members, once each; the size counts them. *)
Theorem FinSet.elements_spec : FinSet.wf E s -> (In k (FinSet.elements s) <-> FinSet.mem E k s = true).
Theorem FinSet.elements_nodup : FinSet.wf E s -> NoDup (FinSet.elements s).
Theorem FinSet.size_elements : FinSet.size s = List.length (FinSet.elements s).
(* Proof idea: from Map.elements_*. Card: COL-1c. *)

(** The position-level API: membership, union, intersection, difference and subset read one
    position, for every set, well formed or not. *)
Theorem FinSet.mem_code : FinSet.mem E k s = true <-> Map.code_get (encode E k) s <> None.
Theorem FinSet.union_code : Map.code_get p (FinSet.union E s1 s2) <> None <->
  Map.code_get p s1 <> None \/ Map.code_get p s2 <> None.
Theorem FinSet.inter_code : Map.code_get p (FinSet.inter E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 <> None.
Theorem FinSet.diff_code : Map.code_get p (FinSet.diff E s1 s2) <> None <->
  Map.code_get p s1 <> None /\ Map.code_get p s2 = None.
Theorem FinSet.subset_code : FinSet.subset E s1 s2 = true <->
  forall p, Map.code_get p s1 <> None -> Map.code_get p s2 <> None.
(* Proof idea: unfolding mem; Map.code_get_union_with and Map.code_get_combine; Map.forall2_spec for
   subset, the unit value being discarded. Card: COL-1c. *)

(** Emptiness and size: a well-formed set with no member is empty; inclusion bounds the size, and
    strictly when it is proper; a set inside a universe is no larger than the universe. *)
Theorem FinSet.is_empty_spec : FinSet.wf E s -> (FinSet.is_empty s = true <-> forall k, FinSet.mem E k s = false).
Theorem FinSet.size_subset : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.subset E s1 s2 = true ->
  FinSet.size s1 <= FinSet.size s2.
Theorem FinSet.size_lt : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.subset E s1 s2 = true ->
  FinSet.subset E s2 s1 = false -> FinSet.size s1 < FinSet.size s2.
Theorem FinSet.size_le_length : forall U : list K, FinSet.wf E s1 ->
  (forall k, FinSet.mem E k s1 = true -> In k U) -> FinSet.size s1 <= List.length U.
(* Proof idea: Map.is_empty_spec; the size is the length of the elements, which are NoDup and are
   exactly the members (FinSet.elements_spec); NoDup_incl_length, adding one member outside s1 for the
   strict case. Card: COL-1c. *)

(** The algebra of well-formed sets, as equalities. *)
Theorem FinSet.union_comm : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.union E s1 s2 = FinSet.union E s2 s1.
Theorem FinSet.union_assoc : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.union E s1 (FinSet.union E s2 s3) = FinSet.union E (FinSet.union E s1 s2) s3.
Theorem FinSet.union_idem : FinSet.wf E s -> FinSet.union E s s = s.
Theorem FinSet.union_empty_r : FinSet.wf E s -> FinSet.union E s FinSet.empty = s.
Theorem FinSet.inter_comm : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.inter E s1 s2 = FinSet.inter E s2 s1.
Theorem FinSet.inter_assoc : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.inter E s1 (FinSet.inter E s2 s3) = FinSet.inter E (FinSet.inter E s1 s2) s3.
Theorem FinSet.inter_idem : FinSet.wf E s -> FinSet.inter E s s = s.
Theorem FinSet.inter_empty_r : FinSet.wf E s -> FinSet.inter E s FinSet.empty = FinSet.empty.
Theorem FinSet.inter_union_distr : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.wf E s3 ->
  FinSet.inter E s1 (FinSet.union E s2 s3) = FinSet.union E (FinSet.inter E s1 s2) (FinSet.inter E s1 s3).
Theorem FinSet.union_inter_absorb : FinSet.wf E s1 -> FinSet.wf E s2 -> FinSet.union E s1 (FinSet.inter E s1 s2) = s1.
Theorem FinSet.diff_self : FinSet.wf E s -> FinSet.diff E s s = FinSet.empty.
(* Proof idea: FinSet.extensionality after FinSet.wf_ops, then Boolean reasoning on FinSet.mem_*.
   Card: COL-1c. *)
End FinSetLaws.
```

### Priority queue

```coq
Section PQueueLaws.
Context {K : Type} (E : encoding K).
Variables (q q' : PQueue.t K) (p p2 : positive) (k k1 k2 : K).

(** The empty queue is well formed and holds no key. *)
Theorem PQueue.wf_empty : PQueue.wf E (@PQueue.empty K).
Theorem PQueue.priority_empty : PQueue.priority E k (@PQueue.empty K) = None.
(* Proof idea: unfolding the empty heap and the empty live map. Card: COL-2. *)

(** Push keeps the smaller priority of a present key and leaves other keys alone. *)
Theorem PQueue.priority_push_same : PQueue.wf E q -> PQueue.priority E k (PQueue.push E p k q) =
  Some (match PQueue.priority E k q with None => p | Some p0 => Pos.min p0 p end).
Theorem PQueue.priority_push_other : PQueue.wf E q -> k1 <> k2 ->
  PQueue.priority E k1 (PQueue.push E p k2 q) = PQueue.priority E k1 q.
Theorem PQueue.size_push_new : PQueue.wf E q -> PQueue.priority E k q = None ->
  PQueue.size (PQueue.push E p k q) = S (PQueue.size q).
Theorem PQueue.size_push_old : PQueue.wf E q -> PQueue.priority E k q <> None ->
  PQueue.size (PQueue.push E p k q) = PQueue.size q.
Theorem PQueue.wf_push : PQueue.wf E q -> PQueue.wf E (PQueue.push E p k q).
(* Proof idea: binomial-heap insertion plus a live-map update; a lowering push adds one entry
   and makes the old one stale. Card: COL-2. *)

(** Pop fails exactly on an empty queue. *)
Theorem PQueue.pop_none : PQueue.wf E q -> (PQueue.pop E q = None <-> PQueue.is_empty q = true).
(** Pop returns a key of minimal (priority, code) and removes exactly that key. *)
Theorem PQueue.pop_min : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') ->
  PQueue.priority E k q = Some p /\
  forall (k2 : K) (p2 : positive), PQueue.priority E k2 q = Some p2 ->
    PQueue.before p (encode E k) p2 (encode E k2).
Theorem PQueue.pop_rest : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') ->
  PQueue.priority E k q' = None /\
  (forall k2 : K, k2 <> k -> PQueue.priority E k2 q' = PQueue.priority E k2 q) /\
  PQueue.size q = S (PQueue.size q').
Theorem PQueue.wf_pop : PQueue.wf E q -> PQueue.pop E q = Some (p, k, q') -> PQueue.wf E q'.
(* Proof idea: discard heap tops that disagree with the live map, then merge the subheaps of the
   first top that agrees. Card: COL-2. *)

(** The held pairs are the live map, once per key, and their number is the size. *)
Theorem PQueue.members_spec : PQueue.wf E q ->
  (In (k, p) (PQueue.members q) <-> PQueue.priority E k q = Some p).
Theorem PQueue.members_nodup : PQueue.wf E q -> NoDup (List.map fst (PQueue.members q)).
Theorem PQueue.size_members : PQueue.wf E q -> PQueue.size q = List.length (PQueue.members q).
Theorem PQueue.is_empty_spec : PQueue.wf E q ->
  (PQueue.is_empty q = true <-> forall k, PQueue.priority E k q = None).
(* Proof idea: members is Map.elements of the live map; Map.elements_* and wf link the counter. Card: COL-2. *)
End PQueueLaws.
```

### Union-find

```coq
Section UnionFindLaws.
Context {K : Type} (E : encoding K).
Variables (uf : UnionFind.t K) (x y z a b : K) (l : list (K * K)).

(** Equivalence is an equivalence relation, whatever the structure. *)
Theorem UnionFind.equiv_equivalence : equivalence K (UnionFind.equiv E uf).
(* Proof idea: equality of representatives. Card: COL-2. *)

(** Every operation keeps the structure well formed. *)
Theorem UnionFind.wf_make : UnionFind.wf E (@UnionFind.make K).
Theorem UnionFind.wf_find : UnionFind.wf E uf -> UnionFind.wf E (snd (UnionFind.find E x uf)).
Theorem UnionFind.wf_union : UnionFind.wf E uf -> UnionFind.wf E (UnionFind.union E x y uf).
(* Proof idea: compression redirects a node to an ancestor, which has a larger rank; linking
   raises a rank only on a tie. Card: COL-2. *)

(** Finding never changes anyone's representative, and a representative represents itself:
    representatives are canonical. *)
Theorem UnionFind.find_rep_stable : UnionFind.wf E uf ->
  fst (UnionFind.find E x (snd (UnionFind.find E y uf))) = fst (UnionFind.find E x uf).
Theorem UnionFind.find_rep_canonical : UnionFind.wf E uf ->
  fst (UnionFind.find E (fst (UnionFind.find E x uf)) uf) = fst (UnionFind.find E x uf).
(* Proof idea: the root reached from x is the root reached from every node on its path. Card: COL-2. *)

(** A fresh structure relates only equal keys; union merges exactly the classes of its arguments. *)
Theorem UnionFind.make_equiv : UnionFind.equiv E UnionFind.make a b <-> a = b.
Theorem UnionFind.union_equiv : UnionFind.wf E uf ->
  (UnionFind.equiv E (UnionFind.union E x y uf) a b <->
   UnionFind.equiv E uf a b \/
   (UnionFind.equiv E uf a x /\ UnionFind.equiv E uf y b) \/
   (UnionFind.equiv E uf a y /\ UnionFind.equiv E uf x b)).
(* Proof idea: the linked root becomes the representative of both classes; other roots stay. Card: COL-2. *)

(** Equivalence is the equivalence closure of the unions performed. *)
Theorem UnionFind.of_unions_equiv : UnionFind.equiv E (UnionFind.of_unions E l) a b <->
  clos_refl_sym_trans K (fun x y => In (x, y) l) a b.
(* Proof idea: induction on l from the right with make_equiv, union_equiv and wf_union. Card: COL-2. *)

(** The boolean test agrees with equiv and returns an equivalent structure. *)
Theorem UnionFind.equivb_correct : UnionFind.wf E uf ->
  (fst (UnionFind.equivb E x y uf) = true <-> UnionFind.equiv E uf x y) /\
  UnionFind.wf E (snd (UnionFind.equivb E x y uf)) /\
  (forall a b, UnionFind.equiv E (snd (UnionFind.equivb E x y uf)) a b <-> UnionFind.equiv E uf a b).
(* Proof idea: two finds, then find_rep_stable and wf_find. Card: COL-2. *)

(** Keys outside the support are alone in their class; the support is exactly the unioned keys,
    each once. *)
Theorem UnionFind.keys_support : UnionFind.wf E uf -> ~ In x (UnionFind.keys E uf) ->
  UnionFind.equiv E uf x y -> y = x.
Theorem UnionFind.keys_make : UnionFind.keys E (@UnionFind.make K) = nil.
Theorem UnionFind.keys_union : UnionFind.wf E uf ->
  (In z (UnionFind.keys E (UnionFind.union E x y uf)) <-> z = x \/ z = y \/ In z (UnionFind.keys E uf)).
Theorem UnionFind.keys_nodup : UnionFind.wf E uf -> NoDup (UnionFind.keys E uf).
(* Proof idea: a key has a parent or rank entry exactly after it is unioned, and a parent has a
   positive rank, so it has a rank entry; the key sets are FinSet.wf by Map.wf, so the union's
   elements are NoDup. Card: COL-2. *)
End UnionFindLaws.
```

### Tables

```coq
Section TableLaws.
Context {V : Type}.
Variables (t t' : Table.t V) (k k1 k2 : list positive) (v : V).

(** Lookup after update, for every table. *)
Theorem Table.get_empty : Table.get k (@Table.empty V) = None.
Theorem Table.get_set_same : Table.get k (Table.set k v t) = Some v.
Theorem Table.get_set_other : k1 <> k2 -> Table.get k1 (Table.set k2 v t) = Table.get k1 t.
Theorem Table.get_remove_same : Table.get k (Table.remove k t) = None.
Theorem Table.get_remove_other : k1 <> k2 -> Table.get k1 (Table.remove k2 t) = Table.get k1 t.
(* Proof idea: the Map laws at Table.key. Card: COL-2. *)

(** Well-formedness is preserved, and well-formed tables with equal lookups are equal. *)
Theorem Table.wf_empty : Table.wf (@Table.empty V).
Theorem Table.wf_set : Table.wf t -> Table.wf (Table.set k v t).
Theorem Table.wf_remove : Table.wf t -> Table.wf (Table.remove k t).
Theorem Table.extensionality :
  Table.wf t -> Table.wf t' -> (forall k, Table.get k t = Table.get k t') -> t = t'.
(* Proof idea: Map.wf_empty, Map.wf_set, Map.wf_remove and Map.extensionality. Card: COL-2. *)

(** Elements list each binding of a well-formed table once; fold, size and emptiness follow. *)
Theorem Table.elements_sound : Table.wf t -> In (k, v) (Table.elements t) -> Table.get k t = Some v.
Theorem Table.elements_complete : Table.wf t -> Table.get k t = Some v -> In (k, v) (Table.elements t).
Theorem Table.elements_nodup : Table.wf t -> NoDup (List.map fst (Table.elements t)).
Theorem Table.fold_elements : forall (B : Type) (f : B -> list positive -> V -> B) (b : B),
  Table.fold f t b = List.fold_left (fun acc kv => f acc (fst kv) (snd kv)) (Table.elements t) b.
Theorem Table.size_elements : Table.size t = List.length (Table.elements t).
Theorem Table.is_empty_spec : Table.wf t -> (Table.is_empty t = true <-> forall k, Table.get k t = None).
(* Proof idea: Map.elements_sound, Map.elements_complete, Map.elements_nodup, Map.fold_elements,
   Map.size_elements and Map.is_empty_spec. Card: COL-2. *)
End TableLaws.
```

## Algorithms and references

- **Tries.** Little-endian radix-2 tries: a key is consumed least-significant bit first, as in
  Okasaki and Gill, "Fast mergeable integer maps" (ML Workshop 1998), but with fixed-depth paths
  and no prefix compression. The seven-shape canonical form makes empty subtrees unrepresentable.
  `Trie.combine` recurses on both tries at once and rebuilds a node only through a smart
  constructor that drops empty children. `Trie.union_with` is Okasaki and Gill's `merge`: a subtree
  present in one trie only is returned as it is. `Trie.forall2` is a short-circuit walk of the
  first trie that follows the second trie only along the paths of the first.
- **Encodings.** An injective code into `positive`, as `Countable` in std++ (Krebbers et al.);
  pairs and lists use a self-delimiting prefix code (doubled bits, then a delimiter).
- **Priority queue.** A rank-position binomial heap ordered by `(priority, code)`. Lowering a
  priority uses lazy deletion: the old entry stays in the heap and `pop` skips an entry that
  disagrees with the live map.
- **Union-find.** Union by rank and path compression (Tarjan, "Efficiency of a good but not linear
  set union algorithm", JACM 1975; Tarjan and van Leeuwen, JACM 1984), made persistent with
  tries in place of arrays (compare Conchon and Filliâtre, "A persistent union-find data
  structure", ML Workshop 2007). The correctness argument follows Charguéraud and Pottier (JAR
  2019),
  stated here on a functional model. `find` takes fuel `S max_rank`, which the rank invariant makes
  sufficient.
- **Tables.** A flat `Map` keyed by `list_encoding positive_encoding`; hash-consing as in
  Filliâtre and Conchon, "Type-safe modular hash-consing", ML Workshop 2006.

## Performance notes

- A trie of `n` bindings whose codes have at most `b` bits has at most `n * b` nodes. Count each
  constructor and branch as a unit operation, separately from work done by supplied functions.
  `Trie.get`, `set` and `remove` cost O(bits of the key); `Trie.combine`, `map`, `beq` and `size`
  cost O(nodes), plus supplied-function work. For two inputs, nodes counts both input tries.
  For `Trie.fold` and `Trie.elements`, let `N` be the number of visited nodes and `L` the sum of
  the bit lengths of the emitted positive keys. Their cost is O(N + L), plus fold callback work.
  `Trie.elements` builds its list with an accumulator (no left-nested append). `Trie.size` is not
  cached; `PQueue.size` is.
- `Trie.forall2` costs at most O(nodes of `t1`) and stops at the first failure; `Trie.union_with`
  costs O(1 + the number of node positions present in both tries), because a one-sided subtree is
  shared in O(1). Both bounds exclude supplied-function work. `FinSet.subset` is one
  `Trie.forall2` (no difference trie is built) and
  `FinSet.union` is one `Trie.union_with`.
- `Map.get`, `set` and `remove` add one `encode`. Prepared index: `Map.wf`, with
  `Map.elements_sound` and `Map.elements_complete` as the agreement lemmas between the trie and the
  key view; `Map.code_get` is the same index read by position.
- With `n` pending heap entries, `PQueue.push` takes O(log(2 + n)) structural heap work and
  O(log(2 + n)) priority/code comparisons, plus a constant number of live-map operations. `pop`
  takes O((1 + d) log(2 + n)) structural heap work and priority/code comparisons, and O(1 + d)
  live-map operations when it discards `d` stale entries, with fuel equal to the entry count.
  Structural work counts constructors and branches; comparison, encoding and live-map costs are
  separate. A positive priority/code comparison may inspect O(bit lengths) bits.
  These are per-call bounds, including on persistent branches, with no amortised bound claimed.
  Prepared index: the live map and counters, with `PQueue.members_spec` and
  `PQueue.size_members` as the agreement lemmas.
- `UnionFind.find` is O(log n) by the rank bound on a single call. Path compression pays off only
  when the client threads the returned structure; `equivb` returns it for that purpose.
- `Table.get` and `Table.set` cost one `encode` of the key plus O(bits of its code). No complexity
  statement in this document is a theorem.

## Open questions

1. **Element order.** `Map.elements` follows `Trie.key_lt` on codes, not the order of keys. A client
   that needs numeric order of keys must sort. Whether to pin the pair and list codes exactly is
   open; pinning makes order portable but forbids improvements.
2. **Added to the anchors:** `Trie.is_empty`, `Map.size/is_empty/mem/of_list/map/beq`,
   `FinSet.is_empty`, `PQueue.priority/members/wf/before`,
   `UnionFind.make/equivb/keys/wf/of_unions`,
   and the `Table` operations. `UnionFind.keys` exists for the join of equality partitions (DOM-7).
3. **`Map.t` stores each key** beside its value so that `elements` needs no decoder. The cost is one
   extra word per binding; the alternative is an `encoding` with a decode function.
4. **Lazy deletion** lets stale heap entries accumulate under many priority decreases; a position
   map for a true decrease-key would avoid it at higher proof cost.

## Cross-document contracts

The collection modules are `Map`, `FinSet`, `PQueue`, `UnionFind` and `Table`.
`UnionFind.keys` takes its encoding, and its support and union laws require well-formedness.
Order uses the position-level map API and the trie-based set operations.

## AUD-COST-BASE: Shared source-event vocabulary

`Galois.Collections.CollectionsAuditCost` owns these new declarations. The tags and folds
alone establish no source correspondence or performance claim. Each source family specifies
its fixed source-site identifiers, typed calls and strict execution relation, and proves its
projection to the actual operation. A truly external opaque callback body is counted only by
an explicitly proved client adapter; internal library calls are included in the relation.
The following theorem statements are future proof obligations.

The source boundary contains proof-erased computational data. It charges data decisions,
recursive control, actual key operands, internal callback bodies and produced output. Laws and
termination evidence used only in `Prop` do not contribute computational work. The mathematical
observer's evaluation is separate from the represented algorithm. An implementation that creates
logs or counters as ordinary data includes their construction in its source account.

The abstract source evaluator uses left-to-right call by value for otherwise unsequenced
application arguments. Explicit lets, branches and elaborated pattern matches retain their own
sequencing and skipped branches. Trace order describes this evaluator; it does not prescribe VM,
extraction or native evaluation order.

Each family fixes its source equations and local block allowances. A whole-operation bound uses
input dimensions or a specified recurrence over the same execution's intermediate states. A
selected event count or a sum of unbounded primitive work does not establish that bound. Supplied
callbacks have separate per-call source and budget laws; library-created callbacks use their fixed
internal bodies. These abstract costs do not claim kernel, VM, extraction or native execution time.

```rocq
(** * Audit event vocabulary

    This declaration-only proposal gives source-operation counters a shared vocabulary.
    For example, a case inspection and an external call contribute two events.
    Builds on: Rocq Stdlib. *)

From Stdlib.Lists Require Import List.
From Stdlib.NArith Require Import NArith.
From Stdlib.PArith Require Import PArith.
From Stdlib.ZArith Require Import ZArith.
Import List.ListNotations.

(** Events retain a fixed source site and, for calls, the typed actual call record. *)
Polymorphic Inductive audit_event (Call : Type) : Type :=
  | AuditCase (site : nat) (operands : list N)
  | AuditCall (call : Call)
  | AuditConstruct (site : nat) (operands : list N)
  | AuditKeyBit (bit : bool)
  | AuditArithmetic (site : nat) (operands : list N).

Arguments AuditCase {Call} _ _.
Arguments AuditCall {Call} _.
Arguments AuditConstruct {Call} _ _.
Arguments AuditKeyBit {Call} _.
Arguments AuditArithmetic {Call} _ _.

Polymorphic Definition audit_trace (Call : Type) : Type := list (audit_event Call).

(** This count is the number of modeled source events, including callback invocations. *)
Polymorphic Definition audit_work {Call} (events : audit_trace Call) : nat := List.length events.

(** Collect calls in their source order, with their actual operands in the call type. *)
Fixpoint audit_calls {Call} (events : audit_trace Call) : list Call :=
  match events with
  | nil => nil
  | AuditCall call :: rest => call :: audit_calls rest
  | _ :: rest => audit_calls rest
  end.

(** Count key-bit events independently of other modeled source events. *)
Fixpoint audit_key_bits {Call} (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditKeyBit _ :: rest => S (audit_key_bits rest)
  | _ :: rest => audit_key_bits rest
  end.

(** Count case inspections at the specified concrete source site. *)
Polymorphic Fixpoint audit_case_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditCase current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_case_count site rest
  | _ :: rest => audit_case_count site rest
  end.

(** Count constructions at the specified concrete source site. *)
Fixpoint audit_construct_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditConstruct current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_construct_count site rest
  | _ :: rest => audit_construct_count site rest
  end.

(** Count arithmetic frames at the specified concrete source site. *)
Fixpoint audit_arithmetic_count {Call} (site : nat) (events : audit_trace Call) : nat :=
  match events with
  | nil => 0
  | AuditArithmetic current _ :: rest =>
      (if Nat.eqb site current then 1 else 0) + audit_arithmetic_count site rest
  | _ :: rest => audit_arithmetic_count site rest
  end.

(** Work is additive for two consecutive source trace segments. *)
Theorem audit_work_app :
  forall Call (left right : audit_trace Call),
    audit_work (left ++ right) = audit_work left + audit_work right.

(** Callback calls retain their chronological order across source trace segments. *)
Theorem audit_calls_app :
  forall Call (left right : audit_trace Call),
    audit_calls (left ++ right) = audit_calls left ++ audit_calls right.

(** Key-bit count is additive across source trace segments. *)
Theorem audit_key_bits_app :
  forall Call (left right : audit_trace Call),
    audit_key_bits (left ++ right) = audit_key_bits left + audit_key_bits right.

(** Case counts are additive across source trace segments. *)
Theorem audit_case_count_app :
  forall Call site (left right : audit_trace Call),
    audit_case_count site (left ++ right) =
      audit_case_count site left + audit_case_count site right.

(** Construction counts are additive across source trace segments. *)
Theorem audit_construct_count_app :
  forall Call site (left right : audit_trace Call),
    audit_construct_count site (left ++ right) =
      audit_construct_count site left + audit_construct_count site right.

(** Arithmetic frame counts are additive across source trace segments. *)
Theorem audit_arithmetic_count_app :
  forall Call site (left right : audit_trace Call),
    audit_arithmetic_count site (left ++ right) =
      audit_arithmetic_count site left + audit_arithmetic_count site right.
```

## Fixed abstract primitive weights

The following definitions are owned by AUD-COST-BASE in the same module as
`audit_event`. They define positive, deterministic abstract charges; they do
not assert native timing or a bound on the pinned primitive source. Each actual
call uses its real operands and any internal callback body is counted by its
own source-family model. AUD-CL owns future trie and encoding implementation
adequacy propositions; the numeric families own the arithmetic bridges.
Those proofs are library obligations, never caller-provided cost laws.

```rocq
(** These fixed weights define an abstract operation model, not native work. *)
Definition audit_z_bits (z : Z) : nat := S (Z.to_nat (Z.log2 (Z.abs z))).

Definition audit_key_bits_weight (key : positive) : nat := Pos.size_nat key.

Definition audit_get_weight (key : positive) : nat := 1 + audit_key_bits_weight key.

Definition audit_set_weight (key : positive) : nat := 1 + 2 * audit_key_bits_weight key.

Definition audit_remove_weight (key : positive) : nat := 1 + 2 * audit_key_bits_weight key.

Definition audit_encoding_weight (emitted_bits : nat) : nat := S emitted_bits.

Definition audit_binary_weight (x y : Z) : nat := 1 + audit_z_bits x + audit_z_bits y.

Definition audit_multiply_weight (x y : Z) : nat := 1 + audit_z_bits x * audit_z_bits y.

Definition audit_divide_weight (x y : Z) : nat :=
  1 + (audit_z_bits x + audit_z_bits y) * (audit_z_bits x + audit_z_bits y).

Definition audit_shift_weight (x amount : Z) : nat :=
  1 + audit_z_bits x + Z.to_nat (Z.abs amount).

Definition audit_unary_conversion_weight (converted : nat) : nat := S converted.
```

## Signed operands in audit events

Card: AUD-COST-BASE. `CollectionsAuditCost.v` also owns these definitions. Numeric families use
them without importing analysis algorithms. Their signed-encoding correctness proof belongs to
AUD-SM-COUNT.

```rocq
(** Encode a signed operand in the natural-valued event payload. *)
Definition count_zencode (z : Z) : N :=
  match z with
  | Z0 => 0%N
  | Zpos p => N.double (N.pos p)
  | Zneg p => N.pred (N.double (N.pos p))
  end.

(** Recover the signed operand represented by an event payload. *)
Definition count_zdecode (n : N) : Z :=
  if N.even n then Z.of_N (N.div2 n)
  else (- Z.of_N (N.succ (N.div2 n)))%Z.

(** Record the two actual signed operands of an arithmetic source site. *)
Definition scalar_z (site : nat) (a b : Z) : audit_event unit :=
  AuditArithmetic site [count_zencode a; count_zencode b].
```

<!-- AUD-API-CL-BEGIN -->

## Exact collection source contracts

Module sections fix the definitions, equations and exact future theorem types.
Definition cards install the model bodies; the named proof leaves prove their claims.
Compilation of a proposition is distinct from a proof. Actual callback bodies and
input or same-execution intermediate dimensions follow the shared source boundary.

## CollectionsAuditAdapted

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditAdapted.v`.

Public module:
`Galois.Collections.CollectionsAuditAdapted`.

```rocq
(** * Adapted complete source bounds

    These compositions require actual source/body laws only for genuine foreign callbacks.
    For example, saved predecessor reads remain concrete library calls with no foreign price law.
    Builds on: complete input recurrences and the shared actual-call adapter. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Collections Require Import CollectionsAuditEncoderBudget.
From Galois.Collections Require Import CollectionsAuditUnionFindWhole.
From Galois.Collections Require Import CollectionsAuditUnionFind.
From Galois.Collections Require Import CollectionsAuditUnionFindAdapters.
From Galois.Collections Require Import CollectionsAuditEncoding.
Import List.ListNotations.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_whole_input_bound_adapted_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget enc_source,
    audit_external_callback_adapter enc work enc_source budget ->
    (forall fuel key forest,
      audit_uf_source_work work (snd (audit_uf_find_fuel enc fuel key forest)) <=
        audit_uf_find_input_budget enc budget fuel key forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_union enc x y forest)) <=
        audit_uf_union_input_budget enc budget x y forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_equivb enc x y forest)) <=
        audit_uf_equivb_input_budget enc budget x y forest) /\
    (forall actions forest,
      audit_uf_source_work work (snd (audit_uf_history enc actions forest)) <=
        audit_uf_history_input_budget enc budget actions forest).

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_pair_whole_input_bound_adapted_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget inputs first_source second_source,
    audit_external_callback_adapter first first_work first_source first_budget ->
    audit_external_callback_adapter second second_work second_source second_budget ->
    let enc := audit_uf_pair_encode first second in
    let budget := audit_pair_input_budget first second first_budget second_budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_pair_encoder_work first_work second_work)
      (snd (audit_uf_pair_of_unions first second inputs)) <=
      audit_uf_history_input_budget enc budget actions UnionFind.make.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_list_whole_input_bound_adapted_statement : Prop :=
  forall A CE (element : A -> positive * list CE) work budget inputs element_source,
    audit_external_callback_adapter element work element_source budget ->
    let enc := audit_uf_list_encode element in
    let key_budget := audit_list_input_budget element budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_list_encoder_work work)
      (snd (audit_uf_list_of_unions element inputs)) <=
      audit_uf_history_input_budget enc key_budget actions UnionFind.make.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_uf_branches_whole_input_bound_adapted_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget left right forest enc_source,
    audit_external_callback_adapter enc work enc_source budget ->
    let branches := audit_uf_branches enc left right forest in
    audit_uf_source_work work (snd (fst branches)) +
      audit_uf_source_work work (snd (snd branches)) <=
    audit_uf_history_input_budget enc budget left forest +
      audit_uf_history_input_budget enc budget right forest.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_pair_input_bound_adapted_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget key first_source second_source,
    audit_external_callback_adapter first first_work first_source first_budget ->
    audit_external_callback_adapter second second_work second_source second_budget ->
    audit_pair_events_work first_work second_work (snd (audit_pair_encode first second key)) <=
      audit_pair_input_budget first second first_budget second_budget key.

(** Genuine foreign source laws bind the actual retained inputs, results and bodies. *)
Definition audit_list_input_bound_adapted_statement : Prop :=
  forall A CE (element : A -> positive * list CE) element_work element_budget keys element_source,
    audit_external_callback_adapter element element_work element_source element_budget ->
    audit_list_events_work element_work (snd (audit_list_encode element keys)) <=
      audit_list_input_budget element element_budget keys.
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditAdaptedENCAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditAdapted.

Theorem audit_pair_input_bound_adapted : audit_pair_input_bound_adapted_statement.
Theorem audit_list_input_bound_adapted : audit_list_input_bound_adapted_statement.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditAdaptedUFAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditAdapted.

Theorem audit_uf_whole_input_bound_adapted : audit_uf_whole_input_bound_adapted_statement.
Theorem audit_uf_pair_whole_input_bound_adapted : audit_uf_pair_whole_input_bound_adapted_statement.
Theorem audit_uf_list_whole_input_bound_adapted : audit_uf_list_whole_input_bound_adapted_statement.
Theorem audit_uf_branches_whole_input_bound_adapted :
  audit_uf_branches_whole_input_bound_adapted_statement.
```

## CollectionsAuditCallback

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditCallback.v`.

Public module:
`Galois.Collections.CollectionsAuditCallback`.

```rocq
(** * Actual foreign callback source adapters

    These laws connect each genuine foreign call's argument, result and retained body to source
      work.
    For example, an operand call retains its exact node and incoming key before its input budget
      applies.
    Builds on: Rocq Stdlib lists. *)

From Stdlib Require Import List.

(** Foreign clients justify their own bodies; this relation cannot price an internal library
  call. *)
Record audit_external_callback_adapter {A R B : Type} (call : A -> R * list B)
    (work : list B -> nat) (source : A -> R -> list B -> nat -> Prop)
    (budget : A -> nat) : Prop := AuditExternalCallbackAdapter {
  audit_external_callback_source : forall argument result body,
    call argument = (result, body) -> source argument result body (work body);
  audit_external_callback_input_bound : forall argument result body,
    call argument = (result, body) -> work body <= budget argument
}.

(** Every observed call is charged at the same returned body and actual input. *)
Definition audit_external_callback_observed_statement : Prop :=
  forall A R B (call : A -> R * list B) work source budget,
    audit_external_callback_adapter call work source budget ->
    forall argument,
      source argument (fst (call argument)) (snd (call argument)) (work (snd (call argument))) /\
      work (snd (call argument)) <= budget argument.
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditCallbackAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditCallback.

Theorem audit_external_callback_observed : audit_external_callback_observed_statement.
```

## CollectionsAuditCompare

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditCompare.v`.

Public module:
`Galois.Collections.CollectionsAuditCompare`.

```rocq
(** * Counted positive ordering comparisons

    The counted clauses follow the pinned [Pos.compare_cont] source and retain the
    accumulator, operands and returned comparison at every recursive frame.  For
    example, comparing two differently tagged nonterminal bits still recurses.
    Builds on: the standard positive-number implementation. *)

From Stdlib Require Import List PArith.
Import List.ListNotations.

(** One event records an actual comparison frame and its result. *)
Inductive audit_positive_compare_event : Type :=
  | AuditPositiveCompare (acc : comparison) (left right : positive)
      (result : comparison).

(** [Pos.compare_cont] recurses whenever both inputs are nonterminal. *)
Fixpoint audit_positive_compare_cont (acc : comparison) (left right : positive)
    {struct right} : comparison * list audit_positive_compare_event :=
  match left, right with
  | xI l, xI r | xO l, xO r =>
      let '(result, events) := audit_positive_compare_cont acc l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xI l, xO r =>
      let '(result, events) := audit_positive_compare_cont Gt l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xO l, xI r =>
      let '(result, events) := audit_positive_compare_cont Lt l r in
      (result, AuditPositiveCompare acc left right result :: events)
  | xH, xH => (acc, [AuditPositiveCompare acc left right acc])
  | xH, _ => (Lt, [AuditPositiveCompare acc left right Lt])
  | _, xH => (Gt, [AuditPositiveCompare acc left right Gt])
  end.

(** The public ordering wrappers inspect the returned comparison once. *)
Definition audit_positive_compare (left right : positive)
    : comparison * list audit_positive_compare_event :=
  audit_positive_compare_cont Eq left right.

Definition audit_positive_ltb (left right : positive)
    : bool * list audit_positive_compare_event :=
  let '(result, events) := audit_positive_compare left right in
  (match result with Lt => true | _ => false end, events).

Definition audit_positive_leb (left right : positive)
    : bool * list audit_positive_compare_event :=
  let '(result, events) := audit_positive_compare left right in
  (match result with Gt => false | _ => true end, events).

(** Two selected source inspection frames per recursive comparison event. *)
Definition audit_positive_compare_source_work
    (events : list audit_positive_compare_event) : nat :=
  2 * length events.

(** Ordering wrappers add their fixed entry and comparison-result branches. *)
Definition audit_positive_order_source_work
    (events : list audit_positive_compare_event) : nat :=
  4 + audit_positive_compare_source_work events.

(** These are future source-card proofs, not assertions established by elaboration. *)
Definition audit_positive_compare_cont_statement : Prop :=
  forall acc left right,
    let '(result, events) := audit_positive_compare_cont acc left right in
    result = Pos.compare_cont acc left right /\
    audit_positive_compare_source_work events <=
      2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).

Definition audit_positive_compare_statement : Prop :=
  forall left right,
    fst (audit_positive_compare left right) = Pos.compare left right.

Definition audit_positive_order_statement : Prop :=
  forall left right,
    fst (audit_positive_ltb left right) = Pos.ltb left right /\
    fst (audit_positive_leb left right) = Pos.leb left right /\
    audit_positive_order_source_work (snd (audit_positive_ltb left right)) <=
      4 + 2 * Nat.min (Pos.size_nat left) (Pos.size_nat right) /\
    audit_positive_order_source_work (snd (audit_positive_leb left right)) <=
      4 + 2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).

Example audit_positive_compare_different_tags :
  (fst (audit_positive_ltb 2%positive 3%positive),
   length (snd (audit_positive_compare 2%positive 3%positive))) = (true, 2).
Proof. reflexivity. Qed.
```

Card: AUD-CL-TRIE

Future proof module: `Galois.Collections.CollectionsAuditCompareAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditCompare.

Theorem audit_positive_compare_cont : audit_positive_compare_cont_statement.
Theorem audit_positive_compare : audit_positive_compare_statement.
Theorem audit_positive_order : audit_positive_order_statement.
```

## CollectionsAuditComposite

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditComposite.v`.

Public module:
`Galois.Collections.CollectionsAuditComposite`.

```rocq
(** Historical selected structural observations, separate from source adequacy.

    Callback prices here are abstract observations. Actual library component bodies are
    accounted by the concrete source-shaped models in CollectionsAuditEncoding. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Collections Require Import CollectionsAuditState.

Record composite_costs (A B : Type) : Type := CompositeCosts {
  composite_left_encode : A -> nat;
  composite_right_encode : B -> nat
}.
Arguments composite_left_encode {A B}.
Arguments composite_right_encode {A B}.

Record composite_cost_laws {A B} (observed bound : composite_costs A B) : Prop := {
  composite_left_bound : forall a, composite_left_encode observed a <= composite_left_encode bound
    a;
  composite_right_bound : forall b, composite_right_encode observed b <= composite_right_encode
    bound b
}.

Record composite_pair_work : Type := CompositePairWork {
  composite_left_bits : nat;
  composite_right_bits : nat;
  composite_emitted_bits : nat;
  composite_stream_nodes : nat;
  composite_callback_work : nat
}.

Definition prepared_pair_work {A B} (EA : encoding A) (EB : encoding B)
    (cost : composite_costs A B) (a : A) (b : B) : composite_pair_work :=
  let left := Pos.size_nat (encode EA a) in
  let right := Pos.size_nat (encode EB b) in
  CompositePairWork left right (2 * left + 2 * right) (S (2 * left + 2 * right))
    (composite_left_encode cost a + composite_right_encode cost b).

Definition prepared_pair_work_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (cost : composite_costs A B) a b,
    let work := prepared_pair_work EA EB cost a b in
    composite_stream_nodes work = Pos.size_nat (key_code (prepare_key (pair_encoding EA EB)
      (a,b))) /\
    composite_emitted_bits work = 2 * composite_left_bits work + 2 * composite_right_bits work /\
    composite_callback_work work = composite_left_encode cost a + composite_right_encode cost b.

Record composite_list_costs (A : Type) : Type := CompositeListCosts {
  composite_element_encode : A -> nat
}.
Arguments composite_element_encode {A}.
Record composite_list_cost_laws {A} (observed bound : composite_list_costs A) : Prop := {
  composite_element_bound : forall a, composite_element_encode observed a <=
    composite_element_encode bound a
}.
Record composite_list_work : Type := CompositeListWork {
  composite_list_elements : nat;
  composite_list_input_bits : nat;
  composite_list_emitted_bits : nat;
  composite_list_stream_nodes : nat;
  composite_list_callbacks : nat
}.
Definition prepared_list_work {A} (EA : encoding A) (cost : composite_list_costs A) (xs : list A) :
    composite_list_work :=
  let bits := fold_right (fun a total => Pos.size_nat (encode EA a) + total) 0 xs in
  CompositeListWork (length xs) bits (2 * bits) (S (2 * bits))
    (fold_right (fun a total => composite_element_encode cost a + total) 0 xs).
Definition prepared_list_work_statement : Prop :=
  forall A (EA : encoding A) (cost : composite_list_costs A) xs,
    let work := prepared_list_work EA cost xs in
    composite_list_stream_nodes work = Pos.size_nat (key_code (prepare_key (list_encoding EA) xs))
      /\
    composite_list_elements work = length xs /\
    composite_list_emitted_bits work = 2 * composite_list_input_bits work /\
    composite_list_callbacks work = fold_right (fun a total => composite_element_encode cost a +
      total) 0 xs.
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditCompositeAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditComposite.

Theorem prepared_pair_work : prepared_pair_work_statement.
Theorem prepared_list_work : prepared_list_work_statement.
```

## CollectionsAuditContracts

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditContracts.v`.

Public module:
`Galois.Collections.CollectionsAuditContracts`.

```rocq
(** * Collection audit contract groups

    These proposition groups retain the prepared-key, dense-slot and persistent-forest claims.
    For example, bounded-slot refinement includes both conversion directions and removal.
    Builds on: G4 semantic contracts and the source-shaped collection observers. *)

From Galois.Collections Require Import CollectionsAuditState.
From Galois.Collections Require Import CollectionsAuditPrepared.
From Galois.Collections Require Import CollectionsAuditDense.
From Galois.Collections Require Import CollectionsAuditDenseSlots.
From Galois.Collections Require Import CollectionsAuditUnionFind.
From Galois.Collections Require Import CollectionsAuditComposite.
From Galois.Collections Require Import CollectionsAuditHistorical.

(** Key reuse retains injection, update and exact composite bit-length statements. *)
Definition prepared_key_refines_contract : Prop :=
  prepare_key_valid_statement /\ prepared_key_refinement_statement /\
  prepared_key_injection_statement /\ prepared_key_update_statement /\ prepared_pair_statement /\
  prepared_list_injection_statement /\ prepared_pair_bits_statement /\
    prepared_list_bits_statement /\
  prepared_pair_work_statement /\ prepared_list_work_statement /\
  audit_prepare_key_erases_statement /\ audit_prepared_lookup_erases_statement /\
  audit_prepared_update_erases_statement /\ audit_prepared_remove_erases_statement /\
  audit_prepared_encoder_reuse_statement /\ audit_prepared_lookup_source_bound_statement /\
  audit_prepared_update_source_bound_statement /\ audit_prepared_remove_source_bound_statement.

(** Dense-map refinement includes all original in/outside, canonicity and batch observations. *)
Definition dense_map_refines_contract : Prop :=
  slot_empty_statement /\ slot_update_statement /\ slot_present_update_statement /\
  slot_elements_statement /\ slot_canonical_statement /\ slot_to_map_statement /\
  slot_of_map_statement /\ slot_prepare_statement /\ slot_outside_statement /\
  slot_batch_refinement_statement /\ slot_update_refines_statement /\
    slot_remove_refines_statement /\
  slot_remove_frame_statement /\ slot_remove_outside_statement /\ slot_elements_refines_statement /\
  dense_token_prepare_statement /\ dense_token_read_statement /\ dense_token_scope_statement /\
  slot_batch_cost_statement /\ audit_read_slots_observation_statement /\
  audit_dense_prepare_erases_statement /\
  audit_dense_prepare_source_bound_statement /\ audit_slot_lookup_erases_statement /\
  audit_slot_update_erases_statement /\ audit_slot_remove_erases_statement /\
  audit_slot_elements_erases_statement /\ audit_slot_to_map_erases_statement /\
  audit_slot_of_map_erases_statement /\ audit_slot_elements_source_bound_statement /\
  audit_slot_to_map_source_bound_statement /\ audit_slot_of_map_source_bound_statement /\
  audit_dense_token_prepare_erases_statement /\ audit_dense_token_read_erases_statement /\
  audit_dense_token_prepare_source_bound_statement /\ audit_dense_token_read_source_bound_statement.

(** Source results and independently started branches are stated separately from native
  allocation. *)
Definition union_find_cost_contract : Prop :=
  trace_find_result_statement /\ trace_union_result_statement /\ trace_actions_result_statement /\
  trace_branch_sum_statement /\ union_source_work_statement /\
  audit_uf_find_fuel_erases_statement /\ audit_uf_find_erases_statement /\
  audit_uf_union_erases_statement /\ audit_uf_equivb_erases_statement /\
    audit_uf_keys_erases_statement /\
  audit_uf_history_erases_statement /\ audit_uf_of_unions_erases_statement /\
  audit_uf_find_fuel_count_statement /\ audit_uf_union_count_statement /\
    audit_uf_equivb_count_statement /\
  audit_uf_find_fuel_work_bound_statement /\ audit_uf_union_work_bound_statement /\
  audit_uf_equivb_work_bound_statement /\ audit_uf_keys_input_bound_statement /\
  audit_uf_history_bound_statement /\ audit_uf_branches_bound_statement /\
  audit_uf_of_unions_source_bound_statement.
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditContractsDENSEAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditContracts.

Theorem prepared_key_refines_contract_holds : prepared_key_refines_contract.
Theorem dense_map_refines_contract_holds : dense_map_refines_contract.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditContractsUFAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditContracts.

Theorem union_find_cost_contract_holds : union_find_cost_contract.
```

## CollectionsAuditDense

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditDense.v`.

Public module:
`Galois.Collections.CollectionsAuditDense`.

```rocq
(** * Counted dense universe preparation

    This observer retains each distinctness probe, index insertion and numeric conversion.
    For example, a repeated key is probed twice but numbered only once.
    Builds on: CollectionsDenseSet and shared collection cost models. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Collections Require Import CollectionsAuditFinSet.
Import List.ListNotations.

(** * Original numeric conversion cases *)

Inductive audit_dense_numeric_event : Type :=
  | AuditDenseBinarySuccessor (input output : N) (events : list audit_n_encoding_event)
  | AuditDenseLengthConversion (input : nat) (output : N) (events : list audit_nat_encoding_event).

(** [N.succ] and [N.succ_pos] share the same positive carry computation. *)
Definition audit_dense_N_succ (input : N) : N * list audit_dense_numeric_event :=
  let '(p, events) := audit_N_encode input in
  (Npos p, [AuditDenseBinarySuccessor input (Npos p) events]).

(** [N.of_nat] inspects zero or invokes [Pos.of_succ_nat] on the predecessor. *)
Definition audit_dense_N_of_nat (input : nat) : N * list audit_dense_numeric_event :=
  match input with
  | 0 => (N0, [AuditDenseLengthConversion input N0 []])
  | S rest =>
      let '(p, events) := audit_nat_encode rest in
      (Npos p, [AuditDenseLengthConversion input (Npos p) events])
  end.

Definition audit_dense_N_succ_erases_statement : Prop :=
  forall input, fst (audit_dense_N_succ input) = N.succ input.

Definition audit_dense_N_of_nat_erases_statement : Prop :=
  forall input, fst (audit_dense_N_of_nat input) = N.of_nat input.

(** * First-occurrence selection and position indexing *)

Inductive audit_dense_prepare_event (K CE : Type) : Type :=
  | AuditDenseUniqueCase (remaining : list K) (seen : FinSet.t K)
  | AuditDenseUniqueProbe (key : K) (found : bool) (calls : list (audit_set_event K CE))
  | AuditDenseUniqueAdd (key : K) (calls : list (audit_set_event K CE))
  | AuditDenseUniqueKeep (key : K)
  | AuditDenseNumberCase (remaining : list K) (index : N)
  | AuditDenseNumberNext (input output : N) (events : list audit_dense_numeric_event)
  | AuditDenseNumberStore (key : K) (index : N) (calls : list (audit_map_event K N CE))
  | AuditDenseLength (input : nat) (output : N) (events : list audit_dense_numeric_event).

Arguments AuditDenseUniqueCase {K CE} _ _.
Arguments AuditDenseUniqueProbe {K CE} _ _ _.
Arguments AuditDenseUniqueAdd {K CE} _ _.
Arguments AuditDenseUniqueKeep {K CE} _.
Arguments AuditDenseNumberCase {K CE} _ _.
Arguments AuditDenseNumberNext {K CE} _ _ _.
Arguments AuditDenseNumberStore {K CE} _ _ _.
Arguments AuditDenseLength {K CE} _ _ _.

(** Duplicates retain the original seen set and do not issue an insertion. *)
Fixpoint audit_dense_unique {K CE} (enc : K -> positive * list CE) (seen : FinSet.t K)
    (keys : list K) : list K * list (audit_dense_prepare_event K CE) :=
  match keys with
  | [] => ([], [AuditDenseUniqueCase keys seen])
  | key :: rest =>
      let '(found, probes) := audit_finset_mem enc key seen in
      if found then
        let '(unique, events) := audit_dense_unique enc seen rest in
        (unique, [AuditDenseUniqueCase keys seen; AuditDenseUniqueProbe key found probes] ++ events)
      else
        let '(next, adds) := audit_finset_add enc key seen in
        let '(unique, events) := audit_dense_unique enc next rest in
        (key :: unique, [AuditDenseUniqueCase keys seen; AuditDenseUniqueProbe key found probes;
                         AuditDenseUniqueAdd key adds; AuditDenseUniqueKeep key] ++ events)
  end.

(** Numbering calls [N.succ] before the recursive tail and writes the map on return. *)
Fixpoint audit_dense_number {K CE} (enc : K -> positive * list CE) (keys : list K) (index : N)
    : Map.t K N * list (audit_dense_prepare_event K CE) :=
  match keys with
  | [] => (Map.empty, [AuditDenseNumberCase keys index])
  | key :: rest =>
      let '(next, ne) := audit_dense_N_succ index in
      let '(tail, te) := audit_dense_number enc rest next in
      let '(out, se) := audit_map_set enc key index tail in
      (out, [AuditDenseNumberCase keys index; AuditDenseNumberNext index next ne] ++ te ++
        [AuditDenseNumberStore key index se])
  end.

Definition audit_dense_prepare {K CE} (enc : K -> positive * list CE) (keys : list K)
    : dense_universe K * list (audit_dense_prepare_event K CE) :=
  let '(unique, ue) := audit_dense_unique enc FinSet.empty keys in
  let '(index, ie) := audit_dense_number enc unique 0%N in
  let '(length, le) := audit_dense_N_of_nat (List.length unique) in
  (DenseUniverse K unique index length, ue ++ ie ++ [AuditDenseLength (List.length unique) length
    le]).

(** * Future exact source-result obligations *)

Definition audit_dense_unique_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) seen keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_unique enc seen keys) = dense_unique original seen keys.

Definition audit_dense_number_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) keys index,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_number enc keys index) = dense_number original keys index.

Definition audit_dense_prepare_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (audit_dense_prepare enc keys) = dense_prepare original keys.

(** * Fixed source charges and original-input preparation budget *)

Fixpoint audit_dense_prepare_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_dense_prepare_event K CE)) : nat :=
  match events with
  | [] => 0
  | AuditDenseUniqueCase _ _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueProbe _ _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueAdd _ calls :: rest => audit_finset_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseUniqueKeep _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberCase _ _ :: rest => 1 + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberNext _ _ calls :: rest =>
      2 + (match calls with
           | [AuditDenseBinarySuccessor _ _ sub] => audit_N_encoding_work sub
           | _ => 0
           end) + audit_dense_prepare_work enc_work rest
  | AuditDenseNumberStore _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_dense_prepare_work enc_work rest
  | AuditDenseLength input _ calls :: rest =>
      2 + input + (match calls with
                   | [AuditDenseLengthConversion _ _ sub] => audit_nat_events_work sub
                   | _ => 0
                   end) + audit_dense_prepare_work enc_work rest
  end.

Fixpoint audit_dense_unique_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 10 + 2 * enc_work (snd (enc key)) + 21 * Pos.size_nat (fst (enc key)) +
      audit_dense_unique_budget enc enc_work rest
  end.

Fixpoint audit_dense_number_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) (index : N) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      let '(next, ne) := audit_dense_N_succ index in
      5 + (match ne with
           | [AuditDenseBinarySuccessor _ _ sub] => audit_N_encoding_work sub
           | _ => 0
           end) + enc_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
        audit_dense_number_budget enc enc_work rest next
  end.

Definition audit_dense_prepare_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  let unique := fst (audit_dense_unique enc FinSet.empty keys) in
  let converted := audit_dense_N_of_nat (List.length unique) in
  audit_dense_unique_budget enc enc_work keys + audit_dense_number_budget enc enc_work unique 0%N +
    2 + List.length unique +
    (match snd converted with
     | [AuditDenseLengthConversion _ _ sub] => audit_nat_events_work sub
     | _ => 0
     end).

Definition audit_dense_prepare_source_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work keys,
    audit_dense_prepare_work enc_work (snd (audit_dense_prepare enc keys)) <=
      audit_dense_prepare_budget enc enc_work keys.
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditDenseAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditDense.

Theorem audit_dense_N_succ_erases : audit_dense_N_succ_erases_statement.
Theorem audit_dense_N_of_nat_erases : audit_dense_N_of_nat_erases_statement.
Theorem audit_dense_unique_erases : audit_dense_unique_erases_statement.
Theorem audit_dense_number_erases : audit_dense_number_erases_statement.
Theorem audit_dense_prepare_erases : audit_dense_prepare_erases_statement.
Theorem audit_dense_prepare_source_bound : audit_dense_prepare_source_bound_statement.
```

## CollectionsAuditDenseInput

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditDenseInput.v`.

Public module:
`Galois.Collections.CollectionsAuditDenseInput`.

```rocq
(** * Whole dense and prepared-key input budgets

    These recurrences close every internal binary and unary encoder at its original operand.
    For example, a successful conversion pays both probes and its fixed numeric slot write.
    Builds on: dense source bodies, concrete encoder budgets and actual foreign callback
      adapters. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsDenseSet.
From Galois.Collections Require Import CollectionsAuditState.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditEncoderBudget.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Collections Require Import CollectionsAuditPrepared.
From Galois.Collections Require Import CollectionsAuditDense.
From Galois.Collections Require Import CollectionsAuditDenseSlots.
Import List.ListNotations.

Fixpoint audit_dense_unique_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 10 + 2 * encoder_budget key + 21 * Pos.size_nat (fst (enc key)) +
      audit_dense_unique_input_budget enc encoder_budget rest
  end.

Fixpoint audit_dense_number_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) (index : N) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      let next := N.succ index in
      5 + audit_N_input_budget index + encoder_budget key + 16 * Pos.size_nat (fst (enc key)) +
        audit_dense_number_input_budget enc encoder_budget rest next
  end.

Definition audit_dense_prepare_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  let unique := fst (audit_dense_unique enc FinSet.empty keys) in
  audit_dense_unique_input_budget enc encoder_budget keys + audit_dense_number_input_budget enc
    encoder_budget unique 0%N +
    2 + List.length unique +
    (match length unique with 0 => 0 | S rest => audit_nat_input_budget rest end).

Definition audit_slot_key_get_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (key : K) : nat :=
  6 + encoder_budget key + 5 * Pos.size_nat (fst (enc key)).

Definition audit_slot_index_get_input_budget (index : N) : nat :=
  6 + audit_N_input_budget index +
    5 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_index_update_input_budget (index : N) : nat :=
  3 + audit_N_input_budget index +
    16 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_lookup_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_input_budget enc encoder_budget key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_get_input_budget i
    end.

Definition audit_slot_update_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_input_budget enc encoder_budget key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_update_input_budget i
    end.

Fixpoint audit_slot_elements_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 2 + audit_slot_lookup_input_budget enc encoder_budget u key +
      audit_slot_elements_input_budget enc encoder_budget u rest
  end.

Fixpoint audit_slot_of_map_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      1 + 2 * audit_slot_key_get_input_budget enc encoder_budget key +
      (match fst (audit_map_get enc key (dense_index u)) with
       | None => 0
       | Some i => audit_slot_index_update_input_budget i
       end) + audit_slot_of_map_input_budget enc encoder_budget u rest
  end.

Fixpoint audit_slot_bindings_input_budget {K V CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (bindings : list (K * V)) : nat :=
  match bindings with
  | [] => 0
  | (key, _) :: rest => 4 + encoder_budget key + 16 * Pos.size_nat (fst (enc key)) +
      audit_slot_bindings_input_budget enc encoder_budget rest
  end.

Fixpoint audit_prepare_slots_input_budget {K CE} (enc : K -> positive * list CE)
    (encoder_budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 1 + audit_slot_key_get_input_budget enc encoder_budget key +
      audit_prepare_slots_input_budget enc encoder_budget rest
  end.

Fixpoint audit_read_slots_input_budget (slots : list (option N)) : nat :=
  match slots with
  | [] => 1
  | None :: rest => 1 + audit_read_slots_input_budget rest
  | Some index :: rest => 1 + audit_slot_index_get_input_budget index +
    audit_read_slots_input_budget rest
  end.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_prepare_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source keys,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_dense_prepare_work enc_work (snd (audit_dense_prepare enc keys)) <=
      audit_dense_prepare_input_budget enc encoder_budget keys.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_lookup_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_lookup enc u m key)) <=
      audit_slot_lookup_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_update_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key value,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_update enc u m key value)) <=
      audit_slot_update_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_remove_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V) key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_remove enc u m key)) <=
      audit_slot_update_input_budget enc encoder_budget u key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_elements_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_elements enc u m)) <=
      audit_slot_elements_input_budget enc encoder_budget u (dense_keys u).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_of_map_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (abstract :
    Map.t K V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_of_map enc u abstract)) <=
      audit_slot_of_map_input_budget enc encoder_budget u (dense_keys u).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_to_map_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u (m :
    slot_map V),
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (audit_slot_to_map enc u m)) <=
      audit_slot_elements_input_budget enc encoder_budget u (dense_keys u) +
      audit_slot_bindings_input_budget enc encoder_budget (fst (audit_slot_elements enc u m)).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_token_prepare_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source (original :
    encoding K) u key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_dense_token_prepare K V CE enc original u key)) <=
      audit_slot_key_get_input_budget enc encoder_budget key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_dense_token_read_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (original : encoding K) u (token : dense_slot_token original u) (m :
    slot_map V),
    audit_slot_source_work enc_work (snd (@audit_dense_token_read K V CE original u token m)) <=
      audit_slot_index_get_input_budget (dense_token_index token).

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_prepare_slot_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u key,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_prepare_slot K V CE enc u key)) <=
      audit_slot_key_get_input_budget enc encoder_budget key.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_slot_read_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) index,
    audit_slot_source_work enc_work (snd (@audit_slot_read K V CE m index)) <=
      audit_slot_index_get_input_budget index.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_prepare_slots_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work encoder_budget enc_source u keys,
    audit_external_callback_adapter enc enc_work enc_source encoder_budget ->
    audit_slot_source_work enc_work (snd (@audit_prepare_slots K V CE enc u keys)) <=
      audit_prepare_slots_input_budget enc encoder_budget keys.

(** The complete bound closes internal encoders and binds any actual external key body. *)
Definition audit_read_slots_whole_input_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) slots,
    audit_slot_source_work enc_work (snd (@audit_read_slots K V CE m slots)) <=
      audit_read_slots_input_budget slots.

(** Preparing a key pays its sole genuine external encoder call before all later direct trie
  reuse. *)
Definition audit_prepare_key_whole_input_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) work source budget key,
    audit_external_callback_adapter enc work source budget ->
    audit_prepared_source_work work (snd (@audit_prepare_key K V CE enc key)) <= 1 + budget key.
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditDenseInputAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditDenseInput.

Theorem audit_dense_prepare_whole_input_bound : audit_dense_prepare_whole_input_bound_statement.
Theorem audit_slot_lookup_whole_input_bound : audit_slot_lookup_whole_input_bound_statement.
Theorem audit_slot_update_whole_input_bound : audit_slot_update_whole_input_bound_statement.
Theorem audit_slot_remove_whole_input_bound : audit_slot_remove_whole_input_bound_statement.
Theorem audit_slot_elements_whole_input_bound : audit_slot_elements_whole_input_bound_statement.
Theorem audit_slot_of_map_whole_input_bound : audit_slot_of_map_whole_input_bound_statement.
Theorem audit_slot_to_map_whole_input_bound : audit_slot_to_map_whole_input_bound_statement.
Theorem audit_dense_token_prepare_whole_input_bound :
  audit_dense_token_prepare_whole_input_bound_statement.
Theorem audit_dense_token_read_whole_input_bound :
  audit_dense_token_read_whole_input_bound_statement.
Theorem audit_prepare_slot_whole_input_bound : audit_prepare_slot_whole_input_bound_statement.
Theorem audit_slot_read_whole_input_bound : audit_slot_read_whole_input_bound_statement.
Theorem audit_prepare_slots_whole_input_bound : audit_prepare_slots_whole_input_bound_statement.
Theorem audit_read_slots_whole_input_bound : audit_read_slots_whole_input_bound_statement.
Theorem audit_prepare_key_whole_input_bound : audit_prepare_key_whole_input_bound_statement.
```

## CollectionsAuditDenseSlots

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditDenseSlots.v`.

Public module:
`Galois.Collections.CollectionsAuditDenseSlots`.

```rocq
(** * Counted prepared dense-map slots

    These observers retain exact universe lookups, numeric slot accesses and updates.
    For example, an outside key is looked up and rejected without modifying the slot map.
    Builds on: G4 collections semantics and shared map and encoding observers. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsDenseSet.
From Galois.Collections Require Import CollectionsAuditState.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditMap.
Import List.ListNotations.

Inductive audit_slot_event (K V CE : Type) : Type :=
  | AuditSlotUniverseGet (key : K) (index : option N) (calls : list (audit_map_event K N CE))
  | AuditSlotAbstractGet (key : K) (value : option V) (calls : list (audit_map_event K V CE))
  | AuditSlotRead (index : N) (value : option V)
      (calls : list (audit_map_event N V audit_n_encoding_event))
  | AuditSlotWrite (index : N) (value : V) (calls : list (audit_map_event N V
    audit_n_encoding_event))
  | AuditSlotRemove (index : N) (calls : list (audit_map_event N V audit_n_encoding_event))
  | AuditSlotMapWrite (key : K) (value : V) (calls : list (audit_map_event K V CE))
  | AuditSlotCase (remaining : list K)
  | AuditSlotBatchIndex (remaining : list (option N))
  | AuditSlotEmit (key : K) (value : V).

Arguments AuditSlotUniverseGet {K V CE} _ _ _.
Arguments AuditSlotAbstractGet {K V CE} _ _ _.
Arguments AuditSlotRead {K V CE} _ _ _.
Arguments AuditSlotWrite {K V CE} _ _ _.
Arguments AuditSlotRemove {K V CE} _ _.
Arguments AuditSlotMapWrite {K V CE} _ _ _.
Arguments AuditSlotCase {K V CE} _.
Arguments AuditSlotBatchIndex {K V CE} _.
Arguments AuditSlotEmit {K V CE} _ _.

(** Direct prepared-slot lookup retains its one encoded-key map read. *)
Definition audit_prepare_slot {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (key : K) : option N * list (audit_slot_event K V CE) :=
  let '(index, calls) := audit_map_get enc key (dense_index u) in
  (index, [AuditSlotUniverseGet key index calls]).

Definition audit_slot_read {K V CE} (m : slot_map V) (index : N)
    : option V * list (audit_slot_event K V CE) :=
  let '(value, calls) := audit_map_get audit_N_encode index m in
  (value, [AuditSlotRead index value calls]).

(** Slot lookup reads the numeric map only after a successful universe lookup. *)
Definition audit_slot_lookup {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) : option V * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(value, slot_calls) := audit_map_get audit_N_encode i m in
      (value, [AuditSlotUniverseGet key index universe_calls; AuditSlotRead i value slot_calls])
  end.

Definition audit_slot_update {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) (value : V) : option (slot_map V) * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(out, calls) := audit_map_set audit_N_encode i value m in
      (Some out, [AuditSlotUniverseGet key index universe_calls; AuditSlotWrite i value calls])
  end.

Definition audit_slot_remove {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (m : slot_map V) (key : K) : option (slot_map V) * list (audit_slot_event K V CE) :=
  let '(index, universe_calls) := audit_map_get enc key (dense_index u) in
  match index with
  | None => (None, [AuditSlotUniverseGet key index universe_calls])
  | Some i =>
      let '(out, calls) := audit_map_remove audit_N_encode i m in
      (Some out, [AuditSlotUniverseGet key index universe_calls; AuditSlotRemove i calls])
  end.

(** Each key in the source universe is visited, including absent or malformed slots. *)
Fixpoint audit_slot_elements_from {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) (keys : list K)
    : list (K * V) * list (audit_slot_event K V CE) :=
  match keys with
  | [] => ([], [AuditSlotCase keys])
  | key :: rest =>
      let '(value, calls) := audit_slot_lookup enc u m key in
      let '(tail, events) := audit_slot_elements_from enc u m rest in
      match value with
      | None => (tail, AuditSlotCase keys :: calls ++ events)
      | Some v => ((key, v) :: tail, AuditSlotCase keys :: calls ++ AuditSlotEmit key v :: events)
      end
  end.

Definition audit_slot_elements {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) := audit_slot_elements_from enc u m (dense_keys u).

(** Batches preserve order, repeated keys and every optional-slot branch. *)
Fixpoint audit_prepare_slots {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (keys : list K) : list (option N) * list (audit_slot_event K V CE) :=
  match keys with
  | [] => ([], [AuditSlotCase keys])
  | key :: rest =>
      let '(index, calls) := @audit_prepare_slot K V CE enc u key in
      let '(tail, events) := audit_prepare_slots enc u rest in
      (index :: tail, AuditSlotCase keys :: calls ++ events)
  end.

Fixpoint audit_read_slots {K V CE} (m : slot_map V) (slots : list (option N))
    : list (option V) * list (audit_slot_event K V CE) :=
  match slots with
  | [] => ([], [AuditSlotBatchIndex slots])
  | None :: rest =>
      let '(tail, events) := audit_read_slots m rest in
      (None :: tail, AuditSlotBatchIndex slots :: events)
  | Some index :: rest =>
      let '(value, calls) := @audit_slot_read K V CE m index in
      let '(tail, events) := audit_read_slots m rest in
      (value :: tail, AuditSlotBatchIndex slots :: calls ++ events)
  end.

(** Conversion inspects the abstract lookup first and skips the universe read on a miss. *)
Fixpoint audit_slot_of_map_from {K V CE} (enc : K -> positive * list CE) (u : dense_universe K)
    (abstract : Map.t K V) (keys : list K) (state : slot_map V)
    : slot_map V * list (audit_slot_event K V CE) :=
  match keys with
  | [] => (state, [AuditSlotCase keys])
  | key :: rest =>
      let '(value, value_calls) := audit_map_get enc key abstract in
      let prefix := [AuditSlotCase keys; AuditSlotAbstractGet key value value_calls] in
      match value with
      | None =>
          let '(out, events) := audit_slot_of_map_from enc u abstract rest state in
          (out, prefix ++ events)
      | Some v =>
          let '(index, index_calls) := audit_map_get enc key (dense_index u) in
          let prefix := prefix ++ [AuditSlotUniverseGet key index index_calls] in
          match index with
          | None =>
              let '(out, events) := audit_slot_of_map_from enc u abstract rest state in
              (out, prefix ++ events)
          | Some i =>
              let '(next, writes) := audit_map_set audit_N_encode i v state in
              let '(out, events) := audit_slot_of_map_from enc u abstract rest next in
              (out, prefix ++ [AuditSlotWrite i v writes] ++ events)
          end
      end
  end.

Definition audit_slot_of_map {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (abstract : Map.t K V) :=
  audit_slot_of_map_from enc u abstract (dense_keys u) Map.empty.

(** Conversion to a standard map processes each emitted binding in source list order. *)
Fixpoint audit_slot_bindings_to_map {K V CE} (enc : K -> positive * list CE)
    (bindings : list (K * V)) (state : Map.t K V) : Map.t K V * list (audit_slot_event K V CE) :=
  match bindings with
  | [] => (state, [])
  | (key, value) :: rest =>
      let '(next, calls) := audit_map_set enc key value state in
      let '(out, events) := audit_slot_bindings_to_map enc rest next in
      (out, AuditSlotMapWrite key value calls :: events)
  end.

Definition audit_slot_to_map {K V CE} (enc : K -> positive * list CE)
    (u : dense_universe K) (m : slot_map V) : Map.t K V * list (audit_slot_event K V CE) :=
  let '(bindings, first) := audit_slot_elements enc u m in
  let '(result, second) := audit_slot_bindings_to_map enc bindings Map.empty in
  (result, first ++ second).

(** A token records the actual key and index returned by its single universe lookup. *)
Definition audit_dense_token_prepare {K V CE} (enc : K -> positive * list CE)
    (original : encoding K) (u : dense_universe K) (key : K)
    : option (dense_slot_token original u) * list (audit_slot_event K V CE) :=
  let '(index, calls) := audit_map_get enc key (dense_index u) in
  (match index with None => None | Some i => Some (DenseSlotToken key i) end,
    [AuditSlotUniverseGet key index calls]).

Definition audit_dense_token_read {K V CE} (original : encoding K) (u : dense_universe K)
    (token : dense_slot_token original u) (m : slot_map V)
    : option V * list (audit_slot_event K V CE) :=
  let index := dense_token_index token in
  let '(value, calls) := audit_map_get audit_N_encode index m in
  (value, [AuditSlotRead index value calls]).

(** * Future exact-result obligations *)

Definition audit_slot_lookup_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_lookup enc u m key) = slot_lookup original u m key.

Definition audit_prepare_slot_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u key,
    fst (enc key) = encode original key ->
    fst (@audit_prepare_slot K V CE enc u key) = prepare_slot original u key.

Definition audit_slot_read_erases_statement : Prop :=
  forall K V CE (m : slot_map V) index, fst (@audit_slot_read K V CE m index) = slot_read m index.

Definition audit_prepare_slots_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u keys,
    (forall k, In k keys -> fst (enc k) = encode original k) ->
    fst (@audit_prepare_slots K V CE enc u keys) = prepare_slots original u keys.

Definition audit_read_slots_erases_statement : Prop :=
  forall K V CE (m : slot_map V) slots, fst (@audit_read_slots K V CE m slots) = read_slots m slots.

Definition audit_slot_update_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key
    value,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_update enc u m key value) = slot_update original u m key value.

Definition audit_slot_remove_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V) key,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_remove enc u m key) = slot_remove original u m key.

Definition audit_slot_elements_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_elements enc u m) = slot_elements original u m.

Definition audit_slot_of_map_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (abstract : Map.t K V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_of_map enc u abstract) = slot_of_map original u abstract.

Definition audit_slot_to_map_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u (m : slot_map V),
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_slot_to_map enc u m) = slot_to_map original u m.

Definition audit_dense_token_prepare_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) u key,
    fst (enc key) = encode original key ->
    fst (@audit_dense_token_prepare K V CE enc original u key) = dense_token_prepare original u key.

Definition audit_dense_token_read_erases_statement : Prop :=
  forall K V CE (original : encoding K) u (token : dense_slot_token original u) (m : slot_map V),
    fst (@audit_dense_token_read K V CE original u token m) = dense_token_read original u token m.

(** * Fixed nested source work and input-derived operation budgets *)

Fixpoint audit_slot_source_work {K V CE} (enc_work : list CE -> nat)
    (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotUniverseGet _ _ calls :: rest => 1 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotAbstractGet _ _ calls :: rest => 1 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotRead _ _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotWrite _ _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotRemove _ calls :: rest => 1 + audit_map_source_work audit_N_encoding_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotMapWrite _ _ calls :: rest => 2 + audit_map_source_work enc_work calls +
      audit_slot_source_work enc_work rest
  | AuditSlotCase _ :: rest => 1 + audit_slot_source_work enc_work rest
  | AuditSlotBatchIndex _ :: rest => 1 + audit_slot_source_work enc_work rest
  | AuditSlotEmit _ _ :: rest => 1 + audit_slot_source_work enc_work rest
  end.

Definition audit_slot_key_get_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (key : K) : nat :=
  6 + enc_work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).

Definition audit_slot_index_get_budget (index : N) : nat :=
  6 + audit_N_encoding_work (snd (audit_N_encode index)) +
    5 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_index_update_budget (index : N) : nat :=
  3 + audit_N_encoding_work (snd (audit_N_encode index)) +
    16 * Pos.size_nat (fst (audit_N_encode index)).

Definition audit_slot_lookup_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_budget enc enc_work key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_get_budget i
    end.

Definition audit_slot_update_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (key : K) : nat :=
  audit_slot_key_get_budget enc enc_work key +
    match fst (audit_map_get enc key (dense_index u)) with
    | None => 0
    | Some i => audit_slot_index_update_budget i
    end.

Definition audit_slot_lookup_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key,
    audit_slot_source_work enc_work (snd (audit_slot_lookup enc u m key)) <=
      audit_slot_lookup_budget enc enc_work u key.

Definition audit_slot_update_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key value,
    audit_slot_source_work enc_work (snd (audit_slot_update enc u m key value)) <=
      audit_slot_update_budget enc enc_work u key.

Definition audit_slot_remove_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V) key,
    audit_slot_source_work enc_work (snd (audit_slot_remove enc u m key)) <=
      audit_slot_update_budget enc enc_work u key.

Fixpoint audit_slot_elements_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 2 + audit_slot_lookup_budget enc enc_work u key +
      audit_slot_elements_budget enc enc_work u rest
  end.

Definition audit_slot_elements_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V),
    audit_slot_source_work enc_work (snd (audit_slot_elements enc u m)) <=
      audit_slot_elements_budget enc enc_work u (dense_keys u).

(** This input bound permits both probes; the source skips the second on a miss. *)
Fixpoint audit_slot_of_map_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (u : dense_universe K) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest =>
      1 + 2 * audit_slot_key_get_budget enc enc_work key +
      (match fst (audit_map_get enc key (dense_index u)) with
       | None => 0
       | Some i => audit_slot_index_update_budget i
       end) + audit_slot_of_map_budget enc enc_work u rest
  end.

Definition audit_slot_of_map_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (abstract : Map.t K V),
    audit_slot_source_work enc_work (snd (audit_slot_of_map enc u abstract)) <=
      audit_slot_of_map_budget enc enc_work u (dense_keys u).

Fixpoint audit_slot_bindings_budget {K V CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (bindings : list (K * V)) : nat :=
  match bindings with
  | [] => 0
  | (key, _) :: rest => 4 + enc_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
      audit_slot_bindings_budget enc enc_work rest
  end.

Definition audit_slot_to_map_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u (m : slot_map V),
    audit_slot_source_work enc_work (snd (audit_slot_to_map enc u m)) <=
      audit_slot_elements_budget enc enc_work u (dense_keys u) +
      audit_slot_bindings_budget enc enc_work (fst (audit_slot_elements enc u m)).

Definition audit_dense_token_prepare_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work (original : encoding K) u key,
    audit_slot_source_work enc_work (snd (@audit_dense_token_prepare K V CE enc original u key)) <=
      audit_slot_key_get_budget enc enc_work key.

Definition audit_dense_token_read_source_bound_statement : Prop :=
  forall K V CE enc_work (original : encoding K) u (token : dense_slot_token original u) (m :
    slot_map V),
    audit_slot_source_work enc_work (snd (@audit_dense_token_read K V CE original u token m)) <=
      audit_slot_index_get_budget (dense_token_index token).

Definition audit_prepare_slot_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u key,
    audit_slot_source_work enc_work (snd (@audit_prepare_slot K V CE enc u key)) <=
      audit_slot_key_get_budget enc enc_work key.

Definition audit_slot_read_source_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) index,
    audit_slot_source_work enc_work (snd (@audit_slot_read K V CE m index)) <=
      audit_slot_index_get_budget index.

Fixpoint audit_prepare_slots_budget {K CE} (enc : K -> positive * list CE)
    (enc_work : list CE -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 1 + audit_slot_key_get_budget enc enc_work key +
      audit_prepare_slots_budget enc enc_work rest
  end.

Fixpoint audit_read_slots_budget (slots : list (option N)) : nat :=
  match slots with
  | [] => 1
  | None :: rest => 1 + audit_read_slots_budget rest
  | Some index :: rest => 1 + audit_slot_index_get_budget index + audit_read_slots_budget rest
  end.

Definition audit_prepare_slots_source_bound_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) enc_work u keys,
    audit_slot_source_work enc_work (snd (@audit_prepare_slots K V CE enc u keys)) <=
      audit_prepare_slots_budget enc enc_work keys.

Definition audit_read_slots_source_bound_statement : Prop :=
  forall K V CE enc_work (m : slot_map V) slots,
    audit_slot_source_work enc_work (snd (@audit_read_slots K V CE m slots)) <=
      audit_read_slots_budget slots.

(** The original batch contract counts every present slot and its actual binary code. *)
Fixpoint audit_slot_read_calls {K V CE} (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotRead _ _ _ :: rest => S (audit_slot_read_calls rest)
  | _ :: rest => audit_slot_read_calls rest
  end.

Fixpoint audit_slot_read_key_bits {K V CE} (events : list (audit_slot_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditSlotRead index _ _ :: rest =>
      Pos.size_nat (encode N_encoding index) + audit_slot_read_key_bits rest
  | _ :: rest => audit_slot_read_key_bits rest
  end.

Definition audit_read_slots_observation_statement : Prop :=
  forall K V CE (m : slot_map V) slots,
    let '(out, events) := @audit_read_slots K V CE m slots in
    out = read_slots m slots /\ length out = length slots /\
    audit_slot_read_calls events =
      length (filter (fun slot => match slot with Some _ => true | None => false end) slots) /\
    audit_slot_read_key_bits events =
      fold_right (fun slot bits => match slot with
        | Some i => Pos.size_nat (encode N_encoding i) + bits
        | None => bits
        end) 0 slots.
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditDenseSlotsAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditDenseSlots.

Theorem audit_slot_lookup_erases : audit_slot_lookup_erases_statement.
Theorem audit_prepare_slot_erases : audit_prepare_slot_erases_statement.
Theorem audit_slot_read_erases : audit_slot_read_erases_statement.
Theorem audit_prepare_slots_erases : audit_prepare_slots_erases_statement.
Theorem audit_read_slots_erases : audit_read_slots_erases_statement.
Theorem audit_slot_update_erases : audit_slot_update_erases_statement.
Theorem audit_slot_remove_erases : audit_slot_remove_erases_statement.
Theorem audit_slot_elements_erases : audit_slot_elements_erases_statement.
Theorem audit_slot_of_map_erases : audit_slot_of_map_erases_statement.
Theorem audit_slot_to_map_erases : audit_slot_to_map_erases_statement.
Theorem audit_dense_token_prepare_erases : audit_dense_token_prepare_erases_statement.
Theorem audit_dense_token_read_erases : audit_dense_token_read_erases_statement.
Theorem audit_slot_lookup_source_bound : audit_slot_lookup_source_bound_statement.
Theorem audit_slot_update_source_bound : audit_slot_update_source_bound_statement.
Theorem audit_slot_remove_source_bound : audit_slot_remove_source_bound_statement.
Theorem audit_slot_elements_source_bound : audit_slot_elements_source_bound_statement.
Theorem audit_slot_of_map_source_bound : audit_slot_of_map_source_bound_statement.
Theorem audit_slot_to_map_source_bound : audit_slot_to_map_source_bound_statement.
Theorem audit_dense_token_prepare_source_bound : audit_dense_token_prepare_source_bound_statement.
Theorem audit_dense_token_read_source_bound : audit_dense_token_read_source_bound_statement.
Theorem audit_prepare_slot_source_bound : audit_prepare_slot_source_bound_statement.
Theorem audit_slot_read_source_bound : audit_slot_read_source_bound_statement.
Theorem audit_prepare_slots_source_bound : audit_prepare_slots_source_bound_statement.
Theorem audit_read_slots_source_bound : audit_read_slots_source_bound_statement.
Theorem audit_read_slots_observation : audit_read_slots_observation_statement.
```

## CollectionsAuditElements

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditElements.v`.

Public module:
`Galois.Collections.CollectionsAuditElements`.

```rocq
(** * Counted trie and set enumeration

    This candidate mirrors the actual accumulator traversal and its final list passes.
    For example, a singleton emits its stored key and its trie position once.
    Builds on: CollectionsTrie, CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet.
Import List.ListNotations.

(** * Concrete traversal frames *)

Inductive audit_elements_event (A : Type) : Type :=
  | AuditElementsNode (node : Trie.ne A) (acc : list (positive * A))
  | AuditElementsEmit (position : positive) (value : A) (acc : list (positive * A))
  | AuditElementsReverse (remaining acc : list (positive * A))
  | AuditElementsMap (remaining : list (positive * A)).

Arguments AuditElementsNode {A} _ _.
Arguments AuditElementsEmit {A} _ _ _.
Arguments AuditElementsReverse {A} _ _.
Arguments AuditElementsMap {A} _.

(** Preserve the exact original left-root-right traversal and accumulator. *)
Fixpoint audit_elements_fold_ne {A} (path : positive -> positive) (node : Trie.ne A)
    (acc : list (positive * A)) : list (positive * A) * list (audit_elements_event A) :=
  let here := [AuditElementsNode node acc] in
  match node with
  | Trie.N001 r =>
      let '(out, events) := audit_elements_fold_ne (fun p => path (xI p)) r acc in
      (out, here ++ events)
  | Trie.N010 v =>
      let p := path xH in ((p, v) :: acc, here ++ [AuditElementsEmit p v acc])
  | Trie.N011 v r =>
      let p := path xH in
      let next := (p, v) :: acc in
      let '(out, events) := audit_elements_fold_ne (fun q => path (xI q)) r next in
      (out, here ++ [AuditElementsEmit p v acc] ++ events)
  | Trie.N100 l =>
      let '(out, events) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      (out, here ++ events)
  | Trie.N101 l r =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let '(out, re) := audit_elements_fold_ne (fun p => path (xI p)) r middle in
      (out, here ++ le ++ re)
  | Trie.N110 l v =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let p := path xH in
      ((p, v) :: middle, here ++ le ++ [AuditElementsEmit p v middle])
  | Trie.N111 l v r =>
      let '(middle, le) := audit_elements_fold_ne (fun p => path (xO p)) l acc in
      let p := path xH in
      let next := (p, v) :: middle in
      let '(out, re) := audit_elements_fold_ne (fun q => path (xI q)) r next in
      (out, here ++ le ++ [AuditElementsEmit p v middle] ++ re)
  end.

(** This is [rev_append] on the same accumulator, including its final empty case. *)
Fixpoint audit_elements_reverse {A} (input acc : list (positive * A))
    : list (positive * A) * list (audit_elements_event A) :=
  match input with
  | [] => (acc, [AuditElementsReverse input acc])
  | x :: rest =>
      let '(out, events) := audit_elements_reverse rest (x :: acc) in
      (out, AuditElementsReverse input acc :: events)
  end.

(** The actual position-value enumeration is the traversal followed by reversal. *)
Definition audit_trie_elements {A} (input : Trie.t A)
    : list (positive * A) * list (audit_elements_event A) :=
  let '(reversed, fold_events) :=
    match input with
    | Trie.Empty => ([], [])
    | Trie.Nodes node => audit_elements_fold_ne (fun p => p) node []
    end in
  let '(out, reverse_events) := audit_elements_reverse reversed [] in
  (out, fold_events ++ reverse_events).

(** Map and set projection each visit the exact returned list. *)
Fixpoint audit_elements_values {A} (input : list (positive * A))
    : list A * list (audit_elements_event A) :=
  match input with
  | [] => ([], [AuditElementsMap input])
  | (_, value) :: rest =>
      let '(out, events) := audit_elements_values rest in
      (value :: out, AuditElementsMap input :: events)
  end.

Definition audit_map_elements {K V} (input : Map.t K V)
    : list (K * V) * list (audit_elements_event (K * V)) :=
  let '(positions, first) := audit_trie_elements input in
  let '(values, second) := audit_elements_values positions in
  (values, first ++ second).

Inductive audit_set_elements_event (K : Type) : Type :=
  | AuditSetElementsTrie (event : audit_elements_event (K * unit))
  | AuditSetElementsProject (remaining : list (K * unit)).

Arguments AuditSetElementsTrie {K} _.
Arguments AuditSetElementsProject {K} _.

Fixpoint audit_set_elements_project {K} (input : list (K * unit))
    : list K * list (audit_set_elements_event K) :=
  match input with
  | [] => ([], [AuditSetElementsProject input])
  | (key, _) :: rest =>
      let '(out, events) := audit_set_elements_project rest in
      (key :: out, AuditSetElementsProject input :: events)
  end.

Definition audit_finset_elements {K} (input : FinSet.t K)
    : list K * list (audit_set_elements_event K) :=
  let '(values, first) := audit_map_elements input in
  let '(keys, second) := audit_set_elements_project values in
  (keys, map AuditSetElementsTrie first ++ second).

(** * Future correctness and quantitative claims *)

Fixpoint audit_elements_nodes {A} (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => S (audit_elements_nodes r)
  | Trie.N010 _ => 1
  | Trie.N011 _ r => S (audit_elements_nodes r)
  | Trie.N100 l => S (audit_elements_nodes l)
  | Trie.N101 l r => S (audit_elements_nodes l + audit_elements_nodes r)
  | Trie.N110 l _ => S (audit_elements_nodes l)
  | Trie.N111 l _ r => S (audit_elements_nodes l + audit_elements_nodes r)
  end.

Definition audit_trie_elements_erases_statement : Prop :=
  forall A (input : Trie.t A), fst (audit_trie_elements input) = Trie.elements input.

Definition audit_map_elements_erases_statement : Prop :=
  forall K V (input : Map.t K V), fst (audit_map_elements input) = Map.elements input.

Definition audit_finset_elements_erases_statement : Prop :=
  forall K (input : FinSet.t K), fst (audit_finset_elements input) = FinSet.elements input.

Definition audit_elements_fold_count_statement : Prop :=
  forall A path (node : Trie.ne A) acc,
    length (snd (audit_elements_fold_ne path node acc)) <= 2 * audit_elements_nodes node.

(** * Fixed source-frame charges and input measures *)

(** Position construction pays for every bit of the concrete emitted position. *)
Fixpoint audit_elements_bits {A} (path : positive -> positive) (node : Trie.ne A) : nat :=
  match node with
  | Trie.N001 r => audit_elements_bits (fun p => path (xI p)) r
  | Trie.N010 _ => Pos.size_nat (path xH)
  | Trie.N011 _ r => Pos.size_nat (path xH) + audit_elements_bits (fun p => path (xI p)) r
  | Trie.N100 l => audit_elements_bits (fun p => path (xO p)) l
  | Trie.N101 l r => audit_elements_bits (fun p => path (xO p)) l +
      audit_elements_bits (fun p => path (xI p)) r
  | Trie.N110 l _ => audit_elements_bits (fun p => path (xO p)) l + Pos.size_nat (path xH)
  | Trie.N111 l _ r => audit_elements_bits (fun p => path (xO p)) l + Pos.size_nat (path xH) +
      audit_elements_bits (fun p => path (xI p)) r
  end.

Definition audit_elements_frame_work {A} (event : audit_elements_event A) : nat :=
  match event with
  | AuditElementsNode _ _ => 10
  | AuditElementsEmit position _ _ => 3 + Pos.size_nat position
  | AuditElementsReverse _ _ => 2
  | AuditElementsMap _ => 2
  end.

Fixpoint audit_elements_work {A} (events : list (audit_elements_event A)) : nat :=
  match events with
  | [] => 0
  | event :: rest => audit_elements_frame_work event + audit_elements_work rest
  end.

Fixpoint audit_set_elements_work {K} (events : list (audit_set_elements_event K)) : nat :=
  match events with
  | [] => 0
  | AuditSetElementsTrie event :: rest =>
      audit_elements_frame_work event + audit_set_elements_work rest
  | AuditSetElementsProject _ :: rest => 2 + audit_set_elements_work rest
  end.

Definition audit_trie_nodes {A} (input : Trie.t A) : nat :=
  match input with Trie.Empty => 0 | Trie.Nodes node => audit_elements_nodes node end.

Definition audit_trie_output_bits {A} (input : Trie.t A) : nat :=
  match input with
  | Trie.Empty => 0
  | Trie.Nodes node => audit_elements_bits (fun p => p) node
  end.

(** Bounds are input-derived and include emitted position bits and existing output traversals. *)
Definition audit_trie_elements_work_bound_statement : Prop :=
  forall A (input : Trie.t A),
    audit_elements_work (snd (audit_trie_elements input)) <=
      15 * audit_trie_nodes input + audit_trie_output_bits input + 2.

Definition audit_map_elements_work_bound_statement : Prop :=
  forall K V (input : Map.t K V),
    audit_elements_work (snd (audit_map_elements input)) <=
      17 * audit_trie_nodes input + audit_trie_output_bits input + 4.

Definition audit_finset_elements_work_bound_statement : Prop :=
  forall K (input : FinSet.t K),
    audit_set_elements_work (snd (audit_finset_elements input)) <=
      19 * audit_trie_nodes input + audit_trie_output_bits input + 6.
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditElementsAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditElements.

Theorem audit_trie_elements_erases : audit_trie_elements_erases_statement.
Theorem audit_map_elements_erases : audit_map_elements_erases_statement.
Theorem audit_finset_elements_erases : audit_finset_elements_erases_statement.
Theorem audit_elements_fold_count : audit_elements_fold_count_statement.
Theorem audit_trie_elements_work_bound : audit_trie_elements_work_bound_statement.
Theorem audit_map_elements_work_bound : audit_map_elements_work_bound_statement.
Theorem audit_finset_elements_work_bound : audit_finset_elements_work_bound_statement.
```

## CollectionsAuditEncoderBudget

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditEncoderBudget.v`.

Public module:
`Galois.Collections.CollectionsAuditEncoderBudget`.

```rocq
(** * Input budgets for concrete encoders

    These budgets depend on key operands and component budgets, never returned event work.
    For example, a pair pays for both child codes and their delimiter and stream traversals.
    Builds on: CollectionsEncoding and the counted encoding bodies. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Collections Require Import CollectionsAuditEncoding.
Import List.ListNotations.

(** An external body exposes its actual execution separately from its counted adapter. *)
Record audit_encoder_adapter (K CE : Type) : Type := AuditEncoderAdapter {
  audit_encoder_run : K -> positive * list CE;
  audit_encoder_work : list CE -> nat;
  audit_encoder_budget : K -> nat;
  audit_encoder_source : K -> positive -> nat -> Prop
}.

Arguments audit_encoder_run {K CE} _ _.
Arguments audit_encoder_work {K CE} _ _.
Arguments audit_encoder_budget {K CE} _ _.
Arguments audit_encoder_source {K CE} _ _ _ _.

(** Clients prove their external source body, its returned code and its per-input budget. *)
Record audit_encoder_adapter_laws {K CE} (original : encoding K)
    (adapter : audit_encoder_adapter K CE) : Prop := AuditEncoderAdapterLaws {
  audit_encoder_source_total : forall key, exists code work,
    audit_encoder_source adapter key code work;
  audit_encoder_source_agrees : forall key code work,
    audit_encoder_source adapter key code work ->
    code = fst (audit_encoder_run adapter key) /\
    work = audit_encoder_work adapter (snd (audit_encoder_run adapter key));
  audit_encoder_code_agrees : forall key,
    fst (audit_encoder_run adapter key) = encode original key;
  audit_encoder_input_bound : forall key,
    audit_encoder_work adapter (snd (audit_encoder_run adapter key)) <=
      audit_encoder_budget adapter key
}.

Definition audit_nat_input_budget (key : nat) : nat :=
  2 * S key * S (Pos.size_nat (encode nat_encoding key)).

Definition audit_N_input_budget (key : N) : nat :=
  match key with
  | N0 => 2
  | Npos p => 2 + 2 * Pos.size_nat p
  end.

Definition audit_pair_input_budget {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB)
    (first_budget : A -> nat) (second_budget : B -> nat) (key : A * B) : nat :=
  5 + 10 * (Pos.size_nat (fst (first (fst key))) +
    Pos.size_nat (fst (second (snd key)))) +
    first_budget (fst key) + second_budget (snd key).

Fixpoint audit_child_input_budget {A} (budget : A -> nat) (keys : list A) : nat :=
  match keys with
  | [] => 0
  | key :: rest => budget key + audit_child_input_budget budget rest
  end.

Definition audit_list_input_budget {A CE} (element : A -> positive * list CE)
    (element_budget : A -> nat) (keys : list A) : nat :=
  4 + 2 * length keys + 10 * audit_encoded_bits element keys +
    audit_child_input_budget element_budget keys.

Definition audit_option_input_budget {A} (element_budget : A -> nat) (key : option A) : nat :=
  match key with
  | None => 1
  | Some a => 1 + element_budget a
  end.

Definition audit_sum_input_budget {A B} (left_budget : A -> nat) (right_budget : B -> nat)
    (key : A + B) : nat :=
  match key with
  | inl a => 1 + left_budget a
  | inr b => 1 + right_budget b
  end.

(** Every fixed base encoder has its own body and an independent operand budget. *)
Definition audit_base_encoder_input_bound_statement : Prop :=
  (forall p, audit_basic_encoding_work (snd (audit_positive_encode p)) <= 1) /\
  (forall b, audit_basic_encoding_work (snd (audit_bool_encode b)) <= 1) /\
  (forall u, audit_basic_encoding_work (snd (audit_unit_encode u)) <= 1) /\
  (forall z, audit_basic_encoding_work (snd (audit_z_encode z)) <= 1) /\
  (forall n, audit_nat_events_work (snd (audit_nat_encode n)) <= audit_nat_input_budget n) /\
  (forall n, audit_N_encoding_work (snd (audit_N_encode n)) <= audit_N_input_budget n).

(** Pair composition requires only the two actual external component call bounds. *)
Definition audit_pair_input_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget key,
    (forall a, first_work (snd (first a)) <= first_budget a) ->
    (forall b, second_work (snd (second b)) <= second_budget b) ->
    audit_pair_events_work first_work second_work (snd (audit_pair_encode first second key)) <=
      audit_pair_input_budget first second first_budget second_budget key.

(** List composition charges each original element occurrence and every emitted code bit. *)
Definition audit_list_input_bound_statement : Prop :=
  forall A CE (element : A -> positive * list CE) element_work element_budget keys,
    (forall a, element_work (snd (element a)) <= element_budget a) ->
    audit_list_events_work element_work (snd (audit_list_encode element keys)) <=
      audit_list_input_budget element element_budget keys.

(** Sum and option bounds retain the selected constructor without evaluating another body. *)
Definition audit_sum_option_input_bound_statement : Prop :=
  (forall A CE (element : A -> positive * list CE) work budget key,
    (forall a, work (snd (element a)) <= budget a) ->
    audit_option_events_work work (snd (audit_option_encode element key)) <=
      audit_option_input_budget budget key) /\
  (forall A B EA EB (left : A -> positive * list EA) (right : B -> positive * list EB)
      left_work right_work left_budget right_budget key,
    (forall a, left_work (snd (left a)) <= left_budget a) ->
    (forall b, right_work (snd (right b)) <= right_budget b) ->
    audit_sum_events_work left_work right_work (snd (audit_sum_encode left right key)) <=
      audit_sum_input_budget left_budget right_budget key).

Example audit_pair_budget_retains_width :
  audit_pair_input_budget audit_positive_encode audit_positive_encode
    (fun _ => 1) (fun _ => 1) (1%positive, 8%positive) = 57.
Proof.
  reflexivity.
Qed.

Example audit_list_budget_retains_occurrences :
  audit_list_input_budget audit_positive_encode (fun _ => 1)
    [1%positive; 1%positive] = 30.
Proof.
  reflexivity.
Qed.
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditEncoderBudgetAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditEncoderBudget.

Theorem audit_base_encoder_input_bound : audit_base_encoder_input_bound_statement.
Theorem audit_pair_input_bound : audit_pair_input_bound_statement.
Theorem audit_list_input_bound : audit_list_input_bound_statement.
Theorem audit_sum_option_input_bound : audit_sum_option_input_bound_statement.
```

## CollectionsAuditEncoding

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditEncoding.v`.

Public module:
`Galois.Collections.CollectionsAuditEncoding`.

```rocq
(** * Counted encoding primitives

    These candidate mirrors preserve encoder operands, outputs and intermediate stream work.
    For example, unary zero encodes to one and a successor traverses its carry bits.
    Builds on: CollectionsEncoding and the audit vocabulary. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
Import List.ListNotations.

(** * Successor and unary conversion *)

Inductive audit_nat_encoding_event : Type :=
  | AuditNatFrame (input : nat)
  | AuditPositiveSuccFrame (input output : positive).

(** This mirror visits the actual carry chain of [Pos.succ]. *)
Fixpoint audit_positive_succ (input : positive)
    : positive * list audit_nat_encoding_event :=
  match input with
  | xH => (xO xH, [AuditPositiveSuccFrame input (xO xH)])
  | xO p => (xI p, [AuditPositiveSuccFrame input (xI p)])
  | xI p =>
      let '(next, events) := audit_positive_succ p in
      (xO next, AuditPositiveSuccFrame input (xO next) :: events)
  end.

(** This mirror retains every unary constructor and every positive successor frame. *)
Fixpoint audit_nat_encode (input : nat) : positive * list audit_nat_encoding_event :=
  match input with
  | O => (xH, [AuditNatFrame input])
  | S rest =>
      let '(previous, events) := audit_nat_encode rest in
      let '(next, succ_events) := audit_positive_succ previous in
      (next, AuditNatFrame input :: events ++ succ_events)
  end.

(** Exact result and unary-sensitive bound are future AUD-CL proof obligations. *)
Definition audit_positive_succ_erases_statement : Prop :=
  forall input, fst (audit_positive_succ input) = Pos.succ input.

Definition audit_nat_encode_erases_statement : Prop :=
  forall input, fst (audit_nat_encode input) = encode nat_encoding input.

Definition audit_positive_succ_count_statement : Prop :=
  forall input, length (snd (audit_positive_succ input)) <= Pos.size_nat input.

Definition audit_nat_encode_count_statement : Prop :=
  forall input, length (snd (audit_nat_encode input)) <=
    S input * S (Pos.size_nat (encode nat_encoding input)).

(** * Source-indexed unary and carry derivations *)

(** Each successor rule preserves the concrete carry suffix and output constructor. *)
Inductive audit_positive_succ_run : positive -> positive -> list audit_nat_encoding_event ->
    nat -> Prop :=
  | AuditSuccOne : audit_positive_succ_run xH (xO xH) [AuditPositiveSuccFrame xH (xO xH)] 2
  | AuditSuccZero : forall p,
      audit_positive_succ_run (xO p) (xI p) [AuditPositiveSuccFrame (xO p) (xI p)] 2
  | AuditSuccCarry : forall p result events work,
      audit_positive_succ_run p result events work ->
      audit_positive_succ_run (xI p) (xO result)
        (AuditPositiveSuccFrame (xI p) (xO result) :: events) (2 + work).

Definition audit_positive_succ_run_correct_statement : Prop :=
  forall input output events work,
    audit_positive_succ_run input output events work ->
    output = Pos.succ input /\ (output, events) = audit_positive_succ input /\
    work = 2 * length events /\ work <= 2 * Pos.size_nat input.

Definition audit_positive_succ_run_total_statement : Prop :=
  forall input, exists output events work, audit_positive_succ_run input output events work.

(** Each unary step composes the actual successor derivation for that prior result. *)
Inductive audit_nat_encode_run : nat -> positive -> list audit_nat_encoding_event -> nat -> Prop :=
  | AuditNatZero : audit_nat_encode_run 0 xH [AuditNatFrame 0] 2
  | AuditNatSuccessor : forall input previous output events succ_events work succ_work,
      audit_nat_encode_run input previous events work ->
      audit_positive_succ_run previous output succ_events succ_work ->
      audit_nat_encode_run (S input) output (AuditNatFrame (S input) :: events ++ succ_events)
        (2 + work + succ_work).

Definition audit_nat_encode_run_correct_statement : Prop :=
  forall input output events work,
    audit_nat_encode_run input output events work ->
    output = encode nat_encoding input /\ (output, events) = audit_nat_encode input /\
    work = 2 * length events /\
    work <= 2 * S input * S (Pos.size_nat (encode nat_encoding input)).

Definition audit_nat_encode_run_total_statement : Prop :=
  forall input, exists output events work, audit_nat_encode_run input output events work.

(** * Fixed primitive encoding adapters *)

Inductive audit_basic_encoding_event (K : Type) : Type :=
  | AuditBasicEncoding (input : K) (output : positive).

Arguments AuditBasicEncoding {K} _ _.

Definition audit_positive_encode (input : positive)
    : positive * list (audit_basic_encoding_event positive) :=
  (input, [AuditBasicEncoding input input]).

Definition audit_bool_encode (input : bool) : positive * list (audit_basic_encoding_event bool) :=
  let output := if input then xO xH else xH in (output, [AuditBasicEncoding input output]).

Definition audit_unit_encode (input : unit) : positive * list (audit_basic_encoding_event unit) :=
  (xH, [AuditBasicEncoding input xH]).

Definition audit_z_encode (input : Z) : positive * list (audit_basic_encoding_event Z) :=
  let output := match input with
    | Z0 => xH
    | Zpos p => xO p
    | Zneg p => xI p
    end in
  (output, [AuditBasicEncoding input output]).

Inductive audit_n_encoding_event : Type :=
  | AuditNEncoding (input : N) (output : positive)
  | AuditNSucc (event : audit_nat_encoding_event).

(** Binary conversion retains the actual successor carry frames. *)
Definition audit_N_encode (input : N) : positive * list audit_n_encoding_event :=
  match input with
  | N0 => (xH, [AuditNEncoding input xH])
  | Npos p =>
      let '(output, events) := audit_positive_succ p in
      (output, AuditNEncoding input output :: map AuditNSucc events)
  end.

Definition audit_N_encode_erases_statement : Prop :=
  forall input, fst (audit_N_encode input) = encode N_encoding input.

(** Primitive source cases preserve their actual exact returned codes. *)
Definition audit_positive_encode_erases_statement : Prop :=
  forall input, fst (audit_positive_encode input) = encode positive_encoding input.

Definition audit_bool_encode_erases_statement : Prop :=
  forall input, fst (audit_bool_encode input) = encode bool_encoding input.

Definition audit_unit_encode_erases_statement : Prop :=
  forall input, fst (audit_unit_encode input) = encode unit_encoding input.

Definition audit_z_encode_erases_statement : Prop :=
  forall input, fst (audit_z_encode input) = encode Z_encoding input.

(** * Delimited stream construction *)

Inductive audit_encoding_frame : Type :=
  | AuditEmitCode (input : positive) (tail output : list bool)
  | AuditStreamPositive (input : list bool) (output : positive).

(** Every frame includes the actual tail and returned stream. *)
Fixpoint audit_emit_code (input : positive) (tail : list bool)
    : list bool * list audit_encoding_frame :=
  match input with
  | xH =>
      let output := false :: true :: tail in
      (output, [AuditEmitCode input tail output])
  | xO rest =>
      let '(suffix, events) := audit_emit_code rest tail in
      let output := false :: false :: suffix in
      (output, AuditEmitCode input tail output :: events)
  | xI rest =>
      let '(suffix, events) := audit_emit_code rest tail in
      let output := true :: true :: suffix in
      (output, AuditEmitCode input tail output :: events)
  end.

(** Each stream constructor preserves its actual suffix and final positive code. *)
Fixpoint audit_stream_positive (input : list bool) : positive * list audit_encoding_frame :=
  match input with
  | [] => (xH, [AuditStreamPositive input xH])
  | false :: rest =>
      let '(next, events) := audit_stream_positive rest in
      (xO next, AuditStreamPositive input (xO next) :: events)
  | true :: rest =>
      let '(next, events) := audit_stream_positive rest in
      (xI next, AuditStreamPositive input (xI next) :: events)
  end.

Definition audit_emit_code_erases_statement : Prop :=
  forall p tail, fst (audit_emit_code p tail) = emit_code p tail.

Definition audit_stream_positive_erases_statement : Prop :=
  forall bits, fst (audit_stream_positive bits) = stream_positive bits.

(** * Pair composition *)

Inductive audit_pair_event (A B EA EB : Type) : Type :=
  | AuditPairFirst (input : A) (output : positive) (events : list EA)
  | AuditPairSecond (input : B) (output : positive) (events : list EB)
  | AuditPairFrame (event : audit_encoding_frame).

Arguments AuditPairFirst {A B EA EB} _ _ _.
Arguments AuditPairSecond {A B EA EB} _ _ _.
Arguments AuditPairFrame {A B EA EB} _.

(** Actual component traces are retained, not replaced by a price or discarded on composition. *)
Definition audit_pair_encode {A B EA EB}
    (first : A -> positive * list EA) (second : B -> positive * list EB) (input : A * B)
    : positive * list (audit_pair_event A B EA EB) :=
  let '(a, b) := input in
  let '(ac, ae) := first a in
  let '(bc, be) := second b in
  let '(bt, bframes) := audit_emit_code bc [] in
  let '(stream, aframes) := audit_emit_code ac bt in
  let '(result, sframes) := audit_stream_positive stream in
  (result, [AuditPairFirst a ac ae; AuditPairSecond b bc be] ++
    map AuditPairFrame (bframes ++ aframes ++ sframes)).

(** Component erasure applies only to these actual calls; internal components prove it separately.
  *)
Definition audit_pair_encode_erases_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      (e1 : encoding A) (e2 : encoding B) (a : A) (b : B),
    fst (first a) = encode e1 a -> fst (second b) = encode e2 b ->
    fst (audit_pair_encode first second (a, b)) = encode (pair_encoding e1 e2) (a, b).

(** * List, option and sum composition *)

Inductive audit_list_event (A E : Type) : Type :=
  | AuditListCase (input : list A)
  | AuditListComponent (input : A) (output : positive) (events : list E)
  | AuditListFrame (event : audit_encoding_frame).

Arguments AuditListCase {A E} _.
Arguments AuditListComponent {A E} _ _ _.
Arguments AuditListFrame {A E} _.

(** Each list element is encoded once, including its own actual nested event sequence. *)
Fixpoint audit_emit_list {A E} (element : A -> positive * list E) (input : list A)
    : list bool * list (audit_list_event A E) :=
  match input with
  | [] => ([], [AuditListCase input])
  | x :: rest =>
      let '(code, component_events) := element x in
      let '(tail, tail_events) := audit_emit_list element rest in
      let '(result, frames) := audit_emit_code code tail in
      (result, [AuditListCase input; AuditListComponent x code component_events] ++
        tail_events ++ map AuditListFrame frames)
  end.

(** The stream conversion follows the exact emitted list and keeps all its frames. *)
Definition audit_list_encode {A E} (element : A -> positive * list E) (input : list A)
    : positive * list (audit_list_event A E) :=
  let '(bits, events) := audit_emit_list element input in
  let '(result, frames) := audit_stream_positive bits in
  (result, events ++ map AuditListFrame frames).

Definition audit_emit_list_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : list A),
    (forall x, In x input -> fst (element x) = encode enc x) ->
    fst (audit_emit_list element input) = emit_list enc input.

Definition audit_list_encode_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : list A),
    (forall x, In x input -> fst (element x) = encode enc x) ->
    fst (audit_list_encode element input) = encode (list_encoding enc) input.

Inductive audit_sum_event (A B EA EB : Type) : Type :=
  | AuditSumLeft (input : A) (code : positive) (events : list EA)
  | AuditSumRight (input : B) (code : positive) (events : list EB).

Arguments AuditSumLeft {A B EA EB} _ _ _.
Arguments AuditSumRight {A B EA EB} _ _ _.

(** Sum encoding evaluates only the selected actual component. *)
Definition audit_sum_encode {A B EA EB}
    (left : A -> positive * list EA) (right : B -> positive * list EB) (input : A + B)
    : positive * list (audit_sum_event A B EA EB) :=
  match input with
  | inl a => let '(code, events) := left a in (xO code, [AuditSumLeft a code events])
  | inr b => let '(code, events) := right b in (xI code, [AuditSumRight b code events])
  end.

Definition audit_sum_encode_erases_statement : Prop :=
  forall A B EA EB (left : A -> positive * list EA) (right : B -> positive * list EB)
      (e1 : encoding A) (e2 : encoding B) (input : A + B),
    (forall a, input = inl a -> fst (left a) = encode e1 a) ->
    (forall b, input = inr b -> fst (right b) = encode e2 b) ->
    fst (audit_sum_encode left right input) = encode (sum_encoding e1 e2) input.

Inductive audit_option_event (A E : Type) : Type :=
  | AuditOptionNone
  | AuditOptionSome (input : A) (code : positive) (events : list E).

Arguments AuditOptionNone {A E}.
Arguments AuditOptionSome {A E} _ _ _.

Definition audit_option_encode {A E} (element : A -> positive * list E) (input : option A)
    : positive * list (audit_option_event A E) :=
  match input with
  | None => (xH, [AuditOptionNone])
  | Some a => let '(code, events) := element a in (xO code, [AuditOptionSome a code events])
  end.

Definition audit_option_encode_erases_statement : Prop :=
  forall A E (element : A -> positive * list E) (enc : encoding A) (input : option A),
    (forall a, input = Some a -> fst (element a) = encode enc a) ->
    fst (audit_option_encode element input) = encode (option_encoding enc) input.

(** * Fixed event folds *)

(** Fixed positive source-frame charges distinguish delimiter and stream cases. *)
Definition audit_encoding_frame_charge (event : audit_encoding_frame) : nat :=
  match event with
  | AuditEmitCode _ _ _ => 4
  | AuditStreamPositive _ _ => 3
  end.

Fixpoint audit_encoding_frames_work (events : list audit_encoding_frame) : nat :=
  match events with
  | [] => 0
  | event :: rest => audit_encoding_frame_charge event + audit_encoding_frames_work rest
  end.

(** Unary frames and base constructors have fixed, operand-independent event charges. *)
Definition audit_nat_events_work (events : list audit_nat_encoding_event) : nat := 2 * length
  events.

Definition audit_basic_encoding_work {K} (events : list (audit_basic_encoding_event K)) : nat :=
  length events.

Definition audit_N_encoding_work (events : list audit_n_encoding_event) : nat :=
  2 * length events.

(** The supplied folds consume actual child traces; library children use their fixed folds. *)
Fixpoint audit_pair_events_work {A B EA EB}
    (first_work : list EA -> nat) (second_work : list EB -> nat)
    (events : list (audit_pair_event A B EA EB)) : nat :=
  match events with
  | [] => 0
  | AuditPairFirst _ _ child :: rest => 1 + first_work child +
      audit_pair_events_work first_work second_work rest
  | AuditPairSecond _ _ child :: rest => 1 + second_work child +
      audit_pair_events_work first_work second_work rest
  | AuditPairFrame frame :: rest => audit_encoding_frame_charge frame +
      audit_pair_events_work first_work second_work rest
  end.

Fixpoint audit_list_events_work {A E} (child_work : list E -> nat)
    (events : list (audit_list_event A E)) : nat :=
  match events with
  | [] => 0
  | AuditListCase _ :: rest => 1 + audit_list_events_work child_work rest
  | AuditListComponent _ _ child :: rest => 1 + child_work child +
      audit_list_events_work child_work rest
  | AuditListFrame frame :: rest => audit_encoding_frame_charge frame +
      audit_list_events_work child_work rest
  end.

Fixpoint audit_sum_events_work {A B EA EB}
    (left_work : list EA -> nat) (right_work : list EB -> nat)
    (events : list (audit_sum_event A B EA EB)) : nat :=
  match events with
  | [] => 0
  | AuditSumLeft _ _ child :: rest => 1 + left_work child +
      audit_sum_events_work left_work right_work rest
  | AuditSumRight _ _ child :: rest => 1 + right_work child +
      audit_sum_events_work left_work right_work rest
  end.

Fixpoint audit_option_events_work {A E} (child_work : list E -> nat)
    (events : list (audit_option_event A E)) : nat :=
  match events with
  | [] => 0
  | AuditOptionNone :: rest => 1 + audit_option_events_work child_work rest
  | AuditOptionSome _ _ child :: rest => 1 + child_work child +
      audit_option_events_work child_work rest
  end.

(** The original key operands determine emitted bit counts without event self-bounds. *)
Fixpoint audit_encoded_bits {A E} (element : A -> positive * list E) (input : list A) : nat :=
  match input with
  | [] => 0
  | x :: rest => Pos.size_nat (fst (element x)) + audit_encoded_bits element rest
  end.

Definition audit_emit_code_count_statement : Prop :=
  forall code tail, length (snd (audit_emit_code code tail)) = Pos.size_nat code.

Definition audit_stream_positive_count_statement : Prop :=
  forall bits, length (snd (audit_stream_positive bits)) = S (length bits).

Definition audit_emit_list_count_statement : Prop :=
  forall A E (element : A -> positive * list E) input,
    length (snd (audit_emit_list element input)) =
      1 + 2 * length input + audit_encoded_bits element input.

Definition audit_list_encode_count_statement : Prop :=
  forall A E (element : A -> positive * list E) input,
    length (snd (audit_list_encode element input)) =
      2 + 2 * length input + 3 * audit_encoded_bits element input.

Definition audit_pair_encode_count_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB) a b,
    length (snd (audit_pair_encode first second (a, b))) =
      3 + 3 * (Pos.size_nat (fst (first a)) + Pos.size_nat (fst (second b))).
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditEncodingAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditEncoding.

Theorem audit_positive_succ_erases : audit_positive_succ_erases_statement.
Theorem audit_nat_encode_erases : audit_nat_encode_erases_statement.
Theorem audit_positive_succ_count : audit_positive_succ_count_statement.
Theorem audit_nat_encode_count : audit_nat_encode_count_statement.
Theorem audit_positive_succ_run_correct : audit_positive_succ_run_correct_statement.
Theorem audit_positive_succ_run_total : audit_positive_succ_run_total_statement.
Theorem audit_nat_encode_run_correct : audit_nat_encode_run_correct_statement.
Theorem audit_nat_encode_run_total : audit_nat_encode_run_total_statement.
Theorem audit_N_encode_erases : audit_N_encode_erases_statement.
Theorem audit_positive_encode_erases : audit_positive_encode_erases_statement.
Theorem audit_bool_encode_erases : audit_bool_encode_erases_statement.
Theorem audit_unit_encode_erases : audit_unit_encode_erases_statement.
Theorem audit_z_encode_erases : audit_z_encode_erases_statement.
Theorem audit_emit_code_erases : audit_emit_code_erases_statement.
Theorem audit_stream_positive_erases : audit_stream_positive_erases_statement.
Theorem audit_pair_encode_erases : audit_pair_encode_erases_statement.
Theorem audit_emit_list_erases : audit_emit_list_erases_statement.
Theorem audit_list_encode_erases : audit_list_encode_erases_statement.
Theorem audit_sum_encode_erases : audit_sum_encode_erases_statement.
Theorem audit_option_encode_erases : audit_option_encode_erases_statement.
Theorem audit_emit_code_count : audit_emit_code_count_statement.
Theorem audit_stream_positive_count : audit_stream_positive_count_statement.
Theorem audit_emit_list_count : audit_emit_list_count_statement.
Theorem audit_list_encode_count : audit_list_encode_count_statement.
Theorem audit_pair_encode_count : audit_pair_encode_count_statement.
```

## CollectionsAuditFamilyClosure

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditFamilyClosure.v`.

Public module:
`Galois.Collections.CollectionsAuditFamilyClosure`.

```rocq
(** * Canonical collections source adequacy closure

    These are complete future theorem types for the source-shaped family below.
    The groups make the full source-erasure and source-work obligations reviewable
    as one AUD-CL interface while keeping each operation's assumptions explicit. *)
From Galois.Collections Require Import CollectionsAuditTrie.
From Galois.Collections Require Import CollectionsAuditPrimitive.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Collections Require Import CollectionsAuditFinSet.
From Galois.Collections Require Import CollectionsAuditUnion.
From Galois.Collections Require Import CollectionsAuditInter.
From Galois.Collections Require Import CollectionsAuditMapTraverse.
From Galois.Collections Require Import CollectionsAuditMapFold.
From Galois.Collections Require Import CollectionsAuditPrepared.
From Galois.Collections Require Import CollectionsAuditDense.
From Galois.Collections Require Import CollectionsAuditDenseSlots.
From Galois.Collections Require Import CollectionsAuditUnionFind.
From Galois.Collections Require Import CollectionsAuditUnionFindAdapters.
From Galois.Collections Require Import CollectionsAuditEncoderBudget.
From Galois.Collections Require Import CollectionsAuditUnionFindWhole.
From Galois.Collections Require Import CollectionsAuditContracts.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Collections Require Import CollectionsAuditAdapted.
From Galois.Collections Require Import CollectionsAuditTraversalBudget.
From Galois.Collections Require Import CollectionsAuditDenseInput.

Definition audit_cl_primitive_erasure_closure_statement : Prop :=
  audit_trie_get_erases_statement /\ audit_trie_set_erases_statement /\
  audit_trie_remove_erases_statement /\ audit_map_code_get_erases_statement /\
  audit_trie_left_source_adequate_statement /\ audit_trie_right_source_adequate_statement /\
  audit_trie_value_source_adequate_statement /\ audit_trie_node_source_adequate_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_succ_erases_statement /\
  audit_nat_encode_erases_statement /\ audit_N_encode_erases_statement /\
  audit_positive_encode_erases_statement /\ audit_bool_encode_erases_statement /\
  audit_unit_encode_erases_statement /\ audit_z_encode_erases_statement /\
  audit_emit_code_erases_statement /\ audit_stream_positive_erases_statement /\
  audit_pair_encode_erases_statement /\ audit_emit_list_erases_statement /\
  audit_list_encode_erases_statement /\ audit_sum_encode_erases_statement /\
  audit_option_encode_erases_statement /\ audit_trie_elements_erases_statement /\
  audit_map_elements_erases_statement /\ audit_finset_elements_erases_statement /\
  audit_map_get_erases_statement /\ audit_map_set_erases_statement /\
  audit_map_remove_erases_statement /\ audit_finset_of_list_erases_statement /\
  audit_finset_add_erases_statement /\ audit_finset_mem_erases_statement /\
  audit_finset_remove_erases_statement /\ audit_finset_union_erases_statement /\
  audit_finset_inter_erases_statement /\ audit_map_transform_erases_statement /\
  audit_map_union_erases_statement /\ audit_map_fold_erases_statement /\
  audit_prepare_key_erases_statement /\ audit_prepared_lookup_erases_statement /\
  audit_prepared_update_erases_statement /\ audit_prepared_remove_erases_statement /\
  audit_dense_prepare_erases_statement /\ audit_slot_lookup_erases_statement /\
  audit_prepare_slot_erases_statement /\ audit_slot_read_erases_statement /\
  audit_prepare_slots_erases_statement /\ audit_read_slots_erases_statement /\
  audit_slot_update_erases_statement /\ audit_slot_remove_erases_statement /\
  audit_slot_elements_erases_statement /\ audit_slot_of_map_erases_statement /\
  audit_slot_to_map_erases_statement /\ audit_dense_token_prepare_erases_statement /\
  audit_dense_token_read_erases_statement /\ audit_uf_find_fuel_erases_statement /\
  audit_uf_find_erases_statement /\ audit_uf_union_erases_statement /\
  audit_uf_equivb_erases_statement /\ audit_uf_keys_erases_statement /\
  audit_uf_history_erases_statement /\ audit_uf_of_unions_erases_statement.

Definition audit_cl_source_work_closure_statement : Prop :=
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_positive_eqb_source_bound_statement /\ audit_map_get_source_work_bound_statement /\
  audit_map_set_source_work_bound_statement /\ audit_map_remove_source_work_bound_statement /\
  audit_finset_of_list_source_bound_statement /\ audit_finset_union_source_bound_statement /\
  audit_finset_inter_source_bound_statement /\ audit_map_transform_source_bound_statement /\
  audit_map_union_source_bound_statement /\ audit_map_fold_source_work_bound_statement /\
  audit_trie_elements_work_bound_statement /\ audit_map_elements_work_bound_statement /\
  audit_finset_elements_work_bound_statement /\ audit_prepared_lookup_source_bound_statement /\
  audit_prepared_update_source_bound_statement /\ audit_prepared_remove_source_bound_statement /\
  audit_dense_prepare_source_bound_statement /\ audit_slot_lookup_source_bound_statement /\
  audit_slot_update_source_bound_statement /\ audit_slot_remove_source_bound_statement /\
  audit_slot_elements_source_bound_statement /\ audit_slot_of_map_source_bound_statement /\
  audit_slot_to_map_source_bound_statement /\ audit_dense_token_prepare_source_bound_statement /\
  audit_dense_token_read_source_bound_statement /\ audit_prepare_slot_source_bound_statement /\
  audit_slot_read_source_bound_statement /\ audit_prepare_slots_source_bound_statement /\
  audit_read_slots_source_bound_statement /\ audit_uf_find_fuel_work_bound_statement /\
  audit_uf_union_work_bound_statement /\ audit_uf_equivb_work_bound_statement /\
  audit_uf_keys_input_bound_statement /\ audit_uf_history_bound_statement /\
  audit_uf_branches_bound_statement /\ audit_uf_of_unions_source_bound_statement.

Definition audit_cl_composite_union_find_closure_statement : Prop :=
  audit_uf_pair_of_unions_erases_statement /\ audit_uf_list_of_unions_erases_statement /\
  audit_uf_pair_of_unions_source_bound_statement /\
  audit_uf_list_of_unions_source_bound_statement.

Definition audit_cl_full_source_contract_statement : Prop :=
  audit_cl_primitive_erasure_closure_statement /\
  audit_cl_source_work_closure_statement /\
  audit_cl_composite_union_find_closure_statement.

(** Source-run adequacy connects the event folds to the literal trie and unary encoding bodies. *)
Definition audit_cl_literal_body_closure_statement : Prop :=
  audit_trie_get_run_total_statement /\ audit_trie_get_run_correct_statement /\
  audit_trie_update_run_total_statement /\ audit_trie_update_run_correct_statement /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_map_code_get_run_total_statement /\ audit_map_code_get_run_correct_statement /\
  audit_trie_access_source_clauses_statement /\
  audit_positive_succ_run_total_statement /\ audit_positive_succ_run_correct_statement /\
  audit_nat_encode_run_total_statement /\ audit_nat_encode_run_correct_statement.

(** Whole encoder and persistent-operation recurrences assume only genuine external leaf bodies. *)
Definition audit_cl_whole_input_closure_statement : Prop :=
  audit_base_encoder_input_bound_statement /\ audit_pair_input_bound_statement /\
  audit_list_input_bound_statement /\ audit_sum_option_input_bound_statement /\
  audit_uf_whole_input_bound_statement /\ audit_uf_pair_whole_input_bound_statement /\
  audit_uf_list_whole_input_bound_statement /\ audit_uf_branches_whole_input_bound_statement.

(** The final collection closure includes literal adequacy and every whole-operation input bound. *)
Definition audit_cl_complete_source_contract_statement : Prop :=
  audit_cl_full_source_contract_statement /\ audit_cl_literal_body_closure_statement /\
  audit_cl_whole_input_closure_statement /\
  prepared_key_refines_contract /\ dense_map_refines_contract /\ union_find_cost_contract.

(** Actual foreign source relations are bound to every retained collection callback invocation. *)
Definition audit_cl_adapted_source_contract_statement : Prop :=
  audit_cl_complete_source_contract_statement /\ audit_external_callback_observed_statement /\
  audit_uf_whole_input_bound_adapted_statement /\
  audit_uf_pair_whole_input_bound_adapted_statement /\
  audit_uf_list_whole_input_bound_adapted_statement /\
  audit_uf_branches_whole_input_bound_adapted_statement /\
  audit_pair_input_bound_adapted_statement /\ audit_list_input_bound_adapted_statement /\
  audit_map_transform_adapted_input_bound_statement /\
  audit_map_union_adapted_input_bound_statement /\ audit_map_fold_adapted_input_bound_statement.

(** Prepared and dense closure uses only operand budgets for all internal numeric encoders. *)
Definition audit_cl_dense_whole_source_contract_statement : Prop :=
  audit_prepare_key_whole_input_bound_statement /\
    audit_dense_prepare_whole_input_bound_statement /\
  audit_slot_lookup_whole_input_bound_statement /\ audit_slot_update_whole_input_bound_statement /\
  audit_slot_remove_whole_input_bound_statement /\
    audit_slot_elements_whole_input_bound_statement /\
  audit_slot_of_map_whole_input_bound_statement /\ audit_slot_to_map_whole_input_bound_statement /\
  audit_dense_token_prepare_whole_input_bound_statement /\
  audit_dense_token_read_whole_input_bound_statement /\
    audit_prepare_slot_whole_input_bound_statement /\
  audit_slot_read_whole_input_bound_statement /\ audit_prepare_slots_whole_input_bound_statement /\
  audit_read_slots_whole_input_bound_statement.

(** Final collection closure binds foreign source bodies and every independent internal input
  budget. *)
Definition audit_cl_public_source_contract_statement : Prop :=
  audit_cl_adapted_source_contract_statement /\ audit_cl_dense_whole_source_contract_statement.
```

Card: AUD-CL

Future proof module: `Galois.Collections.CollectionsAuditFamilyClosureAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditFamilyClosure.

Theorem audit_cl_primitive_erasure_closure : audit_cl_primitive_erasure_closure_statement.
Theorem audit_cl_source_work_closure : audit_cl_source_work_closure_statement.
Theorem audit_cl_composite_union_find_closure : audit_cl_composite_union_find_closure_statement.
Theorem audit_cl_full_source_contract : audit_cl_full_source_contract_statement.
Theorem audit_cl_literal_body_closure : audit_cl_literal_body_closure_statement.
Theorem audit_cl_whole_input_closure : audit_cl_whole_input_closure_statement.
Theorem audit_cl_complete_source_contract : audit_cl_complete_source_contract_statement.
Theorem audit_cl_adapted_source_contract : audit_cl_adapted_source_contract_statement.
Theorem audit_cl_dense_whole_source_contract : audit_cl_dense_whole_source_contract_statement.
Theorem audit_cl_public_source_contract : audit_cl_public_source_contract_statement.
```

## CollectionsAuditFinSet

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditFinSet.v`.

Public module:
`Galois.Collections.CollectionsAuditFinSet`.

```rocq
(** * Counted finite-set construction

    These mirrors preserve each actual encoded key, intermediate set and trie operation.
    For example, repeated input keys retain separate insertion events.
    Builds on: CollectionsFinSet and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

(** * Actual update and lookup calls *)

Inductive audit_set_event (K E : Type) : Type :=
  | AuditSetAdd (key : K) (code : positive) (input output : FinSet.t K)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetMem (key : K) (code : positive) (input : FinSet.t K) (output : bool)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetRemove (key : K) (code : positive) (input output : FinSet.t K)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * unit)))
  | AuditSetFold (remaining : list K) (input : FinSet.t K).

Arguments AuditSetAdd {K E} _ _ _ _ _ _.
Arguments AuditSetMem {K E} _ _ _ _ _ _.
Arguments AuditSetRemove {K E} _ _ _ _ _ _.
Arguments AuditSetFold {K E} _ _.

(** Add retains the concrete encoded key, source trie input and rebuilt trie. *)
Definition audit_finset_add {K E} (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : FinSet.t K * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_set code (key, tt) input in
  (output, [AuditSetAdd key code input output ee te]).

Definition audit_finset_mem {K E} (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : bool * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(found, te) := audit_map_code_get code input in
  let output := match found with Some _ => true | None => false end in
  (output, [AuditSetMem key code input output ee te]).

Definition audit_finset_remove {K E}
    (enc : K -> positive * list E) (key : K) (input : FinSet.t K)
    : FinSet.t K * list (audit_set_event K E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_remove code input in
  (output, [AuditSetRemove key code input output ee te]).

(** This fold keeps the actual accumulator at every occurrence and at termination. *)
Fixpoint audit_finset_fold {K E} (enc : K -> positive * list E)
    (remaining : list K) (input : FinSet.t K) : FinSet.t K * list (audit_set_event K E) :=
  match remaining with
  | [] => (input, [AuditSetFold remaining input])
  | key :: rest =>
      let '(next, call) := audit_finset_add enc key input in
      let '(output, events) := audit_finset_fold enc rest next in
      (output, AuditSetFold remaining input :: call ++ events)
  end.

Definition audit_finset_of_list {K E} (enc : K -> positive * list E) (input : list K)
    : FinSet.t K * list (audit_set_event K E) := audit_finset_fold enc input FinSet.empty.

(** * Future proof obligations *)

Definition audit_finset_of_list_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) (input : list K),
    (forall key, In key input -> fst (enc key) = encode original key) ->
    fst (audit_finset_of_list enc input) = FinSet.of_list original input.

Definition audit_finset_of_list_count_statement : Prop :=
  forall K E (enc : K -> positive * list E) (input : list K),
    length (snd (audit_finset_of_list enc input)) = S (2 * length input).

Definition audit_finset_add_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_add enc key input) = FinSet.add original key input.

Definition audit_finset_mem_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_mem enc key input) = FinSet.mem original key input.

Definition audit_finset_remove_erases_statement : Prop :=
  forall K E (enc : K -> positive * list E) (original : encoding K) key input,
    fst (enc key) = encode original key ->
    fst (audit_finset_remove enc key input) = FinSet.remove original key input.

(** * Fixed source-frame charges and original-key budget *)

Fixpoint audit_finset_source_work {K E} (encoder_work : list E -> nat)
    (events : list (audit_set_event K E)) : nat :=
  match events with
  | [] => 0
  | AuditSetAdd _ _ _ _ ee te :: rest =>
      2 + encoder_work ee + audit_trie_update_trace_source_work te +
        audit_finset_source_work encoder_work rest
  | AuditSetMem _ _ _ output ee te :: rest =>
      2 + encoder_work ee + audit_trie_get_trace_source_work te +
        (if output then 4 else 2) + audit_finset_source_work encoder_work rest
  | AuditSetRemove _ _ _ _ ee te :: rest =>
      2 + encoder_work ee + audit_trie_update_trace_source_work te +
        audit_finset_source_work encoder_work rest
  | AuditSetFold _ _ :: rest => 1 + audit_finset_source_work encoder_work rest
  end.

Fixpoint audit_finset_of_list_budget {K E} (enc : K -> positive * list E)
    (encoder_work : list E -> nat) (input : list K) : nat :=
  match input with
  | [] => 1
  | key :: rest =>
      3 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)) +
        audit_finset_of_list_budget enc encoder_work rest
  end.

Definition audit_finset_of_list_source_bound_statement : Prop :=
  forall K E (enc : K -> positive * list E) encoder_work input,
    audit_finset_source_work encoder_work (snd (audit_finset_of_list enc input)) <=
      audit_finset_of_list_budget enc encoder_work input.
```

Card: AUD-CL-TRIE

Future proof module: `Galois.Collections.CollectionsAuditFinSetAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditFinSet.

Theorem audit_finset_of_list_erases : audit_finset_of_list_erases_statement.
Theorem audit_finset_of_list_count : audit_finset_of_list_count_statement.
Theorem audit_finset_add_erases : audit_finset_add_erases_statement.
Theorem audit_finset_mem_erases : audit_finset_mem_erases_statement.
Theorem audit_finset_remove_erases : audit_finset_remove_erases_statement.
Theorem audit_finset_of_list_source_bound : audit_finset_of_list_source_bound_statement.
```

## CollectionsAuditHistorical

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditHistorical.v`.

Public module:
`Galois.Collections.CollectionsAuditHistorical`.

```rocq
(** Historical selected-event counters; not full source-runtime accounting. *)
From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsUnionFind.
From Galois.Collections Require Import CollectionsAuditState.
Import List.ListNotations.
Record slot_batch_work : Type := SlotBatchWork {
  slot_reads : nat;
  slot_key_bits : nat
}.

Fixpoint read_slots_counted {V} (m : slot_map V) (slots : list (option N)) :
    list (option V) * slot_batch_work :=
  match slots with
  | [] => ([], SlotBatchWork 0 0)
  | None :: rest =>
    let '(out, work) := read_slots_counted m rest in (None :: out, work)
  | Some i :: rest =>
    let '(out, work) := read_slots_counted m rest in
    (slot_read m i :: out, SlotBatchWork (S (slot_reads work))
      (Pos.size_nat (encode N_encoding i) + slot_key_bits work))
  end.

Definition slot_batch_cost_statement : Prop :=
  forall V (m : slot_map V) slots,
    let '(out, work) := read_slots_counted m slots in
    out = read_slots m slots /\ length out = length slots /\
    slot_reads work = length (filter (fun s => match s with Some _ => true | None => false end)
      slots) /\
    slot_key_bits work = fold_right (fun slot bits => match slot with
      | Some i => Pos.size_nat (encode N_encoding i) + bits
      | None => bits
      end) 0 slots.
Inductive union_action (K : Type) : Type :=
  | FindAction (x : K)
  | UnionAction (x y : K).

Arguments FindAction {K}.
Arguments UnionAction {K}.

Definition action_step {K} (E : encoding K) (a : union_action K) (uf : UnionFind.t K) :
    UnionFind.t K :=
  match a with
  | FindAction x => snd (UnionFind.find E x uf)
  | UnionAction x y => UnionFind.union E x y uf
  end.

Inductive union_event (K : Type) : Type :=
  | UFFuelCheck (remaining : nat)
  | UFParentGet (key : K)
  | UFParentSet (key : K)
  | UFRankGet (key : K)
  | UFRankSet (key : K)
  | UFKeyCompare (left right : K)
  | UFRankCompare (left right : nat)
  | UFRankSuccessor (rank : nat)
  | UFRankMax (left right : nat).
Arguments UFFuelCheck {K}.
Arguments UFParentGet {K}.
Arguments UFParentSet {K}.
Arguments UFRankGet {K}.
Arguments UFRankSet {K}.
Arguments UFKeyCompare {K}.
Arguments UFRankCompare {K}.
Arguments UFRankSuccessor {K}.
Arguments UFRankMax {K}.

Fixpoint trace_find_fuel {K} (E : encoding K) (fuel : nat) (x : K) (uf : UnionFind.t K)
    : (K * UnionFind.t K) * list (union_event K) :=
  match fuel with
  | 0 => ((x, uf), [UFFuelCheck 0])
  | S rest =>
    match Map.get E x (UnionFind.parents uf) with
    | None => ((x, uf), [UFFuelCheck (S rest); UFParentGet x])
    | Some y =>
      let '(result, events) := trace_find_fuel E rest y uf in
      let '(root, compressed) := result in
      ((root, UnionFind.redirect E x root compressed),
        UFFuelCheck (S rest) :: UFParentGet x :: events ++ [UFParentSet x])
    end
  end.

Definition trace_find {K} (E : encoding K) (x : K) (uf : UnionFind.t K) :=
  trace_find_fuel E (S (UnionFind.max_rank uf)) x uf.

Definition trace_union {K} (E : encoding K) (x y : K) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  let '(first, e1) := trace_find E x uf in
  let '(rx, uf1) := first in
  let '(second, e2) := trace_find E y uf1 in
  let '(ry, uf2) := second in
  let prefix := e1 ++ e2 ++ [UFKeyCompare rx ry] in
  if UnionFind.key_eqb E rx ry then
    match Map.get E rx (UnionFind.ranks uf2) with
    | Some _ => (uf2, prefix ++ [UFRankGet rx])
    | None => (UnionFind.Forest (UnionFind.parents uf2)
        (Map.set E rx 0 (UnionFind.ranks uf2)) (UnionFind.max_rank uf2),
        prefix ++ [UFRankGet rx; UFRankSet rx])
    end
  else
    let rankx := UnionFind.rank_of E uf2 rx in
    let ranky := UnionFind.rank_of E uf2 ry in
    let ranked := prefix ++ [UFRankGet rx; UFRankGet ry; UFRankCompare rankx ranky] in
    match Nat.compare rankx ranky with
    | Lt => (UnionFind.link E rx ry false uf2, ranked ++ [UFParentSet rx])
    | Gt => (UnionFind.link E ry rx false uf2, ranked ++ [UFParentSet ry])
    | Eq => (UnionFind.link E ry rx true uf2,
        ranked ++ [UFRankGet rx; UFRankSuccessor rankx; UFParentSet ry; UFRankSet rx;
          UFRankMax (UnionFind.max_rank uf2) (S rankx)])
    end.

Definition trace_find_result_statement : Prop :=
  forall K (E : encoding K) x uf, fst (trace_find E x uf) = UnionFind.find E x uf.
Definition trace_union_result_statement : Prop :=
  forall K (E : encoding K) x y uf, fst (trace_union E x y uf) = UnionFind.union E x y uf.

Definition event_keys {K} (event : union_event K) : list K :=
  match event with
  | UFParentGet k | UFParentSet k | UFRankGet k | UFRankSet k => [k]
  | UFKeyCompare a b => [a; b]
  | _ => []
  end.

Definition event_key_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => fold_right (fun k n => Pos.size_nat (encode E k) + n)
    total (event_keys event)) 0 events.

Record union_callback_costs (K : Type) : Type := UnionCallbackCosts {
  union_encode_work : K -> nat
}.
Arguments union_encode_work {K}.

Definition event_encode_work {K} (costs : union_callback_costs K) (events : list (union_event K))
  : nat :=
  fold_right (fun event total => fold_right (fun k n => union_encode_work costs k + n)
    total (event_keys event)) 0 events.

Definition event_unary_work {K} (event : union_event K) : nat :=
  match event with
  | UFRankCompare a b | UFRankMax a b => S (Nat.min a b)
  | UFRankSuccessor _ | UFFuelCheck _ => 1
  | _ => 0
  end.

Definition event_unary_total {K} (events : list (union_event K)) : nat :=
  fold_right (fun event total => event_unary_work event + total) 0 events.

Definition trace_action {K} (E : encoding K) (action : union_action K) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  match action with
  | FindAction x => let '(r, events) := trace_find E x uf in (snd r, events)
  | UnionAction x y => trace_union E x y uf
  end.

Fixpoint trace_actions {K} (E : encoding K) (actions : list (union_action K)) (uf : UnionFind.t K)
    : UnionFind.t K * list (union_event K) :=
  match actions with
  | [] => (uf, [])
  | action :: rest =>
    let '(next, first) := trace_action E action uf in
    let '(last, tail) := trace_actions E rest next in (last, first ++ tail)
  end.

Definition trace_actions_result_statement : Prop :=
  forall K (E : encoding K) actions uf,
    fst (trace_actions E actions uf) = fold_left (fun state action => action_step E action state)
      actions uf.

Definition trace_branches {K} (E : encoding K) (uf : UnionFind.t K)
    (left right : list (union_action K)) : list (union_event K) :=
  snd (trace_actions E left uf) ++ snd (trace_actions E right uf).

Definition trace_branch_sum_statement : Prop :=
  forall K (E : encoding K) (uf : UnionFind.t K) left right,
    event_key_bits E (trace_branches E uf left right) =
      event_key_bits E (snd (trace_actions E left uf)) + event_key_bits E (snd (trace_actions E
        right uf)) /\
    event_unary_total (trace_branches E uf left right) =
      event_unary_total (snd (trace_actions E left uf)) + event_unary_total (snd (trace_actions E
        right uf)).

Record union_callback_cost_laws {K} (observed bound : union_callback_costs K) : Prop := {
  union_encode_bound : forall k, union_encode_work observed k <= union_encode_work bound k
}.

Definition union_map_gets {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with UFParentGet _ | UFRankGet _ => S n | _ => n end) 0
    events.
Definition union_map_sets {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with UFParentSet _ | UFRankSet _ => S n | _ => n end) 0
    events.
Definition union_comparisons {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with UFKeyCompare _ _ => S n | _ => n end) 0 events.
Definition union_fuel_checks {K} (events : list (union_event K)) : nat :=
  fold_right (fun event n => match event with UFFuelCheck _ => S n | _ => n end) 0 events.
Definition union_trie_read_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFParentGet k | UFRankGet k => Pos.size_nat (encode E k) + total
    | _ => total end) 0 events.
Definition union_trie_write_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFParentSet k | UFRankSet k => Pos.size_nat (encode E k) + total
    | _ => total end) 0 events.
Definition union_key_compare_bits {K} (E : encoding K) (events : list (union_event K)) : nat :=
  fold_right (fun event total => match event with
    | UFKeyCompare a b => Pos.size_nat (encode E a) + Pos.size_nat (encode E b) + total
    | _ => total end) 0 events.

Record union_source_work : Type := UnionSourceWork {
  union_work_gets : nat;
  union_work_sets : nat;
  union_work_fuel_checks : nat;
  union_work_key_comparisons : nat;
  union_work_read_bits : nat;
  union_work_write_bits : nat;
  union_work_compare_bits : nat;
  union_work_encoder : nat;
  union_work_unary : nat;
  union_work_event_count : nat;
  union_work_actions : nat
}.

Definition union_trace_work {K} (E : encoding K) (costs : union_callback_costs K)
    (actions : list (union_action K)) (events : list (union_event K)) : union_source_work :=
  UnionSourceWork (union_map_gets events) (union_map_sets events) (union_fuel_checks events)
    (union_comparisons events) (union_trie_read_bits E events) (union_trie_write_bits E events)
    (union_key_compare_bits E events) (event_encode_work costs events) (event_unary_total events)
    (length events) (length actions).

Definition union_source_work_statement : Prop :=
  forall K (E : encoding K) actions uf costs,
    let '(result, events) := trace_actions E actions uf in
    let work := union_trace_work E costs actions events in
    result = fold_left (fun state action => action_step E action state) actions uf /\
    union_work_read_bits work + union_work_write_bits work + union_work_compare_bits work =
      event_key_bits E events /\
    union_work_actions work = length actions /\ union_work_event_count work = length events.

(** The named prepared-key contract combines exact functional and composite-length laws. *)
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditHistoricalDENSEAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditHistorical.

Theorem slot_batch_cost : slot_batch_cost_statement.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditHistoricalUFAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditHistorical.

Theorem trace_find_result : trace_find_result_statement.
Theorem trace_union_result : trace_union_result_statement.
Theorem trace_actions_result : trace_actions_result_statement.
Theorem trace_branch_sum : trace_branch_sum_statement.
Theorem union_source_work : union_source_work_statement.
```

## CollectionsAuditInter

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditInter.v`.

Public module:
`Galois.Collections.CollectionsAuditInter`.

```rocq
(** * Counted finite-set intersection

    This mirror retains merge recursion and the original one-sided filtering work.
    For example, intersecting a nonempty tree with empty still visits its filtered nodes.
    Builds on: CollectionsFinSet and the shared trie model. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_inter_event (K : Type) : Type :=
  | AuditInterRoot (left right : FinSet.t K)
  | AuditInterMerge (node : Trie.ne (K * unit)) (other : FinSet.t K)
  | AuditInterDrop (node : Trie.ne (K * unit))
  | AuditInterDiscard (value : K * unit)
  | AuditInterValue (left right output : option (K * unit))
  | AuditInterNode (left : FinSet.t K) (value : option (K * unit)) (right output : FinSet.t K).

Arguments AuditInterRoot {K} _ _.
Arguments AuditInterMerge {K} _ _.
Arguments AuditInterDrop {K} _.
Arguments AuditInterDiscard {K} _.
Arguments AuditInterValue {K} _ _ _.
Arguments AuditInterNode {K} _ _ _ _.

(** A one-sided [Trie.filter_ne] still visits each node and rebuilds the empty result. *)
Fixpoint audit_inter_drop_ne {K} (node : Trie.ne (K * unit))
    : FinSet.t K * list (audit_inter_event K) :=
  let enter := [AuditInterDrop node] in
  match node with
  | Trie.N001 r =>
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node Trie.Empty None rr in
      (out, enter ++ re ++ [AuditInterNode Trie.Empty None rr out])
  | Trie.N010 value =>
      let out := Trie.node Trie.Empty None Trie.Empty in
      (out, enter ++ [AuditInterDiscard value; AuditInterNode Trie.Empty None Trie.Empty out])
  | Trie.N011 value r =>
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node Trie.Empty None rr in
      (out, enter ++ [AuditInterDiscard value] ++ re ++ [AuditInterNode Trie.Empty None rr out])
  | Trie.N100 l =>
      let '(ll, le) := audit_inter_drop_ne l in
      let out := Trie.node ll None Trie.Empty in
      (out, enter ++ le ++ [AuditInterNode ll None Trie.Empty out])
  | Trie.N101 l r =>
      let '(ll, le) := audit_inter_drop_ne l in
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node ll None rr in
      (out, enter ++ le ++ re ++ [AuditInterNode ll None rr out])
  | Trie.N110 l value =>
      let '(ll, le) := audit_inter_drop_ne l in
      let out := Trie.node ll None Trie.Empty in
      (out, enter ++ le ++ [AuditInterDiscard value; AuditInterNode ll None Trie.Empty out])
  | Trie.N111 l value r =>
      let '(ll, le) := audit_inter_drop_ne l in
      let '(rr, re) := audit_inter_drop_ne r in
      let out := Trie.node ll None rr in
      (out, enter ++ le ++ [AuditInterDiscard value] ++ re ++ [AuditInterNode ll None rr out])
  end.

Definition audit_inter_drop {K} (input : FinSet.t K) : FinSet.t K * list (audit_inter_event K) :=
  match input with
  | Trie.Empty => (Trie.Empty, [])
  | Trie.Nodes node => audit_inter_drop_ne node
  end.

(** [Map.combine_pair] retains the left key only when both sides are present. *)
Definition audit_inter_value {K} (a b : option (K * unit))
    : option (K * unit) * list (audit_inter_event K) :=
  let out := match a, b with Some (key, _), Some _ => Some (key, tt) | _, _ => None end in
  (out, [AuditInterValue a b out]).

(** The seven merge cases reproduce both original recursive and one-sided filtering calls. *)
Fixpoint audit_inter_merge_ne {K} (node : Trie.ne (K * unit)) (other : FinSet.t K)
    : FinSet.t K * list (audit_inter_event K) :=
  let enter := [AuditInterMerge node other] in
  match other with
  | Trie.Empty =>
      let '(out, events) := audit_inter_drop_ne node in (out, enter ++ events)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node l v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v rr
            out])
      | Trie.N010 kv =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node l v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v r out])
      | Trie.N011 kv r =>
          let '(l, le) := audit_inter_drop (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node l v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode l v rr
            out])
      | Trie.N100 l =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node ll v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v r
            out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value None (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node ll v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v rr
            out])
      | Trie.N110 l kv =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(r, re) := audit_inter_drop (Trie.right other) in
          let out := Trie.node ll v r in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v r
            out])
      | Trie.N111 l kv r =>
          let '(ll, le) := audit_inter_merge_ne l (Trie.left other) in
          let '(v, ve) := audit_inter_value (Some kv) (Trie.value other) in
          let '(rr, re) := audit_inter_merge_ne r (Trie.right other) in
          let out := Trie.node ll v rr in (out, enter ++ le ++ ve ++ re ++ [AuditInterNode ll v rr
            out])
      end
  end.

Definition audit_finset_inter {K} (left right : FinSet.t K)
    : FinSet.t K * list (audit_inter_event K) :=
  match left with
  | Trie.Empty =>
      let '(out, events) := audit_inter_drop right in (out, AuditInterRoot left right :: events)
  | Trie.Nodes node =>
      let '(out, events) := audit_inter_merge_ne node right in
      (out, AuditInterRoot left right :: events)
  end.

(** The result and original-tree bound are future theorem obligations. *)
Definition audit_finset_inter_erases_statement : Prop :=
  forall K (enc : encoding K) (left right : FinSet.t K),
    fst (audit_finset_inter left right) = FinSet.inter enc left right.

Definition audit_finset_inter_count_statement : Prop :=
  forall K (left right : FinSet.t K),
    length (snd (audit_finset_inter left right)) <=
      1 + 6 * (audit_trie_nodes left + audit_trie_nodes right).

(** Fixed local source-block charges include actual one-sided filter and node work. *)
Fixpoint audit_finset_inter_source_work {K} (events : list (audit_inter_event K)) : nat :=
  match events with
  | [] => 0
  | AuditInterRoot _ _ :: rest => 2 + audit_finset_inter_source_work rest
  | AuditInterMerge _ _ :: rest => 12 + audit_finset_inter_source_work rest
  | AuditInterDrop _ :: rest => 9 + audit_finset_inter_source_work rest
  | AuditInterDiscard _ :: rest => 4 + audit_finset_inter_source_work rest
  | AuditInterValue _ _ _ :: rest => 7 + audit_finset_inter_source_work rest
  | AuditInterNode l value r _ :: rest =>
      audit_trie_node_work l value r + audit_finset_inter_source_work rest
  end.

Definition audit_finset_inter_source_bound_statement : Prop :=
  forall K (left right : FinSet.t K),
    audit_finset_inter_source_work (snd (audit_finset_inter left right)) <=
      2 + 30 * (audit_trie_nodes left + audit_trie_nodes right).
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditInterAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditInter.

Theorem audit_finset_inter_erases : audit_finset_inter_erases_statement.
Theorem audit_finset_inter_count : audit_finset_inter_count_statement.
Theorem audit_finset_inter_source_bound : audit_finset_inter_source_bound_statement.
```

## CollectionsAuditMap

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditMap.v`.

Public module:
`Galois.Collections.CollectionsAuditMap`.

```rocq
(** * Counted encoded map calls

    These mirrors compose real encoding calls with trie lookups, writes and removals.
    For example, a missing key still records its actual code and selected trie path.
    Builds on: CollectionsMap and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_map_event (K V E : Type) : Type :=
  | AuditMapGet (key : K) (code : positive) (input : Map.t K V) (output : option V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V)))
  | AuditMapSet (key : K) (value : V) (code : positive) (input output : Map.t K V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V)))
  | AuditMapRemove (key : K) (code : positive) (input output : Map.t K V)
      (encoding_events : list E) (trie_events : audit_trace (audit_trie_call (K * V))).

Arguments AuditMapGet {K V E} _ _ _ _ _ _.
Arguments AuditMapSet {K V E} _ _ _ _ _ _ _.
Arguments AuditMapRemove {K V E} _ _ _ _ _ _.

(** Lookup composes the encoder and code lookup on precisely the returned code. *)
Definition audit_map_get {K V E} (enc : K -> positive * list E) (key : K) (input : Map.t K V)
    : option V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_map_code_get code input in
  (output, [AuditMapGet key code input output ee te]).

Definition audit_map_set {K V E} (enc : K -> positive * list E)
    (key : K) (value : V) (input : Map.t K V)
    : Map.t K V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_set code (key, value) input in
  (output, [AuditMapSet key value code input output ee te]).

Definition audit_map_remove {K V E} (enc : K -> positive * list E)
    (key : K) (input : Map.t K V) : Map.t K V * list (audit_map_event K V E) :=
  let '(code, ee) := enc key in
  let '(output, te) := audit_trie_remove code input in
  (output, [AuditMapRemove key code input output ee te]).

(** * Future proof obligations *)

Definition audit_map_get_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key (input : Map.t K V),
    fst (enc key) = encode original key -> fst (audit_map_get enc key input) = Map.get original
      key input.

Definition audit_map_set_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key value
      (input : Map.t K V),
    fst (enc key) = encode original key ->
    fst (audit_map_set enc key value input) = Map.set original key value input.

Definition audit_map_remove_erases_statement : Prop :=
  forall K V E (enc : K -> positive * list E) (original : encoding K) key (input : Map.t K V),
    fst (enc key) = encode original key ->
    fst (audit_map_remove enc key input) = Map.remove original key input.

(** * Same-call fixed source-frame folds *)

(** The encoder fold observes its actual child trace; internal bodies need their own proof. *)
Fixpoint audit_map_source_work {K V E} (encoder_work : list E -> nat)
    (events : list (audit_map_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapGet _ _ _ output enc_events trie_events :: rest =>
      1 + encoder_work enc_events + audit_trie_get_trace_source_work trie_events +
        (match output with None => 2 | Some _ => 4 end) + audit_map_source_work encoder_work rest
  | AuditMapSet _ _ _ _ _ enc_events trie_events :: rest =>
      2 + encoder_work enc_events + audit_trie_update_trace_source_work trie_events +
        audit_map_source_work encoder_work rest
  | AuditMapRemove _ _ _ _ enc_events trie_events :: rest =>
      2 + encoder_work enc_events + audit_trie_update_trace_source_work trie_events +
        audit_map_source_work encoder_work rest
  end.

(** Bounds refer to the actual input key and actual child encoding trace, not a client price law. *)
Definition audit_map_get_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_get enc key input)) <=
      5 + encoder_work (snd (enc key)) + 5 * Pos.size_nat (fst (enc key)).

Definition audit_map_set_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key value (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_set enc key value input)) <=
      2 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).

Definition audit_map_remove_source_work_bound_statement : Prop :=
  forall K V E (enc : K -> positive * list E) encoder_work key (input : Map.t K V),
    audit_map_source_work encoder_work (snd (audit_map_remove enc key input)) <=
      2 + encoder_work (snd (enc key)) + 16 * Pos.size_nat (fst (enc key)).
```

Card: AUD-CL-TRIE

Future proof module: `Galois.Collections.CollectionsAuditMapAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditMap.

Theorem audit_map_get_erases : audit_map_get_erases_statement.
Theorem audit_map_set_erases : audit_map_set_erases_statement.
Theorem audit_map_remove_erases : audit_map_remove_erases_statement.
Theorem audit_map_get_source_work_bound : audit_map_get_source_work_bound_statement.
Theorem audit_map_set_source_work_bound : audit_map_set_source_work_bound_statement.
Theorem audit_map_remove_source_work_bound : audit_map_remove_source_work_bound_statement.
```

## CollectionsAuditMapFold

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditMapFold.v`.

Public module:
`Galois.Collections.CollectionsAuditMapFold`.

```rocq
(** * Counted map fold

    This mirror retains each accumulator, stored key, value and computed trie position.
    For example, an accumulator of false does not stop later callback applications.
    Builds on: CollectionsMap and the audit trie enumeration measure. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap.
From Galois.Collections Require Import CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_map_fold_event (K V B E : Type) : Type :=
  | AuditMapFoldNode (node : Trie.ne (K * V)) (acc : B)
  | AuditMapFoldCall (position : positive) (key : K) (value : V)
      (before after : B) (events : list E).

Arguments AuditMapFoldNode {K V B E} _ _.
Arguments AuditMapFoldCall {K V B E} _ _ _ _ _ _.

(** The original position is computed even though [Map.fold] discards it in its callback. *)
Fixpoint audit_map_fold_ne {K V B E} (f : B -> K -> V -> B * list E)
    (path : positive -> positive) (node : Trie.ne (K * V)) (acc : B)
    : B * list (audit_map_fold_event K V B E) :=
  let here := [AuditMapFoldNode node acc] in
  match node with
  | Trie.N001 r =>
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r acc in (out, here ++ re)
  | Trie.N010 (key, value) =>
      let position := path xH in
      let '(out, ce) := f acc key value in
      (out, here ++ [AuditMapFoldCall position key value acc out ce])
  | Trie.N011 (key, value) r =>
      let position := path xH in
      let '(middle, ce) := f acc key value in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r middle in
      (out, here ++ [AuditMapFoldCall position key value acc middle ce] ++ re)
  | Trie.N100 l =>
      let '(out, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in (out, here ++ le)
  | Trie.N101 l r =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r middle in
      (out, here ++ le ++ re)
  | Trie.N110 l (key, value) =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let position := path xH in
      let '(out, ce) := f middle key value in
      (out, here ++ le ++ [AuditMapFoldCall position key value middle out ce])
  | Trie.N111 l (key, value) r =>
      let '(middle, le) := audit_map_fold_ne f (fun p => path (xO p)) l acc in
      let position := path xH in
      let '(next, ce) := f middle key value in
      let '(out, re) := audit_map_fold_ne f (fun p => path (xI p)) r next in
      (out, here ++ le ++ [AuditMapFoldCall position key value middle next ce] ++ re)
  end.

Definition audit_map_fold {K V B E} (f : B -> K -> V -> B * list E) (input : Map.t K V)
    (acc : B) : B * list (audit_map_fold_event K V B E) :=
  match input with
  | Trie.Empty => (acc, [])
  | Trie.Nodes node => audit_map_fold_ne f (fun p => p) node acc
  end.

Definition audit_map_fold_erases_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) (original : B -> K -> V -> B)
      (input : Map.t K V) acc,
    (forall b k v, fst (f b k v) = original b k v) ->
    fst (audit_map_fold f input acc) = Map.fold original input acc.

(** Node/call counts do not include the separately expanded callback's body. *)
Definition audit_map_fold_count_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) (input : Map.t K V) acc,
    length (snd (audit_map_fold f input acc)) <= 2 * audit_trie_nodes input.

(** Fixed node and position charges include actual position reconstruction. *)
Fixpoint audit_map_fold_source_work {K V B E} (child_work : list E -> nat)
    (events : list (audit_map_fold_event K V B E)) : nat :=
  match events with
  | [] => 0
  | AuditMapFoldNode _ _ :: rest => 10 + audit_map_fold_source_work child_work rest
  | AuditMapFoldCall position _ _ _ _ child :: rest =>
      3 + Pos.size_nat position + child_work child + audit_map_fold_source_work child_work rest
  end.

Fixpoint audit_map_fold_child_work {K V B E} (child_work : list E -> nat)
    (events : list (audit_map_fold_event K V B E)) : nat :=
  match events with
  | [] => 0
  | AuditMapFoldCall _ _ _ _ _ child :: rest =>
      child_work child + audit_map_fold_child_work child_work rest
  | _ :: rest => audit_map_fold_child_work child_work rest
  end.

(** The input-derived outer work excludes only the explicitly retained child executions. *)
Definition audit_map_fold_source_work_bound_statement : Prop :=
  forall K V B E (f : B -> K -> V -> B * list E) child_work (input : Map.t K V) acc,
    let events := snd (audit_map_fold f input acc) in
    audit_map_fold_source_work child_work events <=
      13 * audit_trie_nodes input + audit_trie_output_bits input +
      audit_map_fold_child_work child_work events.
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditMapFoldAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditMapFold.

Theorem audit_map_fold_erases : audit_map_fold_erases_statement.
Theorem audit_map_fold_count : audit_map_fold_count_statement.
Theorem audit_map_fold_source_work_bound : audit_map_fold_source_work_bound_statement.
```

## CollectionsAuditMapTraverse

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditMapTraverse.v`.

Public module:
`Galois.Collections.CollectionsAuditMapTraverse`.

```rocq
(** * Counted map transformations

    These mirrors retain every visited trie node and actual value callback operand and result.
    For example, a singleton map invokes its mapper exactly once.
    Builds on: CollectionsMap and the audit enumeration node measure. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsTrie CollectionsMap.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditElements.
Import List.ListNotations.

Inductive audit_map_transform_event (K V W E : Type) : Type :=
  | AuditMapTransformNode (node : Trie.ne (K * V))
  | AuditMapTransformCall (key : K) (input : V) (output : W) (events : list E)
  | AuditMapTransformBuilt (left : Trie.t (K * W)) (value : option (K * W))
      (right output : Trie.t (K * W)).

Arguments AuditMapTransformNode {K V W E} _.
Arguments AuditMapTransformCall {K V W E} _ _ _ _.
Arguments AuditMapTransformBuilt {K V W E} _ _ _ _.

(** This follows the seven branches of [Trie.filter_ne] used by [Map.map]. *)
Fixpoint audit_map_transform_ne {K V W E} (f : V -> W * list E) (node : Trie.ne (K * V))
    : Trie.t (K * W) * list (audit_map_transform_event K V W E) :=
  let here := [AuditMapTransformNode node] in
  match node with
  | Trie.N001 r =>
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node Trie.Empty None rr in
      (out, here ++ re ++ [AuditMapTransformBuilt Trie.Empty None rr out])
  | Trie.N010 (key, value) =>
      let '(v, ve) := f value in
      let out := Trie.node Trie.Empty (Some (key, v)) Trie.Empty in
      (out, here ++ [AuditMapTransformCall key value v ve;
                     AuditMapTransformBuilt Trie.Empty (Some (key, v)) Trie.Empty out])
  | Trie.N011 (key, value) r =>
      let '(v, ve) := f value in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node Trie.Empty (Some (key, v)) rr in
      (out, here ++ [AuditMapTransformCall key value v ve] ++ re ++
        [AuditMapTransformBuilt Trie.Empty (Some (key, v)) rr out])
  | Trie.N100 l =>
      let '(ll, le) := audit_map_transform_ne f l in
      let out := Trie.node ll None Trie.Empty in
      (out, here ++ le ++ [AuditMapTransformBuilt ll None Trie.Empty out])
  | Trie.N101 l r =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node ll None rr in
      (out, here ++ le ++ re ++ [AuditMapTransformBuilt ll None rr out])
  | Trie.N110 l (key, value) =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(v, ve) := f value in
      let out := Trie.node ll (Some (key, v)) Trie.Empty in
      (out, here ++ le ++ [AuditMapTransformCall key value v ve;
                           AuditMapTransformBuilt ll (Some (key, v)) Trie.Empty out])
  | Trie.N111 l (key, value) r =>
      let '(ll, le) := audit_map_transform_ne f l in
      let '(v, ve) := f value in
      let '(rr, re) := audit_map_transform_ne f r in
      let out := Trie.node ll (Some (key, v)) rr in
      (out, here ++ le ++ [AuditMapTransformCall key value v ve] ++ re ++
        [AuditMapTransformBuilt ll (Some (key, v)) rr out])
  end.

Definition audit_map_transform {K V W E} (f : V -> W * list E) (input : Map.t K V)
    : Map.t K W * list (audit_map_transform_event K V W E) :=
  match input with
  | Trie.Empty => (Trie.Empty, [])
  | Trie.Nodes node => audit_map_transform_ne f node
  end.

(** These claims compare the actual same inputs and bound outer frames by input nodes. *)
Definition audit_map_transform_erases_statement : Prop :=
  forall K V W E (f : V -> W * list E) (original : V -> W) (input : Map.t K V),
    (forall value, fst (f value) = original value) ->
    fst (audit_map_transform f input) = Map.map original input.

Definition audit_map_transform_count_statement : Prop :=
  forall K V W E (f : V -> W * list E) (node : Trie.ne (K * V)),
    length (snd (audit_map_transform_ne f node)) <= 3 * audit_elements_nodes node.

(** * Map union with typed overlapping-value calls *)

Inductive audit_map_union_event (K V E : Type) : Type :=
  | AuditMapUnionEnter (node : Trie.ne (K * V)) (other : Map.t K V)
  | AuditMapUnionCall (left_key right_key : K) (left_value right_value output : V)
      (events : list E)
  | AuditMapUnionBuilt (left : Map.t K V) (value : option (K * V))
      (right output : Map.t K V)
  | AuditMapUnionRoot (left right : Map.t K V).

Arguments AuditMapUnionEnter {K V E} _ _.
Arguments AuditMapUnionCall {K V E} _ _ _ _ _ _.
Arguments AuditMapUnionBuilt {K V E} _ _ _ _.
Arguments AuditMapUnionRoot {K V E} _ _.

(** A callback occurs only for overlapping entries, with both original keys and values. *)
Definition audit_map_union_value {K V E} (f : V -> V -> V * list E)
    (a b : option (K * V)) : option (K * V) * list (audit_map_union_event K V E) :=
  match a, b with
  | Some (ka, va), Some (kb, vb) =>
      let '(v, events) := f va vb in
      (Some (ka, v), [AuditMapUnionCall ka kb va vb v events])
  | Some kv, None => (Some kv, [])
  | None, Some kv => (Some kv, [])
  | None, None => (None, [])
  end.

(** The source merges each overlapping node and shares a missing-side subtree. *)
Fixpoint audit_map_union_ne {K V E} (f : V -> V -> V * list E)
    (node : Trie.ne (K * V)) (other : Map.t K V)
    : Map.t K V * list (audit_map_union_event K V E) :=
  let here := [AuditMapUnionEnter node other] in
  match other with
  | Trie.Empty => (Trie.Nodes node, here)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, here ++ ve ++ re ++ [AuditMapUnionBuilt l v rr out])
      | Trie.N010 kv =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node l v r in
          (out, here ++ ve ++ [AuditMapUnionBuilt l v r out])
      | Trie.N011 kv r =>
          let l := Trie.left other in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, here ++ ve ++ re ++ [AuditMapUnionBuilt l v rr out])
      | Trie.N100 l =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, here ++ le ++ ve ++ [AuditMapUnionBuilt ll v r out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f None (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, here ++ le ++ ve ++ re ++ [AuditMapUnionBuilt ll v rr out])
      | Trie.N110 l kv =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, here ++ le ++ ve ++ [AuditMapUnionBuilt ll v r out])
      | Trie.N111 l kv r =>
          let '(ll, le) := audit_map_union_ne f l (Trie.left other) in
          let '(v, ve) := audit_map_union_value f (Some kv) (Trie.value other) in
          let '(rr, re) := audit_map_union_ne f r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, here ++ le ++ ve ++ re ++ [AuditMapUnionBuilt ll v rr out])
      end
  end.

Definition audit_map_union {K V E} (f : V -> V -> V * list E) (left right : Map.t K V)
    : Map.t K V * list (audit_map_union_event K V E) :=
  match left with
  | Trie.Empty => (right, [AuditMapUnionRoot left right])
  | Trie.Nodes node =>
      let '(out, events) := audit_map_union_ne f node right in
      (out, AuditMapUnionRoot left right :: events)
  end.

Definition audit_map_union_erases_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) (original : V -> V -> V) (left right : Map.t K V),
    (forall x y, fst (f x y) = original x y) ->
    fst (audit_map_union f left right) = Map.union_with original left right.

Definition audit_map_union_count_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) (left right : Map.t K V),
    length (snd (audit_map_union f left right)) <=
      1 + 3 * match left with
              | Trie.Empty => 0
              | Trie.Nodes node => audit_elements_nodes node
              end.

(** * Fixed source-frame charges and actual callback traces *)

Fixpoint audit_map_transform_source_work {K V W E} (child_work : list E -> nat)
    (events : list (audit_map_transform_event K V W E)) : nat :=
  match events with
  | [] => 0
  | AuditMapTransformNode _ :: rest => 10 + audit_map_transform_source_work child_work rest
  | AuditMapTransformCall _ _ _ child :: rest =>
      3 + child_work child + audit_map_transform_source_work child_work rest
  | AuditMapTransformBuilt l value r _ :: rest =>
      audit_trie_node_work l value r + audit_map_transform_source_work child_work rest
  end.

Fixpoint audit_map_transform_child_work {K V W E} (child_work : list E -> nat)
    (events : list (audit_map_transform_event K V W E)) : nat :=
  match events with
  | [] => 0
  | AuditMapTransformCall _ _ _ child :: rest =>
      child_work child + audit_map_transform_child_work child_work rest
  | _ :: rest => audit_map_transform_child_work child_work rest
  end.

Definition audit_map_transform_source_bound_statement : Prop :=
  forall K V W E (f : V -> W * list E) child_work (input : Map.t K V),
    let events := snd (audit_map_transform f input) in
    audit_map_transform_source_work child_work events <=
      18 * audit_trie_nodes input + audit_map_transform_child_work child_work events.

Fixpoint audit_map_union_source_work {K V E} (child_work : list E -> nat)
    (events : list (audit_map_union_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapUnionRoot _ _ :: rest => 1 + audit_map_union_source_work child_work rest
  | AuditMapUnionEnter _ _ :: rest => 10 + audit_map_union_source_work child_work rest
  | AuditMapUnionCall _ _ _ _ _ child :: rest =>
      3 + child_work child + audit_map_union_source_work child_work rest
  | AuditMapUnionBuilt l value r _ :: rest =>
      audit_trie_node_work l value r + audit_map_union_source_work child_work rest
  end.

Fixpoint audit_map_union_child_work {K V E} (child_work : list E -> nat)
    (events : list (audit_map_union_event K V E)) : nat :=
  match events with
  | [] => 0
  | AuditMapUnionCall _ _ _ _ _ child :: rest =>
      child_work child + audit_map_union_child_work child_work rest
  | _ :: rest => audit_map_union_child_work child_work rest
  end.

Definition audit_map_union_source_bound_statement : Prop :=
  forall K V E (f : V -> V -> V * list E) child_work (left right : Map.t K V),
    let events := snd (audit_map_union f left right) in
    audit_map_union_source_work child_work events <=
      1 + 18 * audit_trie_nodes left + audit_map_union_child_work child_work events.
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditMapTraverseAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditMapTraverse.

Theorem audit_map_transform_erases : audit_map_transform_erases_statement.
Theorem audit_map_transform_count : audit_map_transform_count_statement.
Theorem audit_map_union_erases : audit_map_union_erases_statement.
Theorem audit_map_union_count : audit_map_union_count_statement.
Theorem audit_map_transform_source_bound : audit_map_transform_source_bound_statement.
Theorem audit_map_union_source_bound : audit_map_union_source_bound_statement.
```

## CollectionsAuditPrepared

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditPrepared.v`.

Public module:
`Galois.Collections.CollectionsAuditPrepared`.

```rocq
(** * Counted prepared-key operations

    These observers retain the actual initial encoding and subsequent direct trie operations.
    For example, repeated lookups reuse the prepared code without re-encoding the key.
    Builds on: G4 prepared keys and the shared trie and map observers. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Collections Require Import CollectionsAuditState.
From Galois.Collections Require Import CollectionsAuditCost.
From Galois.Collections Require Import CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_prepared_event (K V CE : Type) : Type :=
  | AuditPreparedEncode (key : K) (code : positive) (events : list CE)
  | AuditPreparedRead (code : positive) (result : option V)
      (events : audit_trace (audit_trie_call (K * V)))
  | AuditPreparedWrite (code : positive) (events : audit_trace (audit_trie_call (K * V)))
  | AuditPreparedRemove (code : positive) (events : audit_trace (audit_trie_call (K * V))).

Arguments AuditPreparedEncode {K V CE} _ _ _.
Arguments AuditPreparedRead {K V CE} _ _ _.
Arguments AuditPreparedWrite {K V CE} _ _.
Arguments AuditPreparedRemove {K V CE} _ _.

(** Preparation records the actual encoder invocation and returned positive code. *)
Definition audit_prepare_key {K V CE} (enc : K -> positive * list CE) (key : K)
    : prepared_key K * list (audit_prepared_event K V CE) :=
  let '(code, events) := enc key in (PreparedKey key code, [AuditPreparedEncode key code events]).

Definition audit_prepared_lookup {K V CE} (key : prepared_key K) (m : Map.t K V)
    : option V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_map_code_get (key_code key) m in
  (result, [AuditPreparedRead (key_code key) result events]).

Definition audit_prepared_update {K V CE} (key : prepared_key K) (value : V) (m : Map.t K V)
    : Map.t K V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_trie_set (key_code key) (key_value key, value) m in
  (result, [AuditPreparedWrite (key_code key) events]).

Definition audit_prepared_remove {K V CE} (key : prepared_key K) (m : Map.t K V)
    : Map.t K V * list (audit_prepared_event K V CE) :=
  let '(result, events) := audit_trie_remove (key_code key) m in
  (result, [AuditPreparedRemove (key_code key) events]).

(** The direct operation erasure claims require no validity premise. *)
Definition audit_prepare_key_erases_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (original : encoding K) key,
    fst (enc key) = encode original key -> fst (@audit_prepare_key K V CE enc key) = prepare_key
      original key.

Definition audit_prepared_lookup_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) (m : Map.t K V),
    fst (@audit_prepared_lookup K V CE key m) = prepared_lookup key m.

Definition audit_prepared_update_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) value (m : Map.t K V),
    fst (@audit_prepared_update K V CE key value m) = prepared_update key value m.

Definition audit_prepared_remove_erases_statement : Prop :=
  forall K V CE (key : prepared_key K) (m : Map.t K V),
    fst (@audit_prepared_remove K V CE key m) = prepared_remove key m.

(** Fixed direct-operation work retains each exact child trace. *)
Fixpoint audit_prepared_source_work {K V CE} (enc_work : list CE -> nat)
    (events : list (audit_prepared_event K V CE)) : nat :=
  match events with
  | [] => 0
  | AuditPreparedEncode _ _ child :: rest => 1 + enc_work child + audit_prepared_source_work
    enc_work rest
  | AuditPreparedRead _ result child :: rest =>
      2 + (match result with None => 2 | Some _ => 4 end) + audit_trie_get_trace_source_work child +
      audit_prepared_source_work enc_work rest
  | AuditPreparedWrite _ child :: rest => 2 + audit_trie_update_trace_source_work child +
      audit_prepared_source_work enc_work rest
  | AuditPreparedRemove _ child :: rest => 2 + audit_trie_update_trace_source_work child +
      audit_prepared_source_work enc_work rest
  end.

Definition audit_prepared_lookup_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_lookup K V CE key m)) <=
      6 + 5 * Pos.size_nat (key_code key).

Definition audit_prepared_update_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) value (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_update K V CE key value m)) <=
      2 + 16 * Pos.size_nat (key_code key).

Definition audit_prepared_remove_source_bound_statement : Prop :=
  forall K V CE enc_work (key : prepared_key K) (m : Map.t K V),
    audit_prepared_source_work enc_work (snd (@audit_prepared_remove K V CE key m)) <=
      2 + 16 * Pos.size_nat (key_code key).

(** Prepared operations contain no encoder call; preparation itself has exactly one. *)
Fixpoint audit_prepared_encoder_calls {K V CE} (events : list (audit_prepared_event K V CE)) : nat
  :=
  match events with
  | [] => 0
  | AuditPreparedEncode _ _ _ :: rest => S (audit_prepared_encoder_calls rest)
  | _ :: rest => audit_prepared_encoder_calls rest
  end.

Definition audit_prepared_encoder_reuse_statement : Prop :=
  forall K V CE (enc : K -> positive * list CE) (key : prepared_key K) (m : Map.t K V) value,
    audit_prepared_encoder_calls (snd (@audit_prepare_key K V CE enc (key_value key))) = 1 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_lookup K V CE key m)) = 0 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_update K V CE key value m)) = 0 /\
    audit_prepared_encoder_calls (snd (@audit_prepared_remove K V CE key m)) = 0.
```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditPreparedAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditPrepared.

Theorem audit_prepare_key_erases : audit_prepare_key_erases_statement.
Theorem audit_prepared_lookup_erases : audit_prepared_lookup_erases_statement.
Theorem audit_prepared_update_erases : audit_prepared_update_erases_statement.
Theorem audit_prepared_remove_erases : audit_prepared_remove_erases_statement.
Theorem audit_prepared_lookup_source_bound : audit_prepared_lookup_source_bound_statement.
Theorem audit_prepared_update_source_bound : audit_prepared_update_source_bound_statement.
Theorem audit_prepared_remove_source_bound : audit_prepared_remove_source_bound_statement.
Theorem audit_prepared_encoder_reuse : audit_prepared_encoder_reuse_statement.
```

## CollectionsAuditPrimitive

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditPrimitive.v`.

Public module:
`Galois.Collections.CollectionsAuditPrimitive`.

```rocq
(** * Counted primitive trie frames

    These candidate clauses expose the source's accessor, node and map projection cases.
    For example, an empty root and a present leaf take distinct accessor branches.
    Builds on: CollectionsTrie, CollectionsMap and the audit trie model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditTrie.
Import List.ListNotations.

(** * Accessor cases *)

Definition audit_trie_left_source {A} (input : Trie.t A) : Trie.t A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N100 l) | Trie.Nodes (Trie.N101 l _) |
      Trie.Nodes (Trie.N110 l _) | Trie.Nodes (Trie.N111 l _ _) => Trie.Nodes l
    | _ => Trie.Empty
    end in
  (result, audit_trie_accessor_work input).

Definition audit_trie_right_source {A} (input : Trie.t A) : Trie.t A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N001 r) | Trie.Nodes (Trie.N011 _ r) |
      Trie.Nodes (Trie.N101 _ r) | Trie.Nodes (Trie.N111 _ _ r) => Trie.Nodes r
    | _ => Trie.Empty
    end in
  (result, audit_trie_accessor_work input).

Definition audit_trie_value_source {A} (input : Trie.t A) : option A * nat :=
  let result := match input with
    | Trie.Nodes (Trie.N010 v) | Trie.Nodes (Trie.N011 v _) |
      Trie.Nodes (Trie.N110 _ v) | Trie.Nodes (Trie.N111 _ v _) => Some v
    | _ => None
    end in
  (result, audit_trie_accessor_work input).

(** Each named claim equates both the original output and the fixed actual branch charge. *)
Definition audit_trie_left_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_left_source input =
    (Trie.left input, audit_trie_accessor_work input).

Definition audit_trie_right_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_right_source input =
    (Trie.right input, audit_trie_accessor_work input).

Definition audit_trie_value_source_adequate_statement : Prop :=
  forall A (input : Trie.t A), audit_trie_value_source input =
    (Trie.value input, audit_trie_accessor_work input).

(** * Smart-constructor cases *)

(** Every combination of absent and present inputs selects its original exact constructor. *)
Definition audit_trie_node_source {A} (left : Trie.t A) (value : option A) (right : Trie.t A)
    : Trie.t A * nat :=
  let result := match left, value, right with
    | Trie.Empty, None, Trie.Empty => Trie.Empty
    | Trie.Empty, None, Trie.Nodes r => Trie.Nodes (Trie.N001 r)
    | Trie.Empty, Some v, Trie.Empty => Trie.Nodes (Trie.N010 v)
    | Trie.Empty, Some v, Trie.Nodes r => Trie.Nodes (Trie.N011 v r)
    | Trie.Nodes l, None, Trie.Empty => Trie.Nodes (Trie.N100 l)
    | Trie.Nodes l, None, Trie.Nodes r => Trie.Nodes (Trie.N101 l r)
    | Trie.Nodes l, Some v, Trie.Empty => Trie.Nodes (Trie.N110 l v)
    | Trie.Nodes l, Some v, Trie.Nodes r => Trie.Nodes (Trie.N111 l v r)
    end in
  (result, audit_trie_node_work left value right).

Definition audit_trie_node_source_adequate_statement : Prop :=
  forall A (left : Trie.t A) value right,
    audit_trie_node_source left value right =
      (Trie.node left value right, audit_trie_node_work left value right).

(** * Position-map projection *)

Inductive audit_map_code_get_run {K V} : positive -> Map.t K V -> option V ->
    audit_trace (audit_trie_call (K * V)) -> nat -> Prop :=
  | AuditMapCodeGet : forall key input found events work,
      audit_trie_get_run key input found events work ->
      audit_map_code_get_run key input (option_map snd found) events
        (work + match found with None => 2 | Some _ => 4 end).

Definition audit_map_code_get_run_total_statement : Prop :=
  forall K V key (input : Map.t K V),
    exists output events work, audit_map_code_get_run key input output events work.

Definition audit_map_code_get_run_correct_statement : Prop :=
  forall K V key (input : Map.t K V) output events work,
    audit_map_code_get_run key input output events work ->
    output = Map.code_get key input /\ (output, events) = audit_map_code_get key input /\
    work <= 5 * Pos.size_nat key + 4.

(** The branch-level accounting must be independently related to the literal source evaluation. *)
Definition audit_trie_access_source_clauses_statement : Prop :=
  audit_trie_left_source_adequate_statement /\ audit_trie_right_source_adequate_statement /\
  audit_trie_value_source_adequate_statement /\ audit_trie_node_source_adequate_statement.

(** * Positive equality source cases *)

Inductive audit_positive_eqb_event : Type :=
  | AuditPositiveEqb (left right : positive) (result : bool).

(** The actual [Pos.eqb] descends only while both current constructors match. *)
Fixpoint audit_positive_eqb (left right : positive) {struct right}
    : bool * list audit_positive_eqb_event :=
  match left, right with
  | xI l, xI r =>
      let '(result, events) := audit_positive_eqb l r in
      (result, AuditPositiveEqb left right result :: events)
  | xO l, xO r =>
      let '(result, events) := audit_positive_eqb l r in
      (result, AuditPositiveEqb left right result :: events)
  | xH, xH => (true, [AuditPositiveEqb left right true])
  | _, _ => (false, [AuditPositiveEqb left right false])
  end.

Definition audit_positive_eqb_source_work (events : list audit_positive_eqb_event) : nat :=
  2 * length events.

(** These exact future contracts bind output and work to the original operands. *)
Definition audit_positive_eqb_erases_statement : Prop :=
  forall left right, fst (audit_positive_eqb left right) = Pos.eqb left right.

Definition audit_positive_eqb_source_bound_statement : Prop :=
  forall left right,
    audit_positive_eqb_source_work (snd (audit_positive_eqb left right)) <=
      2 * Nat.min (Pos.size_nat left) (Pos.size_nat right).
```

Card: AUD-CL-TRIE

Future proof module: `Galois.Collections.CollectionsAuditPrimitiveAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditPrimitive.

Theorem audit_trie_left_source_adequate : audit_trie_left_source_adequate_statement.
Theorem audit_trie_right_source_adequate : audit_trie_right_source_adequate_statement.
Theorem audit_trie_value_source_adequate : audit_trie_value_source_adequate_statement.
Theorem audit_trie_node_source_adequate : audit_trie_node_source_adequate_statement.
Theorem audit_map_code_get_run_total : audit_map_code_get_run_total_statement.
Theorem audit_map_code_get_run_correct : audit_map_code_get_run_correct_statement.
Theorem audit_trie_access_source_clauses : audit_trie_access_source_clauses_statement.
Theorem audit_positive_eqb_erases : audit_positive_eqb_erases_statement.
Theorem audit_positive_eqb_source_bound : audit_positive_eqb_source_bound_statement.
```

## CollectionsAuditState

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditState.v`.

Public module:
`Galois.Collections.CollectionsAuditState`.

```rocq
(** * G4 collections semantics

    This declaration-only pilot isolates G4 semantic contracts.
    For example, it keeps the historical observation in its original statement.
    Builds on: Galois.Collections. *)

From Stdlib Require Import List NArith PArith Permutation Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsDenseSet CollectionsUnionFind.
Import List.ListNotations.

Record prepared_key (K : Type) : Type := PreparedKey {
  key_value : K;
  key_code : positive
}.

Arguments PreparedKey {K}.
Arguments key_value {K}.
Arguments key_code {K}.

Definition key_valid {K} (E : encoding K) (p : prepared_key K) : Prop :=
  key_code p = encode E (key_value p).

Definition prepare_key {K} (E : encoding K) (k : K) : prepared_key K :=
  PreparedKey k (encode E k).

Definition prepare_key_valid_statement : Prop :=
  forall K (E : encoding K) k, key_valid E (prepare_key E k).

Definition prepared_lookup {K V} (p : prepared_key K) (m : Map.t K V) : option V :=
  Map.code_get (key_code p) m.

Definition prepared_update {K V} (p : prepared_key K) (v : V) (m : Map.t K V) : Map.t K V :=
  Trie.set (key_code p) (key_value p, v) m.

Definition prepared_remove {K V} (p : prepared_key K) (m : Map.t K V) : Map.t K V :=
  Trie.remove (key_code p) m.

Definition prepared_key_refinement_statement : Prop :=
  forall K V (E : encoding K) (p : prepared_key K) (m : Map.t K V),
    key_valid E p -> prepared_lookup p m = Map.get E (key_value p) m.

Definition prepared_key_injection_statement : Prop :=
  forall K (E : encoding K) (p q : prepared_key K),
    key_valid E p -> key_valid E q -> key_code p = key_code q -> key_value p = key_value q.

Definition prepared_key_update_statement : Prop :=
  forall K V (E : encoding K) (p : prepared_key K) (v : V) (m : Map.t K V),
    key_valid E p -> prepared_update p v m = Map.set E (key_value p) v m /\
    prepared_remove p m = Map.remove E (key_value p) m.

Definition prepared_pair_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (x y : A * B),
    key_code (prepare_key (pair_encoding EA EB) x) =
      key_code (prepare_key (pair_encoding EA EB) y) -> x = y.

Definition prepared_key_bits {K} (p : prepared_key K) : nat := Pos.size_nat (key_code p).

(** Declarations from the KeyCostProbe candidate. *)
Definition prepared_list_injection_statement : Prop :=
  forall A (EA : encoding A) (xs ys : list A),
    key_code (prepare_key (list_encoding EA) xs) = key_code (prepare_key (list_encoding EA) ys) ->
      xs = ys.

Definition prepared_pair_bits_statement : Prop :=
  forall A B (EA : encoding A) (EB : encoding B) (a : A) (b : B),
    Pos.size_nat (key_code (prepare_key (pair_encoding EA EB) (a,b))) =
      S (2 * Pos.size_nat (encode EA a) + 2 * Pos.size_nat (encode EB b)).

Definition prepared_list_bits_statement : Prop :=
  forall A (EA : encoding A) (xs : list A),
    Pos.size_nat (key_code (prepare_key (list_encoding EA) xs)) =
      S (2 * fold_right (fun a bits => Pos.size_nat (encode EA a) + bits) 0 xs).

(** Declarations from the DenseProbe candidate. *)
Definition slot_map (V : Type) := Map.t N V.

Definition slot_valid {K V} (E : encoding K) (u : dense_universe K) (m : slot_map V) : Prop :=
  dense_universe_wf E u /\ Map.wf N_encoding m /\
  forall i v, Map.get N_encoding i m = Some v -> (i < dense_length u)%N.

Definition prepare_slot {K} (E : encoding K) (u : dense_universe K) (k : K) : option N :=
  Map.get E k (dense_index u).

Definition slot_read {V} (m : slot_map V) (i : N) : option V := Map.get N_encoding i m.

Definition slot_lookup {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) : option V :=
  match Map.get E k (dense_index u) with
  | Some i => Map.get N_encoding i m
  | None => None
  end.

Definition slot_update {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) (v : V) : option (slot_map V) :=
  match Map.get E k (dense_index u) with
  | Some i => Some (Map.set N_encoding i v m)
  | None => None
  end.

Definition slot_elements {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) : list (K * V) :=
  flat_map (fun k => match slot_lookup E u m k with
    | Some v => [(k, v)]
    | None => []
    end) (dense_keys u).

Definition slot_to_map {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) : Map.t K V := Map.of_list E (slot_elements E u m).

Definition dense_map_refines {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (abstract : Map.t K V) : Prop :=
  slot_valid E u m /\ Map.wf E abstract /\
  forall k, slot_lookup E u m k = Map.get E k abstract.

Definition slot_of_map {K V} (E : encoding K) (u : dense_universe K)
    (abstract : Map.t K V) : slot_map V :=
  fold_left (fun result k =>
    match Map.get E k abstract, prepare_slot E u k with
    | Some value, Some i => Map.set N_encoding i value result
    | _, _ => result
    end) (dense_keys u) Map.empty.

Definition slot_update_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V) k v,
    slot_valid E u m -> slot_update E u m k v = Some m' ->
    slot_valid E u m' /\ slot_lookup E u m' k = Some v /\
    forall x, x <> k -> slot_lookup E u m' x = slot_lookup E u m x.

Definition slot_elements_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V),
    slot_valid E u m ->
    (forall k v, In (k, v) (slot_elements E u m) <-> slot_lookup E u m k = Some v) /\
    NoDup (map fst (slot_elements E u m)).

Definition slot_canonical_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (a b : slot_map V),
    slot_valid E u a -> slot_valid E u b ->
    (forall k, slot_lookup E u a k = slot_lookup E u b k) -> a = b.

Definition slot_to_map_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V),
    slot_valid E u m -> dense_map_refines E u m (slot_to_map E u m).

Definition slot_of_map_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (abstract : Map.t K V),
    dense_universe_wf E u -> slot_valid E u (slot_of_map E u abstract) /\
    forall k, slot_lookup E u (slot_of_map E u abstract) k =
      match prepare_slot E u k with
      | Some _ => Map.get E k abstract
      | None => None
      end.

Definition slot_prepare_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k i,
    slot_valid E u m -> prepare_slot E u k = Some i ->
    (i < dense_length u)%N /\ slot_read m i = slot_lookup E u m k.

Definition slot_outside_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k v,
    prepare_slot E u k = None -> slot_lookup E u m k = None /\ slot_update E u m k v = None.

Definition slot_empty_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K),
    dense_universe_wf E u -> slot_valid E u (@Map.empty N V).

Definition slot_present_update_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k v,
    slot_valid E u m -> In k (dense_keys u) ->
    exists m', slot_update E u m k v = Some m'.

Definition prepare_slots {K} (E : encoding K) (u : dense_universe K) (keys : list K) :
    list (option N) := map (prepare_slot E u) keys.

Definition read_slots {V} (m : slot_map V) (slots : list (option N)) : list (option V) :=
  map (fun slot => match slot with Some i => slot_read m i | None => None end) slots.

Definition slot_batch_refinement_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) keys,
    read_slots m (prepare_slots E u keys) = map (slot_lookup E u m) keys.

(** Declarations from the DenseUpdateProbe candidate. *)
Definition slot_remove {K V} (E : encoding K) (u : dense_universe K)
    (m : slot_map V) (k : K) : option (slot_map V) :=
  match prepare_slot E u k with
  | Some i => Some (Map.remove N_encoding i m)
  | None => None
  end.

Definition slot_update_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V)
    (abstract : Map.t K V) k value,
    dense_map_refines E u m abstract -> slot_update E u m k value = Some m' ->
    dense_map_refines E u m' (Map.set E k value abstract).

Definition slot_remove_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V)
    (abstract : Map.t K V) k,
    dense_map_refines E u m abstract -> slot_remove E u m k = Some m' ->
    dense_map_refines E u m' (Map.remove E k abstract).

Definition slot_remove_frame_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m m' : slot_map V) k,
    slot_valid E u m -> slot_remove E u m k = Some m' ->
    slot_valid E u m' /\ slot_lookup E u m' k = None /\
    forall other, other <> k -> slot_lookup E u m' other = slot_lookup E u m other.

Definition slot_remove_outside_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) k,
    prepare_slot E u k = None -> slot_remove E u m k = None.

Definition slot_elements_refines_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (m : slot_map V) (abstract : Map.t K V),
    dense_map_refines E u m abstract ->
    (forall k value, In (k,value) (slot_elements E u m) <-> Map.get E k abstract = Some value) /\
    NoDup (map fst (slot_elements E u m)).

(** Declarations from the DenseTokenProbe candidate. *)
Record dense_slot_token {K} (E : encoding K) (u : dense_universe K) : Type := DenseSlotToken {
  dense_token_key : K;
  dense_token_index : N
}.
Arguments DenseSlotToken {K E u}.
Arguments dense_token_key {K E u}.
Arguments dense_token_index {K E u}.

Definition dense_token_valid {K} (E : encoding K) (u : dense_universe K)
    (token : dense_slot_token E u) : Prop :=
  prepare_slot E u (dense_token_key token) = Some (dense_token_index token).

Definition dense_token_prepare {K} (E : encoding K) (u : dense_universe K) (key : K) :
    option (dense_slot_token E u) :=
  match prepare_slot E u key with
  | Some index => Some (DenseSlotToken key index)
  | None => None
  end.

Definition dense_token_read {K V} (E : encoding K) (u : dense_universe K)
    (token : dense_slot_token E u) (m : slot_map V) : option V := slot_read m (dense_token_index
      token).

Definition dense_token_prepare_statement : Prop :=
  forall K (E : encoding K) (u : dense_universe K) key token,
    dense_token_prepare E u key = Some token ->
    dense_token_valid E u token /\ dense_token_key token = key.

Definition dense_token_read_statement : Prop :=
  forall K V (E : encoding K) (u : dense_universe K) (token : dense_slot_token E u) (m : slot_map
    V),
    dense_token_valid E u token -> dense_token_read E u token m = slot_lookup E u m
      (dense_token_key token).

Definition dense_token_scope_statement : Prop :=
  forall K (E : encoding K) (u : dense_universe K) key,
    dense_token_prepare E u key = None <-> prepare_slot E u key = None.


```

Card: AUD-CL-DENSE

Future proof module: `Galois.Collections.CollectionsAuditStateDENSEAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditState.

Theorem prepared_key_refinement : prepared_key_refinement_statement.
Theorem prepared_key_update : prepared_key_update_statement.
Theorem slot_update : slot_update_statement.
Theorem slot_elements : slot_elements_statement.
Theorem slot_canonical : slot_canonical_statement.
Theorem slot_to_map : slot_to_map_statement.
Theorem slot_of_map : slot_of_map_statement.
Theorem slot_prepare : slot_prepare_statement.
Theorem slot_outside : slot_outside_statement.
Theorem slot_empty : slot_empty_statement.
Theorem slot_present_update : slot_present_update_statement.
Theorem slot_batch_refinement : slot_batch_refinement_statement.
Theorem slot_update_refines : slot_update_refines_statement.
Theorem slot_remove_refines : slot_remove_refines_statement.
Theorem slot_remove_frame : slot_remove_frame_statement.
Theorem slot_remove_outside : slot_remove_outside_statement.
Theorem slot_elements_refines : slot_elements_refines_statement.
Theorem dense_token_prepare : dense_token_prepare_statement.
Theorem dense_token_read : dense_token_read_statement.
Theorem dense_token_scope : dense_token_scope_statement.
```

Card: AUD-CL-ENC

Future proof module: `Galois.Collections.CollectionsAuditStateENCAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditState.

Theorem prepare_key_valid : prepare_key_valid_statement.
Theorem prepared_key_injection : prepared_key_injection_statement.
Theorem prepared_pair : prepared_pair_statement.
Theorem prepared_list_injection : prepared_list_injection_statement.
Theorem prepared_pair_bits : prepared_pair_bits_statement.
Theorem prepared_list_bits : prepared_list_bits_statement.
```

## CollectionsAuditTraversalBudget

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditTraversalBudget.v`.

Public module:
`Galois.Collections.CollectionsAuditTraversalBudget`.

```rocq
(** * Independent collection callback budgets and actual source calls

    These bounds charge map, union and fold callbacks at their actual values and accumulators.
    For example, a fold callback changes the accumulator used by the rhs subtree's budget.
    Builds on: source-shaped traversal models and genuine foreign callback adapters. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap.
From Galois.Collections Require Import CollectionsAuditCallback.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Collections Require Import CollectionsAuditMapTraverse.
From Galois.Collections Require Import CollectionsAuditMapFold.
Import List.ListNotations.

Definition audit_map_transform_calls_source {K V W E}
    (work : list E -> nat) (source : V -> W -> list E -> nat -> Prop)
    (events : list (audit_map_transform_event K V W E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapTransformCall _ input output body => source input output body (work body)
    | _ => True
    end) events.

Definition audit_map_union_calls_source {K V E} (work : list E -> nat)
    (source : V * V -> V -> list E -> nat -> Prop)
    (events : list (audit_map_union_event K V E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapUnionCall _ _ lhs rhs output body => source (lhs, rhs) output body (work body)
    | _ => True
    end) events.

Definition audit_map_fold_calls_source {K V B E} (work : list E -> nat)
    (source : B * (K * V) -> B -> list E -> nat -> Prop)
    (events : list (audit_map_fold_event K V B E)) : Prop :=
  Forall (fun event => match event with
    | AuditMapFoldCall _ key value before after body =>
        source (before, (key, value)) after body (work body)
    | _ => True
    end) events.

Definition audit_map_transform_input_budget {K V} (budget : V -> nat) (input : Map.t K V) : nat :=
  18 * audit_trie_nodes input +
    fold_right (fun binding total => budget (snd binding) + total) 0 (Map.elements input).

Definition audit_map_union_input_budget {K V} (budget : V * V -> nat)
    (lhs rhs : Map.t K V) : nat :=
  1 + 18 * audit_trie_nodes lhs +
    fold_right (fun first total =>
      fold_right (fun second subtotal => budget (snd first, snd second) + subtotal) 0
        (Map.elements rhs) + total) 0 (Map.elements lhs).

(** The independent fold recurrence has no event trace or returned event-work projection. *)
Fixpoint audit_map_fold_input_budget_ne {K V B E} (call : B -> K -> V -> B * list E)
    (budget : B * (K * V) -> nat) (path : positive -> positive)
    (node : Trie.ne (K * V)) (acc : B) : B * nat :=
  let cost := fun before key value => 3 + Pos.size_nat (path xH) + budget (before, (key, value)) in
  match node with
  | Trie.N001 rhs =>
      let '(out, rest) := audit_map_fold_input_budget_ne call budget (fun p => path (xI p)) rhs
        acc in
      (out, 10 + rest)
  | Trie.N010 (key, value) => (fst (call acc key value), 10 + cost acc key value)
  | Trie.N011 (key, value) rhs =>
      let middle := fst (call acc key value) in
      let '(out, rest) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs middle in
      (out, 10 + cost acc key value + rest)
  | Trie.N100 lhs =>
      let '(out, rest) := audit_map_fold_input_budget_ne call budget (fun p => path (xO p)) lhs
        acc in
      (out, 10 + rest)
  | Trie.N101 lhs rhs =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      let '(out, second) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs middle in
      (out, 10 + first + second)
  | Trie.N110 lhs (key, value) =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      (fst (call middle key value), 10 + first + cost middle key value)
  | Trie.N111 lhs (key, value) rhs =>
      let '(middle, first) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xO p)) lhs acc in
      let next := fst (call middle key value) in
      let '(out, second) := audit_map_fold_input_budget_ne call budget
        (fun p => path (xI p)) rhs next in
      (out, 10 + first + cost middle key value + second)
  end.

Definition audit_map_fold_input_budget {K V B E} (call : B -> K -> V -> B * list E)
    (budget : B * (K * V) -> nat) (input : Map.t K V) (acc : B) : nat :=
  match input with
  | Trie.Empty => 0
  | Trie.Nodes node => snd (audit_map_fold_input_budget_ne call budget (fun p => p) node acc)
  end.

(** The mapper's source law covers each actual retained value, result and body. *)
Definition audit_map_transform_adapted_input_bound_statement : Prop :=
  forall K V W E (call : V -> W * list E) work source budget (input : Map.t K V),
    audit_external_callback_adapter call work source budget ->
    let events := snd (audit_map_transform call input) in
    audit_map_transform_calls_source work source events /\
    audit_map_transform_source_work work events <= audit_map_transform_input_budget budget input.

(** Union pays every overlap call from the original input values, including distinct stored keys. *)
Definition audit_map_union_adapted_input_bound_statement : Prop :=
  forall K V E (call : V -> V -> V * list E) work source budget (lhs rhs : Map.t K V),
    audit_external_callback_adapter (fun pair => call (fst pair) (snd pair)) work source budget ->
    let events := snd (audit_map_union call lhs rhs) in
    audit_map_union_calls_source work source events /\
    audit_map_union_source_work work events <= audit_map_union_input_budget budget lhs rhs.

(** Fold source and cost use the exact accumulator immediately before every actual callback. *)
Definition audit_map_fold_adapted_input_bound_statement : Prop :=
  forall K V B E (call : B -> K -> V -> B * list E) work source budget
      (input : Map.t K V) (acc : B),
    audit_external_callback_adapter
      (fun args => call (fst args) (fst (snd args)) (snd (snd args))) work source budget ->
    let events := snd (audit_map_fold call input acc) in
    audit_map_fold_calls_source work source events /\
    audit_map_fold_source_work work events <= audit_map_fold_input_budget call budget input acc.
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditTraversalBudgetAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditTraversalBudget.

Theorem audit_map_transform_adapted_input_bound : audit_map_transform_adapted_input_bound_statement.
Theorem audit_map_union_adapted_input_bound : audit_map_union_adapted_input_bound_statement.
Theorem audit_map_fold_adapted_input_bound : audit_map_fold_adapted_input_bound_statement.
```

## CollectionsAuditTrie

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditTrie.v`.

Public module:
`Galois.Collections.CollectionsAuditTrie`.

```rocq
(** * Counted canonical trie calls

    These candidate operations retain the real path, operands and results of trie primitives.
    For example, an absent lookup still visits every bit of its positive key.
    Builds on: CollectionsTrie, CollectionsMap and the audit event vocabulary. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

(** * Typed primitive events *)

Inductive audit_trie_call (A : Type) : Type :=
  | AuditTrieKey (key : positive) (input : Trie.t A)
  | AuditTrieLeft (input output : Trie.t A)
  | AuditTrieRight (input output : Trie.t A)
  | AuditTrieValue (input : Trie.t A) (output : option A)
  | AuditTrieNode (left : Trie.t A) (value : option A) (right output : Trie.t A).

Arguments AuditTrieKey {A} _ _.
Arguments AuditTrieLeft {A} _ _.
Arguments AuditTrieRight {A} _ _.
Arguments AuditTrieValue {A} _ _.
Arguments AuditTrieNode {A} _ _ _ _.

(** A lookup follows the original key and emits each selected accessor with its result. *)
Polymorphic Fixpoint audit_trie_get {A} (key : positive) (input : Trie.t A)
    : option A * audit_trace (audit_trie_call A) :=
  match key with
  | xH =>
      let value := Trie.value input in
      (value, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieValue input value)])
  | xO rest =>
      let left := Trie.left input in
      let '(result, events) := audit_trie_get rest left in
      (result, AuditCall (AuditTrieKey key input) :: AuditCall (AuditTrieLeft input left) :: events)
  | xI rest =>
      let right := Trie.right input in
      let '(result, events) := audit_trie_get rest right in
      (result, AuditCall (AuditTrieKey key input) :: AuditCall (AuditTrieRight input right) ::
        events)
  end.

(** Setting and removal share the source control flow; [value] fixes the actual leaf update. *)
Polymorphic Fixpoint audit_trie_update {A} (key : positive) (value : option A) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) :=
  match key with
  | xH =>
      let left := Trie.left input in
      let right := Trie.right input in
      let output := Trie.node left value right in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left);
                AuditCall (AuditTrieRight input right);
                AuditCall (AuditTrieNode left value right output)])
  | xO rest =>
      let left := Trie.left input in
      let '(updated, events) := audit_trie_update rest value left in
      let old := Trie.value input in
      let right := Trie.right input in
      let output := Trie.node updated old right in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left)] ++
        events ++ [AuditCall (AuditTrieValue input old); AuditCall (AuditTrieRight input right);
                   AuditCall (AuditTrieNode updated old right output)])
  | xI rest =>
      let left := Trie.left input in
      let old := Trie.value input in
      let right := Trie.right input in
      let '(updated, events) := audit_trie_update rest value right in
      let output := Trie.node left old updated in
      (output, [AuditCall (AuditTrieKey key input); AuditCall (AuditTrieLeft input left);
                AuditCall (AuditTrieValue input old); AuditCall (AuditTrieRight input right)] ++
        events ++ [AuditCall (AuditTrieNode left old updated output)])
  end.

(** These wrappers retain the actual updated value or removal. *)
Polymorphic Definition audit_trie_set {A} (key : positive) (value : A) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) := audit_trie_update key (Some value) input.

Definition audit_trie_remove {A} (key : positive) (input : Trie.t A)
    : Trie.t A * audit_trace (audit_trie_call A) := audit_trie_update key None input.

(** Map code lookup preserves the exact stored-pair lookup, including its discarded key. *)
Polymorphic Definition audit_map_code_get {K V} (key : positive) (input : Map.t K V)
    : option V * audit_trace (audit_trie_call (K * V)) :=
  let '(result, events) := audit_trie_get key input in
  (option_map snd result, events).

(** * Future implementation obligations *)

(** Erasure preserves each original public operation for all keys and tries. *)
Definition audit_trie_get_erases_statement : Prop :=
  forall A key (input : Trie.t A), fst (audit_trie_get key input) = Trie.get key input.

Definition audit_trie_set_erases_statement : Prop :=
  forall A key (value : A) input, fst (audit_trie_set key value input) = Trie.set key value input.

Definition audit_trie_remove_erases_statement : Prop :=
  forall A key (input : Trie.t A), fst (audit_trie_remove key input) = Trie.remove key input.

Definition audit_map_code_get_erases_statement : Prop :=
  forall K V key (input : Map.t K V), fst (audit_map_code_get key input) = Map.code_get key input.

(** The number of selected typed events is bounded by the input key length. *)
Definition audit_trie_get_events_bound_statement : Prop :=
  forall A key (input : Trie.t A),
    audit_work (snd (audit_trie_get key input)) = 2 * Pos.size_nat key.

Definition audit_trie_update_events_bound_statement : Prop :=
  forall A key (value : option A) input,
    audit_work (snd (audit_trie_update key value input)) <= 5 * Pos.size_nat key.

(** * Fixed source-frame accounting *)

(** Each selected accessor inspects its outer constructor and, for nodes, its inner constructor. *)
Definition audit_trie_accessor_work {A} (input : Trie.t A) : nat :=
  match input with
  | Trie.Empty => 1
  | Trie.Nodes _ => 2
  end.

(** Node inspection charges three inputs and the selected output constructor frames. *)
Definition audit_trie_node_work {A} (left : Trie.t A) (value : option A) (right : Trie.t A)
    : nat :=
  match left, value, right with
  | Trie.Empty, None, Trie.Empty => 4
  | _, _, _ => 5
  end.

(** Lookup charges the fixpoint/match and each selected accessor and recursive application. *)
Fixpoint audit_trie_get_source_work {A} (key : positive) (input : Trie.t A) : nat :=
  match key with
  | xH => 2 + audit_trie_accessor_work input
  | xO rest => 3 + audit_trie_accessor_work input +
      audit_trie_get_source_work rest (Trie.left input)
  | xI rest => 3 + audit_trie_accessor_work input +
      audit_trie_get_source_work rest (Trie.right input)
  end.

(** Update charges all three strict node operands, selected accessors, recursion and rebuilding. *)
Fixpoint audit_trie_update_source_work {A} (key : positive) (value : option A)
    (input : Trie.t A) : nat :=
  match key with
  | xH => 5 + 2 * audit_trie_accessor_work input +
      audit_trie_node_work (Trie.left input) value (Trie.right input)
  | xO rest => 5 + 3 * audit_trie_accessor_work input +
      audit_trie_update_source_work rest value (Trie.left input) +
      audit_trie_node_work (fst (audit_trie_update rest value (Trie.left input)))
        (Trie.value input) (Trie.right input)
  | xI rest => 5 + 3 * audit_trie_accessor_work input +
      audit_trie_update_source_work rest value (Trie.right input) +
      audit_trie_node_work (Trie.left input) (Trie.value input)
        (fst (audit_trie_update rest value (Trie.right input)))
  end.

(** Bounds use only the original positive key, not the counted result or trace. *)
Definition audit_trie_get_source_work_bound_statement : Prop :=
  forall A key (input : Trie.t A), audit_trie_get_source_work key input <= 5 * Pos.size_nat key.

Definition audit_trie_update_source_work_bound_statement : Prop :=
  forall A key (value : option A) input,
    audit_trie_update_source_work key value input <= 16 * Pos.size_nat key.

(** * Source-indexed derivations *)

(** The derivation fixes the selected source branch, returned result, trace and local charge. *)
Inductive audit_trie_get_run {A} : positive -> Trie.t A -> option A ->
    audit_trace (audit_trie_call A) -> nat -> Prop :=
  | AuditGetHere : forall input,
      audit_trie_get_run xH input (Trie.value input)
        [AuditCall (AuditTrieKey xH input); AuditCall (AuditTrieValue input (Trie.value input))]
        (2 + audit_trie_accessor_work input)
  | AuditGetLeft : forall rest input result events work,
      audit_trie_get_run rest (Trie.left input) result events work ->
      audit_trie_get_run (xO rest) input result
        (AuditCall (AuditTrieKey (xO rest) input) ::
         AuditCall (AuditTrieLeft input (Trie.left input)) :: events)
        (3 + audit_trie_accessor_work input + work)
  | AuditGetRight : forall rest input result events work,
      audit_trie_get_run rest (Trie.right input) result events work ->
      audit_trie_get_run (xI rest) input result
        (AuditCall (AuditTrieKey (xI rest) input) ::
         AuditCall (AuditTrieRight input (Trie.right input)) :: events)
        (3 + audit_trie_accessor_work input + work).

(** This future theorem binds correspondence and the bound to the same actual derivation. *)
Definition audit_trie_get_run_correct_statement : Prop :=
  forall A key (input : Trie.t A) result events work,
    audit_trie_get_run key input result events work ->
    result = Trie.get key input /\
    (result, events) = audit_trie_get key input /\
    work = audit_trie_get_source_work key input /\
    work <= 5 * Pos.size_nat key.

Definition audit_trie_get_run_total_statement : Prop :=
  forall A key (input : Trie.t A),
    exists result events work, audit_trie_get_run key input result events work.

(** The update derivation retains the exact child result used to construct the parent node. *)
Inductive audit_trie_update_run {A} : positive -> option A -> Trie.t A -> Trie.t A ->
    audit_trace (audit_trie_call A) -> nat -> Prop :=
  | AuditUpdateHere : forall value input,
      audit_trie_update_run xH value input (Trie.node (Trie.left input) value (Trie.right input))
        [AuditCall (AuditTrieKey xH input); AuditCall (AuditTrieLeft input (Trie.left input));
         AuditCall (AuditTrieRight input (Trie.right input));
         AuditCall (AuditTrieNode (Trie.left input) value (Trie.right input)
           (Trie.node (Trie.left input) value (Trie.right input)))]
        (5 + 2 * audit_trie_accessor_work input +
          audit_trie_node_work (Trie.left input) value (Trie.right input))
  | AuditUpdateLeft : forall rest value input child child_events child_work,
      audit_trie_update_run rest value (Trie.left input) child child_events child_work ->
      audit_trie_update_run (xO rest) value input
        (Trie.node child (Trie.value input) (Trie.right input))
        ([AuditCall (AuditTrieKey (xO rest) input);
          AuditCall (AuditTrieLeft input (Trie.left input))] ++ child_events ++
         [AuditCall (AuditTrieValue input (Trie.value input));
          AuditCall (AuditTrieRight input (Trie.right input));
          AuditCall (AuditTrieNode child (Trie.value input) (Trie.right input)
            (Trie.node child (Trie.value input) (Trie.right input)))])
        (5 + 3 * audit_trie_accessor_work input + child_work +
          audit_trie_node_work child (Trie.value input) (Trie.right input))
  | AuditUpdateRight : forall rest value input child child_events child_work,
      audit_trie_update_run rest value (Trie.right input) child child_events child_work ->
      audit_trie_update_run (xI rest) value input
        (Trie.node (Trie.left input) (Trie.value input) child)
        ([AuditCall (AuditTrieKey (xI rest) input);
          AuditCall (AuditTrieLeft input (Trie.left input));
          AuditCall (AuditTrieValue input (Trie.value input));
          AuditCall (AuditTrieRight input (Trie.right input))] ++ child_events ++
         [AuditCall (AuditTrieNode (Trie.left input) (Trie.value input) child
            (Trie.node (Trie.left input) (Trie.value input) child))])
        (5 + 3 * audit_trie_accessor_work input + child_work +
          audit_trie_node_work (Trie.left input) (Trie.value input) child).

Definition audit_trie_update_run_correct_statement : Prop :=
  forall A key (value : option A) input result events work,
    audit_trie_update_run key value input result events work ->
    (result, events) = audit_trie_update key value input /\
    work = audit_trie_update_source_work key value input /\
    work <= 16 * Pos.size_nat key.

Definition audit_trie_update_run_total_statement : Prop :=
  forall A key (value : option A) input,
    exists result events work, audit_trie_update_run key value input result events work.

(** * Same-trace source-frame folds *)

(** The lookup and update sites differ, so each fold uses its fixed source-specific charges. *)
Polymorphic Fixpoint audit_trie_get_trace_source_work {A}
    (events : audit_trace (audit_trie_call A)) : nat :=
  match events with
  | [] => 0
  | AuditCall (AuditTrieKey key _) :: rest =>
      (match key with xH => 2 | _ => 3 end) + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieLeft input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieRight input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | AuditCall (AuditTrieValue input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_get_trace_source_work rest
  | _ :: rest => audit_trie_get_trace_source_work rest
  end.

Polymorphic Fixpoint audit_trie_update_trace_source_work {A}
    (events : audit_trace (audit_trie_call A)) : nat :=
  match events with
  | [] => 0
  | AuditCall (AuditTrieKey _ _) :: rest => 5 + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieLeft input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieRight input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieValue input _) :: rest =>
      audit_trie_accessor_work input + audit_trie_update_trace_source_work rest
  | AuditCall (AuditTrieNode l value r _) :: rest =>
      audit_trie_node_work l value r + audit_trie_update_trace_source_work rest
  | _ :: rest => audit_trie_update_trace_source_work rest
  end.

(** These obligations bind the charged events to the exact producer's trace and source input. *)
Definition audit_trie_get_trace_adequate_statement : Prop :=
  forall A key (input : Trie.t A),
    audit_trie_get_trace_source_work (snd (audit_trie_get key input)) =
      audit_trie_get_source_work key input.

Definition audit_trie_update_trace_adequate_statement : Prop :=
  forall A key (value : option A) input,
    audit_trie_update_trace_source_work (snd (audit_trie_update key value input)) =
      audit_trie_update_source_work key value input.
```

Card: AUD-CL-TRIE

Future proof module: `Galois.Collections.CollectionsAuditTrieAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditTrie.

Theorem audit_trie_get_erases : audit_trie_get_erases_statement.
Theorem audit_trie_set_erases : audit_trie_set_erases_statement.
Theorem audit_trie_remove_erases : audit_trie_remove_erases_statement.
Theorem audit_map_code_get_erases : audit_map_code_get_erases_statement.
Theorem audit_trie_get_events_bound : audit_trie_get_events_bound_statement.
Theorem audit_trie_update_events_bound : audit_trie_update_events_bound_statement.
Theorem audit_trie_get_source_work_bound : audit_trie_get_source_work_bound_statement.
Theorem audit_trie_update_source_work_bound : audit_trie_update_source_work_bound_statement.
Theorem audit_trie_get_run_correct : audit_trie_get_run_correct_statement.
Theorem audit_trie_get_run_total : audit_trie_get_run_total_statement.
Theorem audit_trie_update_run_correct : audit_trie_update_run_correct_statement.
Theorem audit_trie_update_run_total : audit_trie_update_run_total_statement.
Theorem audit_trie_get_trace_adequate : audit_trie_get_trace_adequate_statement.
Theorem audit_trie_update_trace_adequate : audit_trie_update_trace_adequate_statement.
```

## CollectionsAuditUnion

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditUnion.v`.

Public module:
`Galois.Collections.CollectionsAuditUnion`.

```rocq
(** * Counted persistent set union

    This candidate mirrors shared one-sided subtrees and the actual merge recursion.
    For example, union with an empty right side retains the left subtree without visiting it.
    Builds on: CollectionsTrie, CollectionsMap and CollectionsFinSet. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsFinSet.
From Galois.Collections Require Import CollectionsAuditElements.
From Galois.Collections Require Import CollectionsAuditTrie.
Import List.ListNotations.

Inductive audit_union_event (K : Type) : Type :=
  | AuditUnionEnter (left : Trie.ne (K * unit)) (right : FinSet.t K)
  | AuditUnionNode (left : FinSet.t K) (value : option (K * unit))
      (right output : FinSet.t K)
  | AuditUnionRoot (left right : FinSet.t K).

Arguments AuditUnionEnter {K} _ _.
Arguments AuditUnionNode {K} _ _ _ _.
Arguments AuditUnionRoot {K} _ _.

(** This is the exact Map.union_with callback used by FinSet.union. *)
Definition audit_set_union_value {K} (a b : option (K * unit)) : option (K * unit) :=
  Trie.union_opt (fun x y => (fst x, (fun v _ => v) (snd x) (snd y))) a b.

(** The recursive call skips a whole subtree when its counterpart is empty. *)
Fixpoint audit_set_union_ne {K} (node : Trie.ne (K * unit)) (other : FinSet.t K)
    : FinSet.t K * list (audit_union_event K) :=
  let enter := [AuditUnionEnter node other] in
  match other with
  | Trie.Empty => (Trie.Nodes node, enter)
  | Trie.Nodes _ =>
      match node with
      | Trie.N001 r =>
          let l := Trie.left other in
          let v := audit_set_union_value None (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, enter ++ re ++ [AuditUnionNode l v rr out])
      | Trie.N010 x =>
          let l := Trie.left other in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node l v r in
          (out, enter ++ [AuditUnionNode l v r out])
      | Trie.N011 x r =>
          let l := Trie.left other in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node l v rr in
          (out, enter ++ re ++ [AuditUnionNode l v rr out])
      | Trie.N100 l =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value None (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, enter ++ le ++ [AuditUnionNode ll v r out])
      | Trie.N101 l r =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value None (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, enter ++ le ++ re ++ [AuditUnionNode ll v rr out])
      | Trie.N110 l x =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let r := Trie.right other in
          let out := Trie.node ll v r in
          (out, enter ++ le ++ [AuditUnionNode ll v r out])
      | Trie.N111 l x r =>
          let '(ll, le) := audit_set_union_ne l (Trie.left other) in
          let v := audit_set_union_value (Some x) (Trie.value other) in
          let '(rr, re) := audit_set_union_ne r (Trie.right other) in
          let out := Trie.node ll v rr in
          (out, enter ++ le ++ re ++ [AuditUnionNode ll v rr out])
      end
  end.

(** No encoding is called by the original set-union body. *)
Definition audit_finset_union {K} (left right : FinSet.t K)
    : FinSet.t K * list (audit_union_event K) :=
  match left with
  | Trie.Empty => (right, [AuditUnionRoot left right])
  | Trie.Nodes node =>
      let '(out, events) := audit_set_union_ne node right in
      (out, AuditUnionRoot left right :: events)
  end.

(** The result equality is a future AUD-CL theorem, not established by elaboration. *)
Definition audit_finset_union_erases_statement : Prop :=
  forall K (enc : encoding K) left right,
    fst (audit_finset_union left right) = FinSet.union enc left right.

(** The selected merge-frame count is bounded by the first input's actual node count. *)
Definition audit_finset_union_count_statement : Prop :=
  forall K (left right : FinSet.t K),
    length (snd (audit_finset_union left right)) <=
      1 + 2 * match left with
              | Trie.Empty => 0
              | Trie.Nodes node => audit_elements_nodes node
              end.

(** Fixed source-frame charges include visited merge branches and actual rebuilt nodes. *)
Fixpoint audit_finset_union_source_work {K} (events : list (audit_union_event K)) : nat :=
  match events with
  | [] => 0
  | AuditUnionRoot _ _ :: rest => 1 + audit_finset_union_source_work rest
  | AuditUnionEnter _ _ :: rest => 10 + audit_finset_union_source_work rest
  | AuditUnionNode l value r _ :: rest =>
      audit_trie_node_work l value r + audit_finset_union_source_work rest
  end.

Definition audit_finset_union_source_bound_statement : Prop :=
  forall K (left right : FinSet.t K),
    audit_finset_union_source_work (snd (audit_finset_union left right)) <=
      1 + 15 * audit_trie_nodes left.
```

Card: AUD-CL-TRAVERSE

Future proof module: `Galois.Collections.CollectionsAuditUnionAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditUnion.

Theorem audit_finset_union_erases : audit_finset_union_erases_statement.
Theorem audit_finset_union_count : audit_finset_union_count_statement.
Theorem audit_finset_union_source_bound : audit_finset_union_source_bound_statement.
```

## CollectionsAuditUnionFind

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditUnionFind.v`.

Public module:
`Galois.Collections.CollectionsAuditUnionFind`.

```rocq
(** * Counted persistent union-find

    This observer follows actual parent compression, rank accesses and persistent updates.
    For example, two sibling histories start from the same forest and are charged separately.
    Builds on: CollectionsUnionFind and shared map, encoding and positive-equality models. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsUnionFind.
From Galois.Collections Require Import CollectionsAuditPrimitive CollectionsAuditMap
  CollectionsAuditMapTraverse CollectionsAuditUnion CollectionsAuditElements.
Import List.ListNotations.

(** * Actual forest operation events *)

Inductive audit_uf_event (K CE : Type) : Type :=
  | AuditUFFindCase (fuel : nat) (key : K) (forest : UnionFind.t K)
  | AuditUFParentRead (key : K) (result : option K) (calls : list (audit_map_event K K CE))
  | AuditUFParentWrite (key root : K) (calls : list (audit_map_event K K CE))
  | AuditUFRankRead (key : K) (result : option nat) (calls : list (audit_map_event K nat CE))
  | AuditUFRankWrite (key : K) (rank : nat) (calls : list (audit_map_event K nat CE))
  | AuditUFEncode (key : K) (code : positive) (events : list CE)
  | AuditUFEqual (left right : positive) (result : bool) (events : list audit_positive_eqb_event)
  | AuditUFRankCompare (left right : nat) (result : comparison)
  | AuditUFRankMax (left right result : nat)
  | AuditUFKeysParents (calls : list (audit_map_transform_event K K unit unit))
  | AuditUFKeysRanks (calls : list (audit_map_transform_event K nat unit unit))
  | AuditUFKeysUnion (calls : list (audit_union_event K))
  | AuditUFKeysElements (calls : list (audit_set_elements_event K))
  | AuditUFHistoryCase (remaining : nat).

Arguments AuditUFFindCase {K CE} _ _ _.
Arguments AuditUFParentRead {K CE} _ _ _.
Arguments AuditUFParentWrite {K CE} _ _ _.
Arguments AuditUFRankRead {K CE} _ _ _.
Arguments AuditUFRankWrite {K CE} _ _ _.
Arguments AuditUFEncode {K CE} _ _ _.
Arguments AuditUFEqual {K CE} _ _ _ _.
Arguments AuditUFRankCompare {K CE} _ _ _.
Arguments AuditUFRankMax {K CE} _ _ _.
Arguments AuditUFKeysParents {K CE} _.
Arguments AuditUFKeysRanks {K CE} _.
Arguments AuditUFKeysUnion {K CE} _.
Arguments AuditUFKeysElements {K CE} _.
Arguments AuditUFHistoryCase {K CE} _.

(** The recursive parent lookup uses the original forest; writes use the returned compressed one. *)
Fixpoint audit_uf_find_fuel {K CE} (enc : K -> positive * list CE) (fuel : nat)
    (key : K) (forest : UnionFind.t K) : (K * UnionFind.t K) * list (audit_uf_event K CE) :=
  match fuel with
  | 0 => ((key, forest), [AuditUFFindCase fuel key forest])
  | S rest =>
      let '(parent, reads) := audit_map_get enc key (UnionFind.parents forest) in
      match parent with
      | None => ((key, forest), [AuditUFFindCase fuel key forest; AuditUFParentRead key parent
        reads])
      | Some next =>
          let '((root, compressed), child) := audit_uf_find_fuel enc rest next forest in
          let '(parents, writes) := audit_map_set enc key root (UnionFind.parents compressed) in
          let output := UnionFind.Forest parents (UnionFind.ranks compressed)
            (UnionFind.max_rank compressed) in
          ((root, output), [AuditUFFindCase fuel key forest; AuditUFParentRead key parent reads] ++
            child ++ [AuditUFParentWrite key root writes])
      end
  end.

Definition audit_uf_find {K CE} (enc : K -> positive * list CE) (key : K) (forest : UnionFind.t K)
    : (K * UnionFind.t K) * list (audit_uf_event K CE) :=
  audit_uf_find_fuel enc (S (UnionFind.max_rank forest)) key forest.

(** Rank lookup retains the actual optional binding and its default-zero branch. *)
Definition audit_uf_rank_of {K CE} (enc : K -> positive * list CE) (forest : UnionFind.t K) (key :
  K)
    : nat * list (audit_uf_event K CE) :=
  let '(found, calls) := audit_map_get enc key (UnionFind.ranks forest) in
  (match found with Some n => n | None => 0 end, [AuditUFRankRead key found calls]).

(** Touch executes the rank write only when the original read is absent. *)
Definition audit_uf_touch {K CE} (enc : K -> positive * list CE) (key : K) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  let '(found, reads) := audit_map_get enc key (UnionFind.ranks forest) in
  match found with
  | Some _ => (forest, [AuditUFRankRead key found reads])
  | None =>
      let '(ranks, writes) := audit_map_set enc key 0 (UnionFind.ranks forest) in
      (UnionFind.Forest (UnionFind.parents forest) ranks (UnionFind.max_rank forest),
        [AuditUFRankRead key found reads; AuditUFRankWrite key 0 writes])
  end.

(** A link preserves every strict operand of the rank-raising record construction. *)
Definition audit_uf_link {K CE} (enc : K -> positive * list CE)
    (child root : K) (raise : bool) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  if raise then
    let '(old_rank, rank_reads) := audit_uf_rank_of enc forest root in
    let new_rank := S old_rank in
    let '(parents, parent_writes) := audit_map_set enc child root (UnionFind.parents forest) in
    let '(ranks, rank_writes) := audit_map_set enc root new_rank (UnionFind.ranks forest) in
    let maximum := Nat.max (UnionFind.max_rank forest) new_rank in
    (UnionFind.Forest parents ranks maximum, rank_reads ++
      [AuditUFParentWrite child root parent_writes; AuditUFRankWrite root new_rank rank_writes;
       AuditUFRankMax (UnionFind.max_rank forest) new_rank maximum])
  else
    let '(parents, writes) := audit_map_set enc child root (UnionFind.parents forest) in
    (UnionFind.Forest parents (UnionFind.ranks forest) (UnionFind.max_rank forest),
      [AuditUFParentWrite child root writes]).

(** Union threads both finds and records the actual equality, rank and link branches. *)
Definition audit_uf_union {K CE} (enc : K -> positive * list CE) (x y : K)
    (forest : UnionFind.t K) : UnionFind.t K * list (audit_uf_event K CE) :=
  let '((rx, first), xe) := audit_uf_find enc x forest in
  let '((ry, second), ye) := audit_uf_find enc y first in
  let '(cx, xenc) := enc rx in
  let '(cy, yenc) := enc ry in
  let '(equal, eq) := audit_positive_eqb cx cy in
  let prefix := xe ++ ye ++ [AuditUFEncode rx cx xenc; AuditUFEncode ry cy yenc;
                             AuditUFEqual cx cy equal eq] in
  if equal then
    let '(out, events) := audit_uf_touch enc rx second in (out, prefix ++ events)
  else
    let '(rankx, re1) := audit_uf_rank_of enc second rx in
    let '(ranky, re2) := audit_uf_rank_of enc second ry in
    let compared := Nat.compare rankx ranky in
    let '(out, events) := match compared with
      | Lt => audit_uf_link enc rx ry false second
      | Gt => audit_uf_link enc ry rx false second
      | Eq => audit_uf_link enc ry rx true second
      end in
    (out, prefix ++ re1 ++ re2 ++ [AuditUFRankCompare rankx ranky compared] ++ events).

(** Equivalence testing retains both compressed states and the actual encoded-key comparison. *)
Definition audit_uf_equivb {K CE} (enc : K -> positive * list CE) (x y : K)
    (forest : UnionFind.t K) : (bool * UnionFind.t K) * list (audit_uf_event K CE) :=
  let '((rx, first), xe) := audit_uf_find enc x forest in
  let '((ry, second), ye) := audit_uf_find enc y first in
  let '(cx, xenc) := enc rx in
  let '(cy, yenc) := enc ry in
  let '(equal, eq) := audit_positive_eqb cx cy in
  ((equal, second), xe ++ ye ++ [AuditUFEncode rx cx xenc; AuditUFEncode ry cy yenc;
                                 AuditUFEqual cx cy equal eq]).

(** Support enumeration retains both actual map traversals, union and output traversal. *)
Definition audit_uf_keys {K CE} (forest : UnionFind.t K)
    : list K * list (audit_uf_event K CE) :=
  let '(parents, pe) := audit_map_transform (fun _ : K => (tt, @nil unit))
    (UnionFind.parents forest) in
  let '(ranks, re) := audit_map_transform (fun _ : nat => (tt, @nil unit))
    (UnionFind.ranks forest) in
  let '(merged, ue) := audit_finset_union parents ranks in
  let '(output, oe) := audit_finset_elements merged in
  (output, [AuditUFKeysParents pe; AuditUFKeysRanks re; AuditUFKeysUnion ue; AuditUFKeysElements
    oe]).

(** * Exact future result obligations *)

Definition audit_uf_find_fuel_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) fuel key forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_find_fuel enc fuel key forest) = UnionFind.find_fuel original fuel key forest.

Definition audit_uf_find_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) key forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_find enc key forest) = UnionFind.find original key forest.

Definition audit_uf_union_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) x y forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_union enc x y forest) = UnionFind.union original x y forest.

Definition audit_uf_equivb_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) x y forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_equivb enc x y forest) = UnionFind.equivb original x y forest.

Definition audit_uf_keys_erases_statement : Prop :=
  forall K CE (original : encoding K) (forest : UnionFind.t K),
    fst (@audit_uf_keys K CE forest) = UnionFind.keys original forest.

(** * Fixed source-block work and input-derived bounds *)

(** Unary rank operations charge their actual constructor traversals. *)
Definition audit_uf_unary_compare_work (left right : nat) : nat := 3 * S (Nat.min left right).

Fixpoint audit_uf_primitive_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_uf_event K CE)) : nat :=
  match events with
  | [] => 0
  | AuditUFParentRead _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFParentWrite _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankRead _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankWrite _ _ calls :: rest => audit_map_source_work enc_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFEncode _ _ calls :: rest => enc_work calls + audit_uf_primitive_work enc_work rest
  | AuditUFEqual _ _ _ calls :: rest => audit_positive_eqb_source_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankCompare x y _ :: rest => audit_uf_unary_compare_work x y +
      audit_uf_primitive_work enc_work rest
  | AuditUFRankMax x y _ :: rest => audit_uf_unary_compare_work x y +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysParents calls :: rest => audit_map_transform_source_work (fun _ => 0) calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysRanks calls :: rest => audit_map_transform_source_work (fun _ => 0) calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysUnion calls :: rest => audit_finset_union_source_work calls +
      audit_uf_primitive_work enc_work rest
  | AuditUFKeysElements calls :: rest => audit_set_elements_work calls +
      audit_uf_primitive_work enc_work rest
  | _ :: rest => audit_uf_primitive_work enc_work rest
  end.

Definition audit_uf_source_work {K CE} (enc_work : list CE -> nat)
    (events : list (audit_uf_event K CE)) : nat :=
  4 * length events + audit_uf_primitive_work enc_work events.

(** The bounds count the real fuel or max-rank input, not an arbitrary output cost. *)
Definition audit_uf_find_fuel_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) fuel key forest,
    length (snd (audit_uf_find_fuel enc fuel key forest)) <= 1 + 3 * fuel.

Definition audit_uf_union_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) x y forest,
    length (snd (audit_uf_union enc x y forest)) <= 16 + 6 * S (UnionFind.max_rank forest).

Definition audit_uf_equivb_count_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) x y forest,
    length (snd (audit_uf_equivb enc x y forest)) <= 5 + 6 * S (UnionFind.max_rank forest).

Definition audit_uf_find_fuel_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work fuel key forest,
    let events := snd (audit_uf_find_fuel enc fuel key forest) in
    audit_uf_source_work enc_work events <=
      4 * (1 + 3 * fuel) + audit_uf_primitive_work enc_work events.

Definition audit_uf_union_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work x y forest,
    let events := snd (audit_uf_union enc x y forest) in
    audit_uf_source_work enc_work events <=
      4 * (16 + 6 * S (UnionFind.max_rank forest)) + audit_uf_primitive_work enc_work events.

Definition audit_uf_equivb_work_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work x y forest,
    let events := snd (audit_uf_equivb enc x y forest) in
    audit_uf_source_work enc_work events <=
      4 * (5 + 6 * S (UnionFind.max_rank forest)) + audit_uf_primitive_work enc_work events.

(** The fixed parent/rank mapper returns [tt] without a client callback body. *)
Definition audit_uf_keys_work_bound_statement : Prop :=
  forall K CE enc_work (forest : UnionFind.t K),
    let events := snd (@audit_uf_keys K CE forest) in
    audit_uf_source_work enc_work events <= 16 + audit_uf_primitive_work enc_work events.

(** The support bound includes both input trees, actual union and all emitted position bits. *)
Definition audit_uf_keys_input_bound_statement : Prop :=
  forall K CE enc_work (forest : UnionFind.t K),
    let parents := fst (audit_map_transform (fun _ : K => (tt, @nil unit))
      (UnionFind.parents forest)) in
    let ranks := fst (audit_map_transform (fun _ : nat => (tt, @nil unit))
      (UnionFind.ranks forest)) in
    let merged := fst (audit_finset_union parents ranks) in
    audit_uf_source_work enc_work (snd (@audit_uf_keys K CE forest)) <=
      23 + 18 * (audit_trie_nodes (UnionFind.parents forest) + audit_trie_nodes (UnionFind.ranks
        forest)) +
      15 * audit_trie_nodes parents + 19 * audit_trie_nodes merged + audit_trie_output_bits merged.

(** * Linear and branching histories *)

Inductive audit_uf_action (K : Type) : Type :=
  | AuditUFFind (key : K)
  | AuditUFUnion (left right : K).

Arguments AuditUFFind {K} _.
Arguments AuditUFUnion {K} _ _.

Definition audit_uf_action_run {K CE} (enc : K -> positive * list CE)
    (action : audit_uf_action K) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  match action with
  | AuditUFFind key =>
      let '((_, result), events) := audit_uf_find enc key forest in (result, events)
  | AuditUFUnion x y => audit_uf_union enc x y forest
  end.

(** This reference action is the corresponding original library call. *)
Definition audit_uf_original_action {K} (enc : encoding K) (forest : UnionFind.t K)
    (action : audit_uf_action K) : UnionFind.t K :=
  match action with
  | AuditUFFind key => snd (UnionFind.find enc key forest)
  | AuditUFUnion x y => UnionFind.union enc x y forest
  end.

Fixpoint audit_uf_history {K CE} (enc : K -> positive * list CE)
    (actions : list (audit_uf_action K)) (forest : UnionFind.t K)
    : UnionFind.t K * list (audit_uf_event K CE) :=
  match actions with
  | [] => (forest, [AuditUFHistoryCase 0])
  | action :: rest =>
      let '(next, first) := audit_uf_action_run enc action forest in
      let '(out, tail) := audit_uf_history enc rest next in
      (out, AuditUFHistoryCase (S (length rest)) :: first ++ tail)
  end.

Definition audit_uf_history_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) actions forest,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_history enc actions forest) =
      fold_left (audit_uf_original_action original) actions forest.

(** This mathematical adapter represents the original [of_unions] fold, not extra runtime work. *)
Definition audit_uf_of_unions {K CE} (enc : K -> positive * list CE) (inputs : list (K * K)) :=
  audit_uf_history enc (map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs) UnionFind.make.

Definition audit_uf_of_unions_erases_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) (original : encoding K) inputs,
    (forall k, fst (enc k) = encode original k) ->
    fst (audit_uf_of_unions enc inputs) = UnionFind.of_unions original inputs.

(** The budget tracks max-rank on each actual persistent state before an action. *)
Fixpoint audit_uf_history_frame_budget {K CE} (enc : K -> positive * list CE)
    (actions : list (audit_uf_action K)) (forest : UnionFind.t K) : nat :=
  match actions with
  | [] => 1
  | action :: rest =>
      let next := fst (audit_uf_action_run enc action forest) in
      1 + (match action with
           | AuditUFFind _ => 1 + 3 * S (UnionFind.max_rank forest)
           | AuditUFUnion _ _ => 16 + 6 * S (UnionFind.max_rank forest)
           end) + audit_uf_history_frame_budget enc rest next
  end.

Definition audit_uf_history_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work actions forest,
    let events := snd (audit_uf_history enc actions forest) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget enc actions forest + audit_uf_primitive_work enc_work
        events.

Definition audit_uf_of_unions_source_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work inputs,
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_of_unions enc inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget enc actions UnionFind.make + audit_uf_primitive_work
        enc_work events.

(** Both branches are evaluated from the same original forest, with distinct retained traces. *)
Definition audit_uf_branches {K CE} (enc : K -> positive * list CE)
    (left right : list (audit_uf_action K)) (forest : UnionFind.t K) :=
  (audit_uf_history enc left forest, audit_uf_history enc right forest).

Definition audit_uf_branches_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) enc_work left right forest,
    let branches := audit_uf_branches enc left right forest in
    let le := snd (fst branches) in
    let re := snd (snd branches) in
    audit_uf_source_work enc_work le + audit_uf_source_work enc_work re <=
      4 * (audit_uf_history_frame_budget enc left forest +
           audit_uf_history_frame_budget enc right forest) +
      audit_uf_primitive_work enc_work le + audit_uf_primitive_work enc_work re.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditUnionFindAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditUnionFind.

Theorem audit_uf_find_fuel_erases : audit_uf_find_fuel_erases_statement.
Theorem audit_uf_find_erases : audit_uf_find_erases_statement.
Theorem audit_uf_union_erases : audit_uf_union_erases_statement.
Theorem audit_uf_equivb_erases : audit_uf_equivb_erases_statement.
Theorem audit_uf_keys_erases : audit_uf_keys_erases_statement.
Theorem audit_uf_find_fuel_count : audit_uf_find_fuel_count_statement.
Theorem audit_uf_union_count : audit_uf_union_count_statement.
Theorem audit_uf_equivb_count : audit_uf_equivb_count_statement.
Theorem audit_uf_find_fuel_work_bound : audit_uf_find_fuel_work_bound_statement.
Theorem audit_uf_union_work_bound : audit_uf_union_work_bound_statement.
Theorem audit_uf_equivb_work_bound : audit_uf_equivb_work_bound_statement.
Theorem audit_uf_keys_work_bound : audit_uf_keys_work_bound_statement.
Theorem audit_uf_keys_input_bound : audit_uf_keys_input_bound_statement.
Theorem audit_uf_history_erases : audit_uf_history_erases_statement.
Theorem audit_uf_of_unions_erases : audit_uf_of_unions_erases_statement.
Theorem audit_uf_history_bound : audit_uf_history_bound_statement.
Theorem audit_uf_of_unions_source_bound : audit_uf_of_unions_source_bound_statement.
Theorem audit_uf_branches_bound : audit_uf_branches_bound_statement.
```

## CollectionsAuditUnionFindAdapters

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditUnionFindAdapters.v`.

Public module:
`Galois.Collections.CollectionsAuditUnionFindAdapters`.

```rocq
(** * Concrete composite-key union-find adapters

    These instantiations connect the fixed pair and list encoders to the complete
    persistent union-find history and [of_unions] model. Child encoder traces are
    priced at their actual recursive call sites in each map access. *)
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsUnionFind.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditUnionFind.
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

Definition audit_uf_pair_of_unions_erases_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
    (e1 : encoding A) (e2 : encoding B) inputs,
    (forall a, fst (first a) = encode e1 a) ->
    (forall b, fst (second b) = encode e2 b) ->
    fst (audit_uf_pair_of_unions first second inputs) =
      UnionFind.of_unions (pair_encoding e1 e2) inputs.

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

Definition audit_uf_pair_of_unions_source_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
    first_work second_work inputs,
    let enc_work := audit_uf_pair_encoder_work first_work second_work in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_pair_of_unions first second inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget (audit_uf_pair_encode first second) actions UnionFind.make +
      audit_uf_primitive_work enc_work events.

Definition audit_uf_list_of_unions_source_bound_statement : Prop :=
  forall A E (element : A -> positive * list E) element_work inputs,
    let enc_work := audit_uf_list_encoder_work element_work in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    let events := snd (audit_uf_list_of_unions element inputs) in
    audit_uf_source_work enc_work events <=
      4 * audit_uf_history_frame_budget (audit_uf_list_encode element) actions UnionFind.make +
      audit_uf_primitive_work enc_work events.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditUnionFindAdaptersAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditUnionFindAdapters.

Theorem audit_uf_pair_of_unions_erases : audit_uf_pair_of_unions_erases_statement.
Theorem audit_uf_list_of_unions_erases : audit_uf_list_of_unions_erases_statement.
Theorem audit_uf_pair_of_unions_source_bound : audit_uf_pair_of_unions_source_bound_statement.
Theorem audit_uf_list_of_unions_source_bound : audit_uf_list_of_unions_source_bound_statement.
```

## CollectionsAuditUnionFindWhole

Card: AUD-CL-MODELS

Source destination:
`theories/Collections/CollectionsAuditUnionFindWhole.v`.

Public module:
`Galois.Collections.CollectionsAuditUnionFindWhole`.

```rocq
(** * Whole persistent union-find input budgets

    These recurrences follow actual intermediate forests and keys without reading event work.
    For example, a second find uses the forest returned by the first find, including compression.
    Builds on: the counted union-find bodies and concrete encoder input budgets. *)

From Stdlib Require Import List PArith PeanoNat.
From Galois.Collections Require Import CollectionsEncoding CollectionsUnionFind.
From Galois.Collections Require Import CollectionsAuditMap.
From Galois.Collections Require Import CollectionsAuditPrimitive.
From Galois.Collections Require Import CollectionsAuditEncoding.
From Galois.Collections Require Import CollectionsAuditUnionFind.
From Galois.Collections Require Import CollectionsAuditUnionFindAdapters.
From Galois.Collections Require Import CollectionsAuditEncoderBudget.
Import List.ListNotations.

Definition audit_uf_read_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat :=
  9 + budget key + 5 * Pos.size_nat (fst (enc key)).

Definition audit_uf_write_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) : nat :=
  6 + budget key + 16 * Pos.size_nat (fst (enc key)).

(** Fuel is the existing source's unary max-rank measure; this model adds no runtime fuel. *)
Fixpoint audit_uf_find_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (fuel : nat) (key : K) (forest : UnionFind.t K) : nat :=
  match fuel with
  | 0 => 4
  | S rest =>
      4 + audit_uf_read_budget enc budget key +
      match fst (audit_map_get enc key (UnionFind.parents forest)) with
      | None => 0
      | Some next => audit_uf_find_input_budget enc budget rest next forest +
          audit_uf_write_budget enc budget key
      end
  end.

Definition audit_uf_touch_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (key : K) (forest : UnionFind.t K) : nat :=
  audit_uf_read_budget enc budget key +
  match fst (audit_map_get enc key (UnionFind.ranks forest)) with
  | Some _ => 0
  | None => audit_uf_write_budget enc budget key
  end.

Definition audit_uf_link_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (child root : K) (raise : bool) (forest : UnionFind.t K) : nat :=
  if raise then
    let old_rank := fst (audit_uf_rank_of enc forest root) in
    audit_uf_read_budget enc budget root + audit_uf_write_budget enc budget child +
    audit_uf_write_budget enc budget root +
    4 + 3 * S (Nat.min (UnionFind.max_rank forest) (S old_rank))
  else audit_uf_write_budget enc budget child.

(** Every rank comparison and maximum uses its actual unary operands. *)
Definition audit_uf_union_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (x y : K) (forest : UnionFind.t K) : nat :=
  let '(rx, first) := fst (audit_uf_find enc x forest) in
  let '(ry, second) := fst (audit_uf_find enc y first) in
  let cx := fst (enc rx) in
  let cy := fst (enc ry) in
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest +
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first +
  12 + budget rx + budget ry + 2 * Nat.min (Pos.size_nat cx) (Pos.size_nat cy) +
  if fst (audit_positive_eqb cx cy) then audit_uf_touch_input_budget enc budget rx second
  else
    let rankx := fst (audit_uf_rank_of enc second rx) in
    let ranky := fst (audit_uf_rank_of enc second ry) in
    audit_uf_read_budget enc budget rx + audit_uf_read_budget enc budget ry +
    4 + 3 * S (Nat.min rankx ranky) +
    match Nat.compare rankx ranky with
    | Lt => audit_uf_link_input_budget enc budget rx ry false second
    | Gt => audit_uf_link_input_budget enc budget ry rx false second
    | Eq => audit_uf_link_input_budget enc budget ry rx true second
    end.

Definition audit_uf_equivb_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (x y : K) (forest : UnionFind.t K) : nat :=
  let '(rx, first) := fst (audit_uf_find enc x forest) in
  let '(ry, _) := fst (audit_uf_find enc y first) in
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) x forest +
  audit_uf_find_input_budget enc budget (S (UnionFind.max_rank first)) y first +
  12 + budget rx + budget ry +
  2 * Nat.min (Pos.size_nat (fst (enc rx))) (Pos.size_nat (fst (enc ry))).

Definition audit_uf_action_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (action : audit_uf_action K) (forest : UnionFind.t K) : nat :=
  match action with
  | AuditUFFind key =>
      audit_uf_find_input_budget enc budget (S (UnionFind.max_rank forest)) key forest
  | AuditUFUnion x y => audit_uf_union_input_budget enc budget x y forest
  end.

(** The recurrence retains every persistent state before the next original action. *)
Fixpoint audit_uf_history_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (actions : list (audit_uf_action K)) (forest : UnionFind.t K) : nat :=
  match actions with
  | [] => 4
  | action :: rest =>
      let next := fst (audit_uf_action_run enc action forest) in
      4 + audit_uf_action_input_budget enc budget action forest +
        audit_uf_history_input_budget enc budget rest next
  end.

(** Whole-operation bounds require a per-key encoder law, never a union-find work premise. *)
Definition audit_uf_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget,
    (forall key, work (snd (enc key)) <= budget key) ->
    (forall fuel key forest,
      audit_uf_source_work work (snd (audit_uf_find_fuel enc fuel key forest)) <=
        audit_uf_find_input_budget enc budget fuel key forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_union enc x y forest)) <=
        audit_uf_union_input_budget enc budget x y forest) /\
    (forall x y forest,
      audit_uf_source_work work (snd (audit_uf_equivb enc x y forest)) <=
        audit_uf_equivb_input_budget enc budget x y forest) /\
    (forall actions forest,
      audit_uf_source_work work (snd (audit_uf_history enc actions forest)) <=
        audit_uf_history_input_budget enc budget actions forest).

(** Pair keys instantiate the fixed pair body; only their external children supply budgets. *)
Definition audit_uf_pair_whole_input_bound_statement : Prop :=
  forall A B EA EB (first : A -> positive * list EA) (second : B -> positive * list EB)
      first_work second_work first_budget second_budget inputs,
    (forall a, first_work (snd (first a)) <= first_budget a) ->
    (forall b, second_work (snd (second b)) <= second_budget b) ->
    let enc := audit_uf_pair_encode first second in
    let budget := audit_pair_input_budget first second first_budget second_budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_pair_encoder_work first_work second_work)
      (snd (audit_uf_pair_of_unions first second inputs)) <=
      audit_uf_history_input_budget enc budget actions UnionFind.make.

(** List keys charge each occurrence of each external element encoder in every real key call. *)
Definition audit_uf_list_whole_input_bound_statement : Prop :=
  forall A CE (element : A -> positive * list CE) work budget inputs,
    (forall a, work (snd (element a)) <= budget a) ->
    let enc := audit_uf_list_encode element in
    let key_budget := audit_list_input_budget element budget in
    let actions := map (fun xy => AuditUFUnion (fst xy) (snd xy)) inputs in
    audit_uf_source_work (audit_uf_list_encoder_work work)
      (snd (audit_uf_list_of_unions element inputs)) <=
      audit_uf_history_input_budget enc key_budget actions UnionFind.make.

(** Branches start at the same original forest and each pays its full persistent history. *)
Definition audit_uf_branches_whole_input_bound_statement : Prop :=
  forall K CE (enc : K -> positive * list CE) work budget left right forest,
    (forall key, work (snd (enc key)) <= budget key) ->
    let branches := audit_uf_branches enc left right forest in
    audit_uf_source_work work (snd (fst branches)) +
      audit_uf_source_work work (snd (snd branches)) <=
    audit_uf_history_input_budget enc budget left forest +
      audit_uf_history_input_budget enc budget right forest.

Example audit_uf_initial_find_whole_budget :
  audit_uf_find_input_budget audit_positive_encode (fun _ => 1) 1 1%positive UnionFind.make = 19.
Proof.
  reflexivity.
Qed.
```

Card: AUD-CL-UF

Future proof module: `Galois.Collections.CollectionsAuditUnionFindWholeAdequacy`.

```rocq
From Galois.Collections Require Import CollectionsAuditUnionFindWhole.

Theorem audit_uf_whole_input_bound : audit_uf_whole_input_bound_statement.
Theorem audit_uf_pair_whole_input_bound : audit_uf_pair_whole_input_bound_statement.
Theorem audit_uf_list_whole_input_bound : audit_uf_list_whole_input_bound_statement.
Theorem audit_uf_branches_whole_input_bound : audit_uf_branches_whole_input_bound_statement.
```


<!-- AUD-API-CL-END -->

<!-- AUD-API-GR-SQ-BEGIN -->

# Graph and SSA source contracts

The definitions describe source work. Future theorem types are proof obligations.

## Galois.Collections.CollectionsAuditQueue

Card: AUD-GR-MODELS

Source destination: `theories/Collections/CollectionsAuditQueue.v`.

```rocq
(** * Persistent queue observations

    This draft records source-shaped operations on the existing persistent priority queue.
    For example, inserting into an occupied heap slot records its link and comparison.
    Builds on: CollectionsEncoding, CollectionsMap, CollectionsHeap and CollectionsTrie. *)

From Stdlib Require Import List Bool PArith Arith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap.
From Galois.Collections Require Import CollectionsAuditCost.
Import List.ListNotations.

(** Events retain operands and map versions needed to account for each operation. *)
Inductive queue_event (K : Type) : Type :=
  | QInsertSlot
  | QMeldSlot
  | QSelectSlot
  | QLink
  | QEntryCompare (a b : PQueue.entry K)
  | QPriorityLt (a b : positive)
  | QPriorityEq (a b : positive)
  | QGet (k : K) (m : Map.t K positive)
  | QSet (k : K) (p : positive) (m : Map.t K positive)
  | QRemove (k : K) (m : Map.t K positive)
  | QEncode (k : K)
  | QChildren (t : PQueue.tree K)
  | QExamined
  | QStale
  | QAccepted
  | QFuelStep.

Arguments QInsertSlot {K}.
Arguments QMeldSlot {K}.
Arguments QSelectSlot {K}.
Arguments QLink {K}.
Arguments QEntryCompare {K}.
Arguments QPriorityLt {K}.
Arguments QPriorityEq {K}.
Arguments QGet {K}.
Arguments QSet {K}.
Arguments QRemove {K}.
Arguments QEncode {K}.
Arguments QChildren {K}.
Arguments QExamined {K}.
Arguments QStale {K}.
Arguments QAccepted {K}.
Arguments QFuelStep {K}.

Definition queue_link {K} (a b : PQueue.tree K) : PQueue.tree K * list (queue_event K) :=
  (PQueue.link a b, [QLink; QEntryCompare (PQueue.root a) (PQueue.root b)]).

Fixpoint queue_insert {K} (t : PQueue.tree K) (h : PQueue.heap K)
    : PQueue.heap K * list (queue_event K) :=
  match h with
  | [] => ([Some t], [QInsertSlot])
  | None :: hs => (Some t :: hs, [QInsertSlot])
  | Some u :: hs =>
    let '(v, ev) := queue_link t u in
    let '(rest, er) := queue_insert v hs in
    (None :: rest, QInsertSlot :: ev ++ er)
  end.

Fixpoint queue_meld {K} (a b : PQueue.heap K) (carry : option (PQueue.tree K))
    : PQueue.heap K * list (queue_event K) :=
  match a with
  | [] =>
    match carry with
    | None => (b, [QMeldSlot])
    | Some t =>
      let '(r, es) := queue_insert t b in
      (r, QMeldSlot :: es)
    end
  | x :: xs =>
    match b with
    | [] =>
      match carry with
      | None => (a, [QMeldSlot])
      | Some t =>
        let '(r, es) := queue_insert t a in
        (r, QMeldSlot :: es)
      end
    | y :: ys =>
      let '(slot, carry', links) :=
        match x, y, carry with
        | None, None, c => (c, None, [])
        | Some t, None, None | None, Some t, None => (Some t, None, [])
        | Some t, Some u, None | Some t, None, Some u | None, Some t, Some u =>
          let '(v, es) := queue_link t u in
          (None, Some v, es)
        | Some t, Some u, Some c =>
          let '(v, es) := queue_link t u in
          (Some c, Some v, es)
        end in
      let '(r, es) := queue_meld xs ys carry' in
      (PQueue.digit slot r, QMeldSlot :: links ++ es)
    end
  end.

Fixpoint queue_select {K} (h : PQueue.heap K)
    : option (PQueue.tree K * PQueue.heap K) * list (queue_event K) :=
  match h with
  | [] => (None, [QSelectSlot])
  | x :: xs =>
    let '(v, es) := queue_select xs in
    match v with
    | None =>
      (match x with
       | None => None
       | Some t => Some (t, [])
       end, QSelectSlot :: es)
    | Some (t, rest) =>
      match x with
      | None => (Some (t, PQueue.digit None rest), QSelectSlot :: es)
      | Some u =>
        (if PQueue.precedesb (PQueue.root u) (PQueue.root t)
         then Some (u, PQueue.digit None xs) else Some (t, PQueue.digit (Some u) rest),
         QSelectSlot :: es ++ [QEntryCompare (PQueue.root u) (PQueue.root t)])
      end
    end
  end.

Definition queue_remove_min {K} (h : PQueue.heap K)
    : option (PQueue.entry K * PQueue.heap K) * list (queue_event K) :=
  let '(v, es) := queue_select h in
  match v with
  | None => (None, es)
  | Some (t, rest) =>
    let children := PQueue.children_heap t in
    let '(merged, em) := queue_meld children rest None in
    (Some (PQueue.root t, merged), es ++ [QChildren t] ++ em)
  end.

Definition queue_push {K} (E : encoding K) (p : positive) (k : K) (q : PQueue.t K)
    : PQueue.t K * list (queue_event K) :=
  let go n :=
    let '(h, es) := queue_insert (PQueue.Tree (p, encode E k, k) []) (PQueue.pending q) in
    (PQueue.Queue h (Map.set E k p (PQueue.live q)) n (S (PQueue.pending_count q)),
     [QEncode k] ++ es ++ [QSet k p (PQueue.live q)]) in
  match PQueue.priority E k q with
  | None =>
    let '(r, es) := go (S (PQueue.live_count q)) in
    (r, QGet k (PQueue.live q) :: es)
  | Some old =>
    if Pos.ltb p old then
      let '(r, es) := go (PQueue.live_count q) in
      (r, QGet k (PQueue.live q) :: QPriorityLt p old :: es)
    else (q, [QGet k (PQueue.live q); QPriorityLt p old])
  end.

Fixpoint queue_pop_fuel {K} (E : encoding K) (fuel : nat) (h : PQueue.heap K)
    (m : Map.t K positive) (n : nat)
    : option (positive * K * PQueue.t K) * list (queue_event K) :=
  match fuel with
  | 0 => (None, [QFuelStep])
  | S rest =>
    let '(v, es) := queue_remove_min h in
    match v with
    | None => (None, QFuelStep :: es)
    | Some ((p, c, k), h') =>
      match Map.get E k m with
      | Some current =>
        if Pos.eqb p current then
          (Some (p, k, PQueue.Queue h' (Map.remove E k m) (Nat.pred n) rest),
           QFuelStep :: es ++ [QExamined; QGet k m; QPriorityEq p current; QAccepted;
                               QRemove k m])
        else
          let '(r, er) := queue_pop_fuel E rest h' m n in
          (r, QFuelStep :: es ++ [QExamined; QGet k m; QPriorityEq p current; QStale] ++ er)
      | None =>
        let '(r, er) := queue_pop_fuel E rest h' m n in
        (r, QFuelStep :: es ++ [QExamined; QGet k m; QStale] ++ er)
      end
    end
  end.

Definition queue_pop {K} (E : encoding K) (q : PQueue.t K) :=
  queue_pop_fuel E (PQueue.pending_count q) (PQueue.pending q) (PQueue.live q)
    (PQueue.live_count q).

Inductive queue_push_execution {K} (E : encoding K) (priority : positive) (key : K)
    (state : PQueue.t K) : PQueue.t K -> list (queue_event K) -> Prop :=
  | QueuePushNew heap insert_events :
      PQueue.priority E key state = None ->
      queue_insert (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state) =
        (heap, insert_events) ->
      queue_push_execution E priority key state
        (PQueue.Queue heap (Map.set E key priority (PQueue.live state))
          (S (PQueue.live_count state)) (S (PQueue.pending_count state)))
        (QGet key (PQueue.live state) :: [QEncode key] ++ insert_events ++
          [QSet key priority (PQueue.live state)])
  | QueuePushLower old heap insert_events :
      PQueue.priority E key state = Some old -> Pos.ltb priority old = true ->
      queue_insert (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state) =
        (heap, insert_events) ->
      queue_push_execution E priority key state
        (PQueue.Queue heap (Map.set E key priority (PQueue.live state))
          (PQueue.live_count state) (S (PQueue.pending_count state)))
        (QGet key (PQueue.live state) :: QPriorityLt priority old :: [QEncode key] ++
    insert_events ++
          [QSet key priority (PQueue.live state)])
  | QueuePushUnchanged old :
      PQueue.priority E key state = Some old -> Pos.ltb priority old = false ->
      queue_push_execution E priority key state state
        [QGet key (PQueue.live state); QPriorityLt priority old].

Inductive queue_pop_fuel_execution {K} (E : encoding K) :
    nat -> PQueue.heap K -> Map.t K positive -> nat ->
    option (positive * K * PQueue.t K) -> list (queue_event K) -> Prop :=
  | QueuePopZero heap live count :
      queue_pop_fuel_execution E 0 heap live count None [QFuelStep]
  | QueuePopEmpty rest heap live count remove_events :
      queue_remove_min heap = (None, remove_events) ->
      queue_pop_fuel_execution E (S rest) heap live count None (QFuelStep :: remove_events)
  | QueuePopAccepted rest heap live count priority code key next_heap remove_events :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = Some priority ->
      queue_pop_fuel_execution E (S rest) heap live count
        (Some (priority, key, PQueue.Queue next_heap (Map.remove E key live) (Nat.pred count) rest))
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QPriorityEq priority priority;
          QAccepted; QRemove key live])
  | QueuePopStale rest heap live count priority code key next_heap current remove_events result
    later :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = Some current -> Pos.eqb priority current = false ->
      queue_pop_fuel_execution E rest next_heap live count result later ->
      queue_pop_fuel_execution E (S rest) heap live count result
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QPriorityEq priority current;
    QStale] ++ later)
  | QueuePopMissing rest heap live count priority code key next_heap remove_events result later :
      queue_remove_min heap = (Some ((priority, code, key), next_heap), remove_events) ->
      Map.get E key live = None ->
      queue_pop_fuel_execution E rest next_heap live count result later ->
      queue_pop_fuel_execution E (S rest) heap live count result
        (QFuelStep :: remove_events ++ [QExamined; QGet key live; QStale] ++ later).

(** Both outer source relations have an actual counted run and the existing result. *)
Definition queue_outer_execution_statement : Prop :=
  (forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    queue_push_execution E priority key state result events /\
    result = PQueue.push E priority key state) /\
  (forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    queue_pop_fuel_execution E fuel heap live count result events /\
    result = PQueue.pop_fuel E fuel heap live count).


(** Each traced queue operation returns the existing operation's exact result. *)
Definition queue_projection_laws : Prop :=
  (forall K (t : PQueue.tree K) h, fst (queue_insert t h) = PQueue.insert t h) /\
  (forall K (a b : PQueue.heap K) c, fst (queue_meld a b c) = PQueue.meld a b c) /\
  (forall K (h : PQueue.heap K), fst (queue_select h) = PQueue.select h) /\
  (forall K (h : PQueue.heap K), fst (queue_remove_min h) = PQueue.remove_min h) /\
  (forall K (E : encoding K) p k q, fst (queue_push E p k q) = PQueue.push E p k q) /\
  (forall K (E : encoding K) fuel h m n,
    fst (queue_pop_fuel E fuel h m n) = PQueue.pop_fuel E fuel h m n) /\
  (forall K (E : encoding K) q, fst (queue_pop E q) = PQueue.pop E q).

(** * Event cost dimensions *)

(** Each map event includes its encoder; [QEncode] records the heap entry key. *)
Definition queue_event_keys {K} (event : queue_event K) : list K :=
  match event with
  | QGet k _ | QSet k _ _ | QRemove k _ | QEncode k => [k]
  | _ => []
  end.

Definition queue_key_calls {K} (events : list (queue_event K)) : list K :=
  flat_map queue_event_keys events.

Definition queue_key_bits {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun k n => Pos.size_nat (encode E k) + n) 0 (queue_key_calls events).

Definition queue_entry_compare_args {K} (a b : PQueue.entry K) : list (positive * positive) :=
  let p := fst (fst a) in
  let q := fst (fst b) in
  let x := snd (fst a) in
  let y := snd (fst b) in
  [(p, q); (p, q); (x, y)].

Definition queue_comparisons {K} (event : queue_event K) : list (positive * positive) :=
  match event with
  | QEntryCompare a b => queue_entry_compare_args a b
  | QPriorityLt a b | QPriorityEq a b => [(a, b)]
  | _ => []
  end.

Definition queue_compare_calls {K} (events : list (queue_event K)) : list (positive * positive) :=
  flat_map queue_comparisons events.

Definition queue_compare_operand_bits {K} (events : list (queue_event K)) : nat :=
  fold_right (fun '(x, y) n => Pos.size_nat x + Pos.size_nat y + n) 0
    (queue_compare_calls events).

(** Element-cell work excludes the two terminal calls for each child traversal. *)
Definition queue_child_cells {K} (events : list (queue_event K)) : nat :=
  fold_right (fun event n =>
    match event with
    | QChildren (PQueue.Tree _ cs) => 2 * length cs + n
    | _ => n
    end) 0 events.

Definition queue_child_calls {K} (events : list (queue_event K)) : nat :=
  fold_right (fun event n =>
    match event with
    | QChildren (PQueue.Tree _ cs) => 2 + 2 * length cs + n
    | _ => n
    end) 0 events.

Definition queue_stale_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event => match event with
    | QStale => true
    | _ => false
    end) events).

Definition queue_examined_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event => match event with
    | QExamined => true
    | _ => false
    end) events).

(** This ghost count describes retained path positions, not native allocation. *)
Fixpoint queue_remove_nodes {A} (p : positive) (tr : Trie.t A) : nat :=
  (if Trie.is_empty (Trie.remove p tr) then 0 else 1) +
  match p with
  | xH => 0
  | xO q => queue_remove_nodes q (Trie.left tr)
  | xI q => queue_remove_nodes q (Trie.right tr)
  end.

Definition queue_trie_visits {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QGet k _ | QSet k _ _ | QRemove k _ => Pos.size_nat (encode E k)
  | _ => 0
  end.

Definition queue_trie_nodes {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QSet k _ _ => Pos.size_nat (encode E k)
  | QRemove k m => queue_remove_nodes (encode E k) m
  | _ => 0
  end.

Definition queue_total_trie_visits {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun event n => queue_trie_visits E event + n) 0 events.

Definition queue_total_trie_nodes {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  fold_right (fun event n => queue_trie_nodes E event + n) 0 events.

(** Encoder body work is charged independently from encoded bit length. *)

Definition queue_slot_steps {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event => match event with
    | QInsertSlot | QMeldSlot | QSelectSlot => true
    | _ => false
    end) events).

Definition queue_link_count {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event => match event with
    | QLink => true
    | _ => false
    end) events).

Definition queue_fuel_steps {K} (events : list (queue_event K)) : nat :=
  length (filter (fun event => match event with
    | QFuelStep => true
    | _ => false
    end) events).

Definition queue_comparison_model (xy : positive * positive) : nat :=
  audit_binary_weight (Z.pos (fst xy)) (Z.pos (snd xy)).

Definition queue_event_primitive_model {K} (E : encoding K) (event : queue_event K) : nat :=
  match event with
  | QGet key _ => audit_get_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QSet key _ _ => audit_set_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QRemove key _ => audit_remove_weight (encode E key) +
      audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QEncode key => audit_encoding_weight (audit_key_bits_weight (encode E key))
  | QChildren (PQueue.Tree _ children) => 1 + 2 * length children
  | QEntryCompare a b => fold_right (fun xy n => queue_comparison_model xy + n) 0
      (queue_entry_compare_args a b)
  | QPriorityLt a b | QPriorityEq a b => queue_comparison_model (a, b)
  | _ => 0
  end.

Definition queue_model_budget {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  64 * S (length events) * S (length events) + 64 * length events +
    fold_right (fun event n => queue_event_primitive_model E event + n) 0 events.

Definition queue_model_work {K} (E : encoding K) (events : list (queue_event K)) : nat :=
  64 * S (length events) * S (length events) +
    fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events.

Definition queue_model_equation_statement : Prop :=
  forall K (E : encoding K) events, queue_model_work E events = queue_model_budget E events.

Definition queue_insert_counted_statement : Prop :=
  forall K (E : encoding K) (tree : PQueue.tree K) heap,
    let '(result, events) := queue_insert tree heap in
    result = PQueue.insert tree heap /\
    length events <= S (3 * length heap) /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_select_counted_statement : Prop :=
  forall K (E : encoding K) (heap : PQueue.heap K),
    let '(result, events) := queue_select heap in
    result = PQueue.select heap /\
    length events <= S (2 * length heap) /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_meld_counted_statement : Prop :=
  forall K (E : encoding K) (a b : PQueue.heap K) carry,
    let '(result, events) := queue_meld a b carry in
    result = PQueue.meld a b carry /\
    length events <= 2 + 4 * (length a + length b) /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_remove_min_counted_statement : Prop :=
  forall K (E : encoding K) (heap : PQueue.heap K),
    let '(result, events) := queue_remove_min heap in
    result = PQueue.remove_min heap /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_pop_fuel_counted_statement : Prop :=
  forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\
    queue_fuel_steps events <= S fuel /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_push_counted_statement : Prop :=
  forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    result = PQueue.push E priority key state /\
    queue_model_work E events = queue_model_budget E events.

Definition queue_pop_counted_statement : Prop :=
  forall K (E : encoding K) state,
    let '(result, events) := queue_pop E state in
    result = PQueue.pop E state /\
    queue_fuel_steps events <= S (PQueue.pending_count state) /\
    queue_model_work E events = queue_model_budget E events.

Example queue_zero_fuel_is_charged :
  let '(result, events) := queue_pop nat_encoding (@PQueue.empty nat) in
  (result, queue_model_work nat_encoding events) = (None, 320).
Proof.
  reflexivity.
Qed.

Example queue_strict_comparison_all_operands :
  length (queue_entry_compare_args (1%positive, 3%positive, 0%nat)
    (2%positive, 4%positive, 1%nat)) = 3.
Proof.
  reflexivity.
Qed.
From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap
    CollectionsAuditCost.
Import List.ListNotations.

Definition audit_queue_input_width {K} (E : encoding K) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let entries := PQueue.entries heap in
  let live_rows := Map.elements live in
  let keys := extra_keys ++ map snd entries ++ map fst live_rows in
  let numbers := extra_numbers ++ flat_map (fun entry => [fst (fst entry); snd (fst entry)])
    entries ++
    map snd live_rows in
  Nat.max (fold_right Nat.max 0 (map (fun k => audit_key_bits_weight (encode E k)) keys))
    (fold_right Nat.max 0 (map audit_key_bits_weight numbers)).

Definition audit_queue_input_scale {K} (fuel : nat) (heap : PQueue.heap K) : nat :=
  1 + fuel + length heap + length (PQueue.entries heap).

Definition audit_queue_input_event_bound {K} (fuel : nat) (heap : PQueue.heap K) : nat :=
  256 * Nat.pow (S (audit_queue_input_scale fuel heap)) 3.

Definition audit_queue_input_budget {K} (E : encoding K) (fuel : nat) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let size := audit_queue_input_scale fuel heap in
  let count := audit_queue_input_event_bound fuel heap in
  let width := audit_queue_input_width E heap live extra_keys extra_numbers in
  1024 * S count * S count + count * (128 + 12 * width + 8 * size).

Definition audit_queue_push_input_statement : Prop :=
  forall K (E : encoding K) priority key state,
    let '(result, events) := queue_push E priority key state in
    result = PQueue.push E priority key state /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E events <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority].

Definition audit_queue_pop_fuel_input_statement : Prop :=
  forall K (E : encoding K) fuel heap live count,
    let '(result, events) := queue_pop_fuel E fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ length events <=
    audit_queue_input_event_bound fuel heap /\
    queue_model_work E events <= audit_queue_input_budget E fuel heap live [] [].

Definition audit_queue_pop_input_statement : Prop :=
  forall K (E : encoding K) state,
    let '(result, events) := queue_pop E state in
    result = PQueue.pop E state /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E events <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] [].

From Galois.Collections Require Import CollectionsTrie.

Definition audit_queue_encoder_model (K B : Type) : Type := K -> positive * list B.
Definition audit_queue_encoder_erases {K B} (E : encoding K) (encoder :
    audit_queue_encoder_model K B) : Prop :=
  forall k, fst (encoder k) = encode E k.

Definition audit_queue_nested_event (K B : Type) : Type := queue_event K * (option (option
    positive) * list B).

Definition audit_queue_push_nested {K B} (encoder : audit_queue_encoder_model K B)
    (priority : positive) (key : K) (state : PQueue.t K)
    : PQueue.t K * list (audit_queue_nested_event K B) :=
  let '(lookup_code, lookup_body) := encoder key in
  let found := Map.code_get lookup_code (PQueue.live state) in
  let go := fun live_count =>
    let '(tree_code, tree_body) := encoder key in
    let '(heap, events) := queue_insert (PQueue.Tree (priority, tree_code, key) [])
    (PQueue.pending state) in
    let '(set_code, set_body) := encoder key in
    (PQueue.Queue heap (Trie.set set_code (key, priority) (PQueue.live state)) live_count
      (S (PQueue.pending_count state)),
     (QEncode key, (None, tree_body)) :: map (fun e => (e, (None, []))) events ++ [(QSet key
    priority (PQueue.live state), (None, set_body))]) in
  match found with
  | None => let '(result, events) := go (S (PQueue.live_count state)) in
      (result, (QGet key (PQueue.live state), (Some found, lookup_body)) :: events)
  | Some old => let lower := Pos.ltb priority old in
    if lower then let '(result, events) := go (PQueue.live_count state) in
      (result, (QGet key (PQueue.live state), (Some found, lookup_body)) :: (QPriorityLt
    priority old, (None, [])) :: events)
    else (state, [(QGet key (PQueue.live state), (Some found, lookup_body)); (QPriorityLt
    priority old, (None, []))])
  end.

Fixpoint audit_queue_pop_fuel_nested {K B} (encoder : audit_queue_encoder_model K B)
    (fuel : nat) (heap : PQueue.heap K) (live : Map.t K positive) (count : nat)
    : option (positive * K * PQueue.t K) * list (audit_queue_nested_event K B) :=
  match fuel with
  | 0 => (None, [(QFuelStep, (None, []))])
  | S rest => let '(selected, select_events) := queue_remove_min heap in
    match selected with
    | None => (None, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events)
    | Some ((priority, code, key), remaining) =>
      let '(lookup_code, lookup_body) := encoder key in let current := Map.code_get lookup_code
    live in
      match current with
      | Some actual => let equal := Pos.eqb priority actual in
        if equal then let '(remove_code, remove_body) := encoder key in
          (Some (priority, key, PQueue.Queue remaining (Trie.remove remove_code live) (Nat.pred
    count) rest),
           (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
           [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QPriorityEq
    priority actual, (None, []));
            (QAccepted, (None, [])); (QRemove key live, (None, remove_body))])
        else let '(result, events) := audit_queue_pop_fuel_nested encoder rest remaining live
    count in
          (result, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
            [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QPriorityEq
    priority actual, (None, [])); (QStale, (None, []))] ++ events)
      | None => let '(result, events) := audit_queue_pop_fuel_nested encoder rest remaining live
    count in
          (result, (QFuelStep, (None, [])) :: map (fun e => (e, (None, []))) select_events ++
            [(QExamined, (None, [])); (QGet key live, (Some current, lookup_body)); (QStale,
    (None, []))] ++ events)
      end
    end
  end.

Definition audit_queue_pop_nested {K B} (encoder : audit_queue_encoder_model K B) (state :
    PQueue.t K) :=
  audit_queue_pop_fuel_nested encoder (PQueue.pending_count state) (PQueue.pending state)
    (PQueue.live state) (PQueue.live_count state).

Definition audit_queue_nested_body_work {K B} (weight : B -> nat) (events : list
    (audit_queue_nested_event K B)) : nat :=
  fold_right (fun event total => fold_right (fun item n => weight item + n) 0 (snd (snd event))
    + total) 0 events.

Definition audit_queue_nested_total_work {K B} (E : encoding K) (weight : B -> nat)
    (events : list (audit_queue_nested_event K B)) : nat :=
  queue_model_work E (map fst events) + audit_queue_nested_body_work weight events.

Definition audit_queue_push_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_push_nested encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority].

Definition audit_queue_pop_fuel_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) fuel heap live count,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_pop_fuel_nested encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ map fst events = snd (queue_pop_fuel E
    fuel heap live count) /\
    length events <= audit_queue_input_event_bound fuel heap /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E fuel heap live [] [].

Definition audit_queue_pop_nested_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_pop_nested encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] [].

Definition audit_queue_capture_encoder {K B} (encoder : audit_queue_encoder_model K B)
    : audit_queue_encoder_model K (positive * list B) :=
  fun key => let '(code, body) := encoder key in (code, [(code, body)]).

Definition audit_queue_recorded_push {K B} (encoder : audit_queue_encoder_model K B)
    (priority : positive) (key : K) (state : PQueue.t K) :=
  audit_queue_push_nested (audit_queue_capture_encoder encoder) priority key state.

Definition audit_queue_recorded_pop {K B} (encoder : audit_queue_encoder_model K B) (state :
    PQueue.t K) :=
  audit_queue_pop_nested (audit_queue_capture_encoder encoder) state.

Definition audit_queue_recorded_pop_fuel {K B} (encoder : audit_queue_encoder_model K B)
    (fuel : nat) (heap : PQueue.heap K) (live : Map.t K positive) (count : nat) :=
  audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder) fuel heap live count.

Definition audit_queue_recorded_body_work {K B} (weight : B -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  audit_queue_nested_body_work (fun captured => 1 + fold_right (fun item n => weight item + n) 0
    (snd captured)) events.

Definition audit_queue_recorded_codes {K B} (E : encoding K)
    (events : list (audit_queue_nested_event K (positive * list B))) : Prop :=
  Forall (fun recorded => let '(event, (observed, bodies)) := recorded in
    match event with
    | QGet key m => observed = Some (Map.get E key m) /\ exists body, bodies = [(encode E key,
    body)]
    | QSet key _ _ | QRemove key _ | QEncode key =>
        observed = None /\ exists body, bodies = [(encode E key, body)]
    | _ => observed = None /\ bodies = [] end) events.

Definition audit_queue_recorded_statement : Prop :=
  (forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_push encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority]) /\
  (forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    queue_model_work E (map fst events) <= audit_queue_input_budget E (PQueue.pending_count state)
      (PQueue.pending state) (PQueue.live state) [] []).

Definition audit_queue_family_statement : Prop :=
  queue_outer_execution_statement /\ queue_projection_laws /\
  queue_insert_counted_statement /\ queue_select_counted_statement /\
    queue_meld_counted_statement /\
  queue_remove_min_counted_statement /\ queue_pop_fuel_counted_statement /\
  audit_queue_push_input_statement /\ audit_queue_pop_fuel_input_statement /\
    audit_queue_pop_input_statement /\
  audit_queue_push_nested_statement /\ audit_queue_pop_fuel_nested_statement /\
    audit_queue_pop_nested_statement /\
  audit_queue_recorded_statement.
From Galois.Collections Require Import CollectionsTrie.
From Galois.Collections Require Import CollectionsAuditTrie CollectionsAuditPrimitive
  CollectionsAuditCompare.

Definition audit_queue_ltb_source_work (a b : positive) : nat :=
  audit_positive_order_source_work (snd (audit_positive_ltb a b)).

Definition audit_queue_leb_source_work (a b : positive) : nat :=
  audit_positive_order_source_work (snd (audit_positive_leb a b)).

Definition audit_queue_eq_source_work (a b : positive) : nat :=
  audit_positive_eqb_source_work (snd (audit_positive_eqb a b)).

Definition audit_queue_recorded_source_event {K B}
    (recorded : audit_queue_nested_event K (positive * list B)) : nat :=
  let '(event, (_, bodies)) := recorded in
  64 + match event, bodies with
  | QGet _ input, [(code, _)] => 5 + audit_trie_get_source_work code input
  | QSet key priority input, [(code, _)] =>
      2 + audit_trie_update_source_work code (Some (key, priority)) input
  | QRemove _ input, [(code, _)] => 2 + audit_trie_update_source_work code None input
  | QEntryCompare a b, _ =>
      audit_queue_ltb_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_eq_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_leb_source_work (snd (fst a)) (snd (fst b))
  | QPriorityLt a b, _ => audit_queue_ltb_source_work a b
  | QPriorityEq a b, _ => audit_queue_eq_source_work a b
  | QChildren (PQueue.Tree _ children), _ => 2 * length children + 2
  | _, _ => 0
  end.

Definition audit_queue_recorded_internal_source_work {K B}
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  fold_right (fun event total => audit_queue_recorded_source_event event + total) 0 events.

Definition audit_queue_recorded_full_source_work {K B} (weight : B -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  audit_queue_recorded_internal_source_work events + audit_queue_recorded_body_work weight events.

Definition audit_queue_full_input_budget {K} (E : encoding K) (fuel : nat) (heap : PQueue.heap K)
    (live : Map.t K positive) (extra_keys : list K) (extra_numbers : list positive) : nat :=
  let size := audit_queue_input_scale fuel heap in
  let count := audit_queue_input_event_bound fuel heap in
  let width := audit_queue_input_width E heap live extra_keys extra_numbers in
  count * (256 + 64 * S width + 8 * size).

Definition audit_queue_recorded_full_push_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    priority key state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_push encoder priority key state in
    result = PQueue.push E priority key state /\ map fst events = snd (queue_push E priority key
    state) /\
    queue_push_execution E priority key state result (map fst events) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound 1 (PQueue.pending state) /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E 1 (PQueue.pending state) (PQueue.live state) [key]
    [priority] +
      audit_queue_recorded_body_work weight events.

Definition audit_queue_recorded_full_pop_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat) state,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop encoder state in
    result = PQueue.pop E state /\ map fst events = snd (queue_pop E state) /\
    queue_pop_fuel_execution E (PQueue.pending_count state) (PQueue.pending state) (PQueue.live
    state)
      (PQueue.live_count state) result (map fst events) /\ audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound (PQueue.pending_count state) (PQueue.pending
    state) /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E (PQueue.pending_count state) (PQueue.pending state)
    (PQueue.live state) [] [] +
      audit_queue_recorded_body_work weight events.

Definition audit_queue_recorded_full_pop_fuel_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat) fuel
    heap live count,
    audit_queue_encoder_erases E encoder ->
    let '(result, events) := audit_queue_recorded_pop_fuel encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\ map fst events = snd (queue_pop_fuel E
    fuel heap live count) /\
    queue_pop_fuel_execution E fuel heap live count result (map fst events) /\
    audit_queue_recorded_codes E events /\
    length events <= audit_queue_input_event_bound fuel heap /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E fuel heap live [] [] + audit_queue_recorded_body_work
    weight events.

Definition audit_queue_full_source_contract_statement : Prop :=
  audit_positive_compare_cont_statement /\ audit_positive_order_statement /\
  audit_positive_eqb_erases_statement /\ audit_positive_eqb_source_bound_statement /\
  audit_trie_get_source_work_bound_statement /\ audit_trie_update_source_work_bound_statement /\
  audit_trie_get_trace_adequate_statement /\ audit_trie_update_trace_adequate_statement /\
  audit_map_code_get_run_correct_statement /\ audit_queue_family_statement /\
  audit_queue_recorded_full_push_statement /\ audit_queue_recorded_full_pop_fuel_statement /\
  audit_queue_recorded_full_pop_statement.
(** This adapter is only for genuinely external encoder bodies. *)
Record audit_queue_external_encoder_adapter {K B} (E : encoding K)
    (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    (source : K -> positive -> list B -> nat -> Prop) (budget : K -> nat) : Prop := {
  audit_queue_external_encoder_value : audit_queue_encoder_erases E encoder;
  audit_queue_external_encoder_source : forall key code body,
    encoder key = (code, body) ->
    source key code body (fold_right (fun item n => weight item + n) 0 body) /\
    fold_right (fun item n => weight item + n) 0 body <= budget key
}.

Definition audit_queue_recorded_encoder_budget_event {K B} (budget : K -> nat)
    (recorded : audit_queue_nested_event K (positive * list B)) : nat :=
  let '(event, (_, bodies)) := recorded in
  match event, bodies with
  | QGet key _, [_] | QSet key _ _, [_] | QRemove key _, [_] | QEncode key, [_] => budget key
  | _, _ => 0
  end.

Definition audit_queue_recorded_encoder_budget {K B} (budget : K -> nat)
    (events : list (audit_queue_nested_event K (positive * list B))) : nat :=
  fold_right (fun event n => audit_queue_recorded_encoder_budget_event budget event + n) 0 events.

Definition audit_queue_external_encoder_push_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget priority key state,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_push_nested (audit_queue_capture_encoder encoder) priority
  key state in
    result = PQueue.push E priority key state /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E 1 (PQueue.pending state) (PQueue.live state) [key] [priority]
  +
      audit_queue_recorded_encoder_budget budget events.

Definition audit_queue_external_encoder_pop_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget state,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_pop_nested (audit_queue_capture_encoder encoder) state in
    result = PQueue.pop E state /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E (PQueue.pending_count state) (PQueue.pending state)
  (PQueue.live state) [] [] +
      audit_queue_recorded_encoder_budget budget events.

Definition audit_queue_external_encoder_pop_fuel_statement : Prop :=
  forall K B (E : encoding K) (encoder : audit_queue_encoder_model K B) (weight : B -> nat)
    source budget fuel heap live count,
    audit_queue_external_encoder_adapter E encoder weight source budget ->
    let '(result, events) := audit_queue_recorded_pop_fuel encoder fuel heap live count in
    result = PQueue.pop_fuel E fuel heap live count /\
    audit_queue_recorded_full_source_work weight events <=
      audit_queue_full_input_budget E fuel heap live [] [] + audit_queue_recorded_encoder_budget
  budget events.
```

## Galois.Collections.CollectionsAuditNAdd

Card: AUD-GR-MODELS

Source destination: `theories/Collections/CollectionsAuditNAdd.v`.

```rocq
(** * Binary natural addition source model

    Record positive addition, carry and successor calls used by direct IDF counters.
    For example, adding one to an odd value follows its successor carry chain.
    Builds on: the collection positive successor source model. *)
From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsAuditEncoding.
Import List.ListNotations.

(** Events retain actual operands and successor source frames. *)
Inductive audit_idf_nadd_event : Type :=
  | IdfNaddFrame : bool -> positive -> positive -> audit_idf_nadd_event
  | IdfNaddSucc : audit_nat_encoding_event -> audit_idf_nadd_event
  | IdfNaddZero : N -> N -> audit_idf_nadd_event.

(** Addition makes its one-bit carry explicit and uses the actual successor helper. *)
Fixpoint audit_idf_positive_add (carry : bool) (left right : positive) {struct left}
    : positive * list audit_idf_nadd_event :=
  let here := IdfNaddFrame carry left right in
  match left, right with
  | xH, xH => (if carry then 3%positive else 2%positive, [here])
  | xH, xO q =>
      if carry then let '(n, events) := audit_positive_succ q in
        (xO n, here :: map IdfNaddSucc events)
      else (xI q, [here])
  | xH, xI q =>
      let '(n, events) := audit_positive_succ q in
      (if carry then xI n else xO n, here :: map IdfNaddSucc events)
  | xO p, xH =>
      if carry then let '(n, events) := audit_positive_succ p in
        (xO n, here :: map IdfNaddSucc events)
      else (xI p, [here])
  | xI p, xH =>
      let '(n, events) := audit_positive_succ p in
      (if carry then xI n else xO n, here :: map IdfNaddSucc events)
  | xO p, xO q =>
      let '(n, events) := audit_idf_positive_add false p q in
      (if carry then xI n else xO n, here :: events)
  | xO p, xI q =>
      let '(n, events) := audit_idf_positive_add carry p q in
      (if carry then xO n else xI n, here :: events)
  | xI p, xO q =>
      let '(n, events) := audit_idf_positive_add carry p q in
      (if carry then xO n else xI n, here :: events)
  | xI p, xI q =>
      let '(n, events) := audit_idf_positive_add true p q in
      (if carry then xI n else xO n, here :: events)
  end.

(** The natural wrapper takes either zero branch without positive addition. *)
Definition audit_idf_nadd_counted (left right : N) : N * list audit_idf_nadd_event :=
  match left, right with
  | N0, _ => (right, [IdfNaddZero left right])
  | _, N0 => (left, [IdfNaddZero left right])
  | Npos a, Npos b => let '(result, events) := audit_idf_positive_add false a b in
      (Npos result, events)
  end.

(** Input widths bound all carry and successor frames. *)
Definition audit_idf_nadd_width (value : N) : nat :=
  match value with N0 => 0 | Npos p => Pos.size_nat p end.

(** The whole source-work allowance depends only on the operands. *)
Definition audit_idf_nadd_budget (left right : N) : nat :=
  64 * S (audit_idf_nadd_width left + audit_idf_nadd_width right) *
    S (audit_idf_nadd_width left + audit_idf_nadd_width right).

(** The source model has the exact Stdlib result and an input-derived bound. *)
Definition audit_idf_nadd_source_statement : Prop :=
  forall left right,
    let '(result, events) := audit_idf_nadd_counted left right in
    result = N.add left right /\ 16 * S (length events) <= audit_idf_nadd_budget left right.
```

## Galois.Collections.CollectionsAuditPositiveSub

Card: AUD-GR-MODELS

Source destination: `theories/Collections/CollectionsAuditPositiveSub.v`.

```rocq
(** * Positive subtraction source model

    Count the binary subtraction and borrow paths used by direct IDF priorities.
    For example, subtracting one from an even value follows the predecessor carry chain.
    Builds on: Stdlib positive arithmetic. *)
From Stdlib Require Import List PArith.
Import List.ListNotations.

(** Events retain each actual subtraction or predecessor operand. *)
Inductive audit_idf_sub_event : Type :=
  | IdfSubFrame : bool -> positive -> positive -> audit_idf_sub_event
  | IdfSubPredFrame : positive -> audit_idf_sub_event
  | IdfSubFinish : Pos.mask -> positive -> audit_idf_sub_event.

(** The predecessor-of-double helper exposes its complete low-bit borrow chain. *)
Fixpoint audit_idf_pred_double (value : positive) : positive * list audit_idf_sub_event :=
  match value with
  | xH => (xH, [IdfSubPredFrame value])
  | xI p => (xI (xO p), [IdfSubPredFrame value])
  | xO p => let '(result, events) := audit_idf_pred_double p in
      (xI result, IdfSubPredFrame value :: events)
  end.

(** A mask for twice a positive predecessor includes the actual borrow helper when needed. *)
Definition audit_idf_double_pred (value : positive) : Pos.mask * list audit_idf_sub_event :=
  match value with
  | xH => (Pos.IsNul, [IdfSubPredFrame value])
  | xI p => (Pos.IsPos (xO (xO p)), [IdfSubPredFrame value])
  | xO p => let '(result, events) := audit_idf_pred_double p in
      (Pos.IsPos (xO result), IdfSubPredFrame value :: events)
  end.

(** Subtraction carries a single borrow bit and records each actual operand pair. *)
Fixpoint audit_idf_sub_mask (borrow : bool) (left right : positive) {struct right}
    : Pos.mask * list audit_idf_sub_event :=
  let here := IdfSubFrame borrow left right in
  match left, right with
  | xH, xH => (if borrow then Pos.IsNeg else Pos.IsNul, [here])
  | xH, _ => (Pos.IsNeg, [here])
  | xI p, xH =>
      if borrow then let '(result, events) := audit_idf_pred_double p in
        (Pos.IsPos result, here :: events)
      else (Pos.IsPos (xO p), [here])
  | xO p, xH =>
      if borrow then let '(result, events) := audit_idf_double_pred p in (result, here :: events)
      else let '(result, events) := audit_idf_pred_double p in (Pos.IsPos result, here :: events)
  | xI p, xI q =>
      let '(result, events) := audit_idf_sub_mask borrow p q in
      (if borrow then Pos.succ_double_mask result else Pos.double_mask result, here :: events)
  | xI p, xO q =>
      let '(result, events) := audit_idf_sub_mask false p q in
      (if borrow then Pos.double_mask result else Pos.succ_double_mask result, here :: events)
  | xO p, xI q =>
      let '(result, events) := audit_idf_sub_mask true p q in
      (if borrow then Pos.double_mask result else Pos.succ_double_mask result, here :: events)
  | xO p, xO q =>
      let '(result, events) := audit_idf_sub_mask borrow p q in
      (if borrow then Pos.succ_double_mask result else Pos.double_mask result, here :: events)
  end.

(** The public positive subtraction clamps nonpositive differences to one. *)
Definition audit_idf_sub_counted (left right : positive) : positive * list audit_idf_sub_event :=
  let '(mask, events) := audit_idf_sub_mask false left right in
  let result := match mask with Pos.IsPos value => value | _ => 1%positive end in
  (result, events ++ [IdfSubFinish mask result]).

(** Input widths bound all subtraction and borrow frames and trace construction. *)
Definition audit_idf_sub_budget (left right : positive) : nat :=
  64 * (S (Pos.size_nat left + Pos.size_nat right)) * (S (Pos.size_nat left + Pos.size_nat right)).

(** The source model returns exactly the Stdlib result with input-derived work. *)
Definition audit_idf_sub_source_statement : Prop :=
  forall left right,
    let '(result, events) := audit_idf_sub_counted left right in
    result = Pos.sub left right /\ 16 * S (length events) <= audit_idf_sub_budget left right.
```

### Future proofs in `CollectionsAuditNAddAdequacy`

Card: AUD-GR-IDF

Source destination: `theories/Collections/CollectionsAuditNAddAdequacy.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditNAdd.

Theorem audit_idf_nadd_source_holds :
  CollectionsAuditNAdd.audit_idf_nadd_source_statement.
```

### Future proofs in `CollectionsAuditPositiveSubAdequacy`

Card: AUD-GR-IDF

Source destination: `theories/Collections/CollectionsAuditPositiveSubAdequacy.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditPositiveSub.

Theorem audit_idf_sub_source_holds :
  CollectionsAuditPositiveSub.audit_idf_sub_source_statement.
```

### Future proofs in `CollectionsAuditQueueAdequacy`

Card: AUD-GR-QUEUE

Source destination: `theories/Collections/CollectionsAuditQueueAdequacy.v`.

```rocq
From Galois.Collections Require Import CollectionsAuditQueue.

Theorem queue_outer_execution_holds :
  CollectionsAuditQueue.queue_outer_execution_statement.
Theorem queue_model_equation_holds :
  CollectionsAuditQueue.queue_model_equation_statement.
Theorem queue_insert_counted_holds :
  CollectionsAuditQueue.queue_insert_counted_statement.
Theorem queue_select_counted_holds :
  CollectionsAuditQueue.queue_select_counted_statement.
Theorem queue_meld_counted_holds :
  CollectionsAuditQueue.queue_meld_counted_statement.
Theorem queue_remove_min_counted_holds :
  CollectionsAuditQueue.queue_remove_min_counted_statement.
Theorem queue_pop_fuel_counted_holds :
  CollectionsAuditQueue.queue_pop_fuel_counted_statement.
Theorem queue_push_counted_holds :
  CollectionsAuditQueue.queue_push_counted_statement.
Theorem queue_pop_counted_holds :
  CollectionsAuditQueue.queue_pop_counted_statement.
Theorem audit_queue_push_input_holds :
  CollectionsAuditQueue.audit_queue_push_input_statement.
Theorem audit_queue_pop_fuel_input_holds :
  CollectionsAuditQueue.audit_queue_pop_fuel_input_statement.
Theorem audit_queue_pop_input_holds :
  CollectionsAuditQueue.audit_queue_pop_input_statement.
Theorem audit_queue_push_nested_holds :
  CollectionsAuditQueue.audit_queue_push_nested_statement.
Theorem audit_queue_pop_fuel_nested_holds :
  CollectionsAuditQueue.audit_queue_pop_fuel_nested_statement.
Theorem audit_queue_pop_nested_holds :
  CollectionsAuditQueue.audit_queue_pop_nested_statement.
Theorem audit_queue_recorded_holds :
  CollectionsAuditQueue.audit_queue_recorded_statement.
Theorem audit_queue_family_holds :
  CollectionsAuditQueue.audit_queue_family_statement.
Theorem audit_queue_recorded_full_push_correct :
  CollectionsAuditQueue.audit_queue_recorded_full_push_statement.
Theorem audit_queue_recorded_full_pop_correct :
  CollectionsAuditQueue.audit_queue_recorded_full_pop_statement.
Theorem audit_queue_recorded_full_pop_fuel_correct :
  CollectionsAuditQueue.audit_queue_recorded_full_pop_fuel_statement.
Theorem audit_queue_full_source_contract :
  CollectionsAuditQueue.audit_queue_full_source_contract_statement.
Theorem audit_queue_external_encoder_push_correct :
  CollectionsAuditQueue.audit_queue_external_encoder_push_statement.
Theorem audit_queue_external_encoder_pop_correct :
  CollectionsAuditQueue.audit_queue_external_encoder_pop_statement.
Theorem audit_queue_external_encoder_pop_fuel_correct :
  CollectionsAuditQueue.audit_queue_external_encoder_pop_fuel_statement.
```

<!-- AUD-API-GR-SQ-END -->
