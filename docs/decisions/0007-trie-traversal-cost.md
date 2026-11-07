# Trie traversal cost

Status: in force

`Trie.fold` and `Trie.elements` cost O(N + L) (formerly ruling C18). N counts visited nodes
and L sums the bit lengths of emitted keys.

## Why

Materialising keys requires work proportional to their encoded lengths.
