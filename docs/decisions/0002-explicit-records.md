# Explicit records

Status: superseded by [the core design](../design/core.md)

Dictionaries are records parametric in their types, and their laws are separate `Prop` records
(formerly ruling C3). The library uses no typeclasses, instances, canonical structures or functors.
Modules are namespaces. A record with a `Type` field extracts to `Obj.magic`.

## Why

Explicit parameters keep dependencies visible and avoid unsafe extracted type fields.
