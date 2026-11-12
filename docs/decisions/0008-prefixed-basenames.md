# Prefixed basenames

Status: superseded by [the core design](../design/core.md)

Every `.v` basename is unique and begins with its package name (formerly ruling C8). Theories
contain no `Extract` directive.

## Why

Unique basenames avoid module collisions, and extraction stays in its own layer.
