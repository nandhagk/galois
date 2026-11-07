# Prefixed basenames

Status: in force

Every `.v` basename is unique and begins with its package name (formerly ruling C8). Theories
contain no `Extract` directive.

## Why

Unique basenames avoid module collisions, and extraction stays in its own layer.
