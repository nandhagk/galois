# Cost monad

Status: in force

The audit layer is deleted. Core algorithms are written in `Cost.t` and carry cost theorems.
Costs come only from `Cost.t`.

## Why

One costed implementation keeps the executable result and its cost model together.
