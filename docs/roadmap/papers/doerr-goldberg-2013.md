---
paper: doerr-goldberg-2013
targets: [A4]
---

# Doerr & Goldberg (2013)

> Queue status for A4 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## A4. Doerr & Goldberg (2013): Adaptive Drift Analysis

**Paper:** B. Doerr, L. A. Goldberg, *Adaptive Drift Analysis*, Algorithmica 65(1), 224--250 (2013), DOI `10.1007/s00453-011-9585-3`; arXiv:1108.0295.

**Result:** for every constant `c>0`, the `(1+1)` EA with mutation rate `c/n` optimizes every linear objective in `Theta(n log n)`, using objective-dependent drift functions.

**Why reachable:** the current repository already supports objective-dependent linear potentials and arbitrary fixed `c/n`; this is a natural bridge beyond the frozen Witt C3 regime even before obtaining Witt's sharp constant everywhere.
