---
paper: lehre-witt-2012
targets: [C1]
---

# Lehre & Witt (2012)

> Queue status for C1 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C1. Lehre & Witt (2012): Black-Box Search by Unbiased Variation

**Paper:** P. K. Lehre, C. Witt, Algorithmica 64(4), 623--642, DOI `10.1007/s00453-012-9616-8`.

**Result:** formal unbiased black-box model and `Omega(n log n)` lower bounds for unique-optimum function classes, plus matching examples.

**Why reachable:** `StaticUnaryUnbiasedMutation` already captures the unary operator symmetry on bit strings. The missing layer is an algorithm/query-history black-box model rather than mutation mathematics.
