---
paper: buzdalov-doerr-2020
targets: [C8]
---

# Buzdalov & Doerr (2020)

> Queue status for C8 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C8. Buzdalov & Doerr (2020): Optimal Mutation Rates for the `(1+lambda)` EA on OneMax

**Paper:** M. Buzdalov, C. Doerr, PPSN XVI (2020), pp. 574--587, DOI `10.1007/978-3-030-58115-2_40`.

**Result:** computational/dynamic-programming characterization of runtime-optimal mutation rates for `(1+lambda)` variants.

**Why reachable:** naturally follows C7; finite-state dynamic programming can reuse the repository's Bellman/runtime infrastructure.
