---
paper: doerr-rajabi-2023
targets: [D4]
---

# Doerr & Rajabi (2023)

> Queue status for D4 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D4. Doerr & Rajabi (2023): Stagnation Detection Meets Fast Mutation

**Paper:** B. Doerr, A. Rajabi, TCS 946, 113670, DOI `10.1016/j.tcs.2022.12.020`.

**Result:** combines heavy-tailed mutation with stagnation-driven strength adaptation and proves improved probabilities for finding distant improvements.

**Why reachable:** best attempted after D3 plus a generic dynamic-parameter state interface. The current geometric waiting-time layer is useful for the stagnation periods.
