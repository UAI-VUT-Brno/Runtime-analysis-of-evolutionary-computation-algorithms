---
paper: buskulic-doerr-2021
targets: [C6]
---

# Buskulic & Doerr (2021)

> Queue status for C6 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C6. Buskulic & Doerr (2021): Maximizing Drift Is Not Optimal for Solving OneMax

**Paper:** N. Buskulic, C. Doerr, Evolutionary Computation 29(4), 521--541, DOI `10.1162/evco_a_00290`.

**Result:** runtime-optimal mutation strengths differ from drift-maximizing strengths on many OneMax fitness levels; similar phenomena hold for standard and resampling `(1+1)` EAs.

**Why reachable:** after C5's exact OneMax drift/dynamic-programming layer, this is a closely adjacent separation theorem rather than a new algorithm family.
