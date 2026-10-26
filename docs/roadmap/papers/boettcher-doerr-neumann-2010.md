---
paper: boettcher-doerr-neumann-2010
targets: [B1, B2]
current: ../../current/papers/boettcher-doerr-neumann-2010.md
---

# Böttcher, Doerr & Neumann (2010)

> Queue status for B1, B2 is in [`frontier.toml`](../frontier.toml).
> What is already certified for this paper: [`current/papers/boettcher-doerr-neumann-2010.md`](../../current/papers/boettcher-doerr-neumann-2010.md).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## B1. Böttcher, Doerr & Neumann (2010): optimal static mutation rate on LeadingOnes

**Target result from the already-partially-formalized paper:** optimize the exact fixed-`p` expression and prove `p≈1.59/n` with expected runtime about `0.77n^2`.

**Why reachable:** the exact finite expectation is already fully formalized. This is now primarily real asymptotic/optimization analysis, not stochastic-process work.

## B2. Böttcher, Doerr & Neumann (2010): fitness-dependent adaptive LeadingOnes rate

**Target result:** formalize the exact adaptive-rate expression and the asymptotic `≈0.68n^2` optimum.

**Why reachable:** the difficult exact LeadingOnes entry/residence structure is already present. A state-dependent mutation kernel is the main additional semantic layer.
