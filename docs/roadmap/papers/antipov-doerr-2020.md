---
paper: antipov-doerr-2020
targets: [D5]
---

# Antipov & Doerr (2020)

> Queue status for D5 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D5. Antipov & Doerr (2020): Heavy-Tailed `(1+(lambda,lambda))` GA on Jump

**Paper:** D. Antipov, B. Doerr, *Runtime Analysis of a Heavy-Tailed (1+(lambda,lambda)) Genetic Algorithm on Jump Functions*, PPSN 2020; arXiv:2006.03523.

**Result:** instance-independent power-law parameter choices achieve performance close (within controlled polynomial factors) to tuned parameters on Jump functions.

**Why reachable:** mutation-distribution infrastructure transfers, but crossover and two-phase offspring semantics make this more distant than D1/D3.
