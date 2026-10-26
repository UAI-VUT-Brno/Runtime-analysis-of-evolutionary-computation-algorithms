---
paper: jaegerskuepper-2008
targets: [A6]
---

# Jägersküpper (2008)

> Queue status for A6 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## A6. Jägersküpper (2008): A Blend of Markov-Chain and Drift Analysis

**Paper:** J. Jägersküpper, *A Blend of Markov-Chain and Drift Analysis*, PPSN X, LNCS 5199, 41--51, DOI `10.1007/978-3-540-87700-4_5`.

**Result:** linear-function runtime analysis via a combination of coordinate-ordering/Markov-chain structure and drift.

**Why reachable:** Markov trajectories, linear objectives, coordinate marginals, and drift are already core repository abstractions. This is a short historical bridge that can also expose reusable monotonicity lemmas for later lower bounds.
