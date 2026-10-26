---
paper: doerr-doerr-yang-2020
targets: [C5]
---

# Doerr, Doerr & Yang (2020)

> Queue status for C5 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C5. Doerr, Doerr & Yang (2020): Optimal Parameter Choices via Precise Black-Box Analysis

**Paper:** B. Doerr, C. Doerr, J. Yang, TCS 801, 1--34, DOI `10.1016/j.tcs.2019.06.014`.

**Result:** precise unary-unbiased black-box complexity of OneMax and a fitness-dependent mutation-strength algorithm that is asymptotically optimal up to lower-order terms.

**Why reachable:** exact static unary-unbiased mask semantics are already available. The missing components are OneMax-specific exact drift optimization and black-box lower bounds.
