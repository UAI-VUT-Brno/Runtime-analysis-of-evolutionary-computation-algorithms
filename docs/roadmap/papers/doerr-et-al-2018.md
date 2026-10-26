---
paper: doerr-et-al-2018
targets: [C10]
---

# Doerr, Gießen, Witt & Yang (2017/2018)

> Queue status for C10 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C10. Doerr, Gießen, Witt & Yang (2017/2018): self-adjusting mutation rate for `(1+lambda)` EA

**Paper:** B. Doerr, C. Gießen, C. Witt, J. Yang, *The (1+lambda) Evolutionary Algorithm with Self-Adjusting Mutation Rate*, GECCO 2017, DOI `10.1145/3071178.3071279`.

**Result:** expected optimization time `O(n lambda/log lambda + n log n)` on OneMax, asymptotically optimal in the relevant parallel unbiased model.

**Why reachable:** a strong later target after population semantics and the exact `(1+lambda)` OneMax branch are available.
