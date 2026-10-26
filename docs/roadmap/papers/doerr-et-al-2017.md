---
paper: doerr-et-al-2017
targets: [D3, M6]
current: ../../current/papers/doerr-et-al-2017.md
---

# Doerr, Le, Makhmara & Nguyen (2017)

> Queue status for D3, M6 is in [`frontier.toml`](../frontier.toml).
> What is already certified for this paper: [`current/papers/doerr-et-al-2017.md`](../../current/papers/doerr-et-al-2017.md).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D3. Doerr, Le, Makhmara & Nguyen (2017): Fast Genetic Algorithms

**Paper:** GECCO 2017, 777--784, DOI `10.1145/3071178.3071301`; arXiv:1703.03334.

**Result:** heavy-tailed randomized mutation rates give robust near-instance-optimal performance on Jump and other problems.

**Why reachable:** the static unary-unbiased operator abstraction can represent heavy-tailed radius mixtures and already exposes `p_1`, `chi`, and factorial moments. Jump-function escape analysis would require a new objective but little new mutation semantics.
