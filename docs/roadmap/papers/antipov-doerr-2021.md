---
paper: antipov-doerr-2021
targets: [D1]
---

# Antipov & Doerr (2021)

> Queue status for D1 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D1. Antipov & Doerr (2021): Precise Runtime Analysis for Plateau Functions

**Paper:** D. Antipov, B. Doerr, ACM TELO 1(4), Article 13, DOI `10.1145/3469800`.

**Result:** for constant plateau width and an arbitrary unbiased mutation operator, the runtime distribution is close to geometric and is controlled primarily by the probability of flipping between one and `k` bits.

**Why reachable:** arbitrary static unary-unbiased radius laws, geometric waiting-time distributions, and stochastic domination are all already formalized. This is arguably the most direct non-linear-function application of the Stage-68 operator abstraction.
