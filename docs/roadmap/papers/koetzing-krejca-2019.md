---
paper: koetzing-krejca-2019
targets: [B7]
---

# Kötzing & Krejca (2019)

> Queue status for B7 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## B7. Kötzing & Krejca (2019): First-hitting times under drift

**Paper:** T. Kötzing, M. S. Krejca, *First-hitting times under drift*, TCS 796, 51--69, DOI `10.1016/j.tcs.2019.08.021`.

**Result:** highly general additive, multiplicative, and variable drift theorems with weakened state-space restrictions, plus lower-bound variants under step control.

**Why reachable:** the repository's semantics are already measure-theoretic and unrestricted enough to support these statements. This is a natural way to strengthen the generic theorem library before more lower-bound applications.
