---
paper: doerr-et-al-2013
targets: [C12]
---

# Doerr, Jansen, Sudholt, Winzen & Zarges (2013)

> Queue status for C12 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C12. Doerr, Jansen, Sudholt, Winzen & Zarges (2013): Mutation Rate Matters Even When Optimizing Monotonic Functions

**Paper:** Evolutionary Computation 21(1), 1--27, DOI `10.1162/EVCO_a_00055`.

**Result:** every strictly monotone function is optimized in `Theta(n log n)` for `c<1`, while sufficiently large constant mutation factors yield exponential runtime on some monotone functions.

**Why reachable:** the positive-linear branch is already a subclass of monotone functions, and the repository has fixed-`c/n` mutation semantics and drift. The difficult new object is the adversarial monotone-function construction for the lower/negative result.
