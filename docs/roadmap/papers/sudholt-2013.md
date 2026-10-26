---
paper: sudholt-2013
targets: [B8]
---

# Sudholt (2013)

> Queue status for B8 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## B8. Sudholt (2013): A New Method for Lower Bounds on the Running Time of Evolutionary Algorithms

**Paper:** D. Sudholt, IEEE Transactions on Evolutionary Computation 17(3), 418--435, DOI `10.1109/TEVC.2012.2202241`.

**Result:** fitness-level lower-bound method with near-exact results for LeadingOnes, OneMax, long paths, and unique-optimum functions, including mutation-rate dependence.

**Why reachable:** the repository already contains a rich fitness-level/geometric domination stack. Formalizing the lower-bound counterpart would immediately support the missing lower side of several already-formalized upper theorems.
