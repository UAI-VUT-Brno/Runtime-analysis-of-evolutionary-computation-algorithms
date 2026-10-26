---
paper: doerr-koetzing-2024
targets: [B9]
---

# Doerr & Kötzing (2024)

> Queue status for B9 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## B9. Doerr & Kötzing (2024): Lower Bounds from Fitness Levels Made Easy

**Paper:** B. Doerr, T. Kötzing, *Lower Bounds from Fitness Levels Made Easy*, Algorithmica 86, 367--395 (2024), DOI `10.1007/s00453-022-00952-w`; conference version GECCO 2021, DOI `10.1145/3449639.3459352`; arXiv:2104.03372.

**Result:** upper/lower fitness-level methods based on level-leaving and visitation probabilities; applications include the exact LeadingOnes runtime and a near-tight OneMax lower bound.

**Why reachable:** level visitation, first entry, and exact LeadingOnes occupation probabilities are already first-class objects in the repository. This may be easier to mechanize than Sudholt's viscosity-parameter method and could become the preferred lower-bound interface.
