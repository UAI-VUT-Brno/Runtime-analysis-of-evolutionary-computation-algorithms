---
paper: doerr-doerr-lengler-2019
targets: [B3]
---

# Doerr, Doerr & Lengler (2019)

> Queue status for B3 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## B3. Doerr, Doerr & Lengler (2019): Self-Adjusting Mutation Rates with Provably Optimal Success Rules

**Paper:** B. Doerr, C. Doerr, J. Lengler, *Self-Adjusting Mutation Rates with Provably Optimal Success Rules*, GECCO 2019, DOI `10.1145/3321707.3321733`; arXiv:1902.02588.

**Result:** on LeadingOnes, small update strength and success rate `1/e` achieve asymptotically the same runtime as the best fitness-dependent rate.

**Why reachable:** builds directly on the same LeadingOnes level structure; the new work is a dynamic rate state and success-rule update process.
