---
paper: doerr-et-al-2017
aliases: [P09]
roadmap: ../../roadmap/papers/doerr-et-al-2017.md
---

# P09 — Doerr, Le, Makhmara and Nguyen (2017): fast genetic algorithms (~20%)

**Verified supporting results / subcases**

1. **Jump plateau one-step escape probability and geometric residence:**
   [`jump_plateau_oneStepSuccessMass`](../../../ECRuntime/JumpPlateauEscape.lean),
   [`jump_plateau_runtimeSup_eq_geometricMean`](../../../ECRuntime/JumpPlateauEscape.lean),
   and [`jump_plateau_runtimeTail_eq_geometric`](../../../ECRuntime/JumpPlateauEscape.lean).
2. **Best fixed mutation rate for plateau escape:**
   [`candidateJumpEscape_fixedRate_optimal`](../../../ECRuntime/JumpEscapeOptimalRate.lean)
   establishes the local probability maximum at `p=k/n` for the indicated
   plateau size/rate assumptions.

**Not yet verified headline families**

- **Paper Theorem 1's complete Jump optimization runtime** (the approach
  phase plus escaping the plateau), including its two-sided global bounds.
- **Sensitivity and slow-down bounds** for perturbed fixed rates and the
  full source-specific parameter ranges.
- **Heavy-tailed mutation algorithms** and their almost-optimal Jump
  runtime guarantees; the **matching/vertex-cover** graph applications.
  A geometric plateau escape calculation is not a full fast-GA theorem.
