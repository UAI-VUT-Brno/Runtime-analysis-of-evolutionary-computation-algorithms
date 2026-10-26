---
paper: doerr-doerr-2016
aliases: [P02b]
roadmap: ../../roadmap/papers/doerr-doerr-2016.md
---

# P02b — Doerr and Doerr (2016): random-initialization comparisons (~25%)

**Verified headline subcase**

1. **RLS on OneMax:** the exact uniform-start mean and sharp `-1/2+o(1)`
   correction are certified by
   [`proposed_strictMonotoneRLS_allDimensionPaperSharpCentered`](../../../ECRuntime/RLSAllDimensionPaperSharpCentered.lean)
   and [`proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection`](../../../ECRuntime/DoerrDoerrMonotoneUniformMean.lean).
2. **Related process/coupling calculations for RLS** are certified by
   [`proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS`](../../../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean).
   These strengthen the RLS portion but do not cover the paper's other
   algorithm/problem pairs.

**Not yet verified headline results**

- **`(1+1)` EA on OneMax:** bounded-additive discrepancy between uniform
  and average-fitness initialization, with its source-specific coupling.
- **RLS on LeadingOnes** and **`(1+1)` EA on LeadingOnes:** the
  uniform-versus-average-initialization comparison and the precise
  level-zero/one exit-time discrepancy decomposition.
- The journal article's joint theorem formulation across the **four
  algorithm/problem combinations** with its stated finite-size constants and
  all initialization conventions. The P01 adaptive LeadingOnes runtime
  theorem is not a substitute for this comparison.

The joint theorem-to-paper audit of P02a and P02b is the annex of [`doerr-doerr-2013.md`](doerr-doerr-2013.md).
