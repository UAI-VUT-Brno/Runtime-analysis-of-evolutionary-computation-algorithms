---
paper: he-yao-2001
aliases: [P03]
roadmap: ../../roadmap/papers/he-yao-2001.md
---

# P03 — He and Yao (2001): average-time drift analysis (~20%)

**Verified related headline specialization**

1. **Finite-state additive drift upper bound on hitting/optimization time:**
   [`additiveDrift_runtimeSup_le`](../../../ECRuntime/AdditiveDrift.lean)
   and [`additiveDrift_finiteHorizonBound`](../../../ECRuntime/AdditiveDrift.lean).
2. **Drift formulation for finite Markov kernels:**
   [`expectedValueAfter_mono`](../../../ECRuntime/Drift.lean)
   and [`additiveDrift_superSolution`](../../../ECRuntime/AdditiveDrift.lean).

**Not yet verified headline families**

- General **exponential lower-time conditions** in the original formulation.
- The source's **population-based selection/crossover/mutation** EA framework
  and examples, beyond a finite transition kernel used in the library.
- The complete range of **polynomial versus exponential complexity
  classifications and concrete problem constructions** under the paper's
  original hypotheses. A finite-state additive upper theorem is not a full
  re-formalization of the 2001 paper.
