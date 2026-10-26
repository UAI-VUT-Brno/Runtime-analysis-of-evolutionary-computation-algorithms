---
paper: lehre-witt-2014
aliases: [P05]
roadmap: ../../roadmap/papers/lehre-witt-2014.md
---

# P05 — Lehre and Witt (2014): general drift and two-sided tails (~15%)

**Verified related specializations**

1. [`multiplicativeDrift_firstHittingTime_tailMass_le`](../../../ECRuntime/MultiplicativeDriftTail.lean)
   gives a specific upper-tail estimate for a finite-state multiplicative
   drift process.
2. [`additiveDrift_runtimeSup_le`](../../../ECRuntime/AdditiveDrift.lean)
   and [`proposed_genericFixedTarget_additiveDrift_runtimeLower`](../../../ECRuntime/GenericFixedTargetAdditiveDriftLower.lean)
   cover expectation-side special cases under explicit potential and drift
   assumptions.

**Not yet verified headline families**

- The paper's **general variable-drift theorem with both upper and lower
  hitting-time tails**, including its overshoot and filtration hypotheses.
- The **sharp concentration applications** to the `(1+1)` EA on general
  linear functions, LeadingOnes, and the other benchmark functions.
- Its **random-permutation cycle** application and general-process
  specializations. The generic drift modules do not imply all these claims.
