---
paper: jansen-zarges-2014
aliases: [P08]
roadmap: ../../roadmap/papers/jansen-zarges-2014.md
---

# P08 — Jansen and Zarges (2014): fixed-budget performance (~20%)

**Verified headline special case**

1. **One-bit RLS expected remaining zero count** after budget `t`,
   `E[Z_t | Z_0=d] = d(1-1/n)^t`:
   [`rlsLinear_fixedBudget_expectedZeros_eq`](../../../ECRuntime/RLSFixedBudget.lean).
2. **Uniform-start fixed-budget mean** as a special case:
   [`proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros`](../../../ECRuntime/RLSUniformInitialFixedBudgetMean.lean).
3. Related **one-bit/unary expected-zero upper bounds** appear in
   [`RLSFixedBudget.lean`](../../../ECRuntime/RLSFixedBudget.lean) but do not by
   themselves establish the original paper's other fixed-budget theorems.

**Not yet verified headline families**

- The source's **`(1+1)` EA fixed-budget** expected-quality upper and lower
  bounds.
- **LeadingOnes, Jump, Ridge** and other test-function regimes, including
  the corresponding budget-dependent comparisons.
- The full set of source-specific **fixed-budget lower bounds and tight
  quality tradeoffs**; only an RLS/OneMax-type slice is matched here.
