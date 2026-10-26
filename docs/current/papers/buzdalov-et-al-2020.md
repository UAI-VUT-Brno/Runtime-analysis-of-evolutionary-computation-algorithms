---
paper: buzdalov-et-al-2020
aliases: [P07]
roadmap: ../../roadmap/papers/buzdalov-et-al-2020.md
---

# P07 — Buzdalov, Doerr, Doerr and Vinokurov: fixed targets (~40%)

**Verified headline results and subcases**

1. **Paper Lemma 3 (binomial/harmonic identity):**
   [`proposed_binomialHarmonicAverage_closedForm`](../../../ECRuntime/BinomialHarmonicAverageClosedForm.lean)
   proves `2⁻ⁿ Σ_k binom(n,k) H_k = H_n - Σ_{j=1}^n 1/(j2^j)`.
2. **Paper Theorem 5, RLS/OneMax subcase:**
   [`rlsLinear_fixedTarget_runtimeSup_eq`](../../../ECRuntime/RLSFixedTarget.lean)
   proves `n(H_d - H_r)` from `d` zero bits to a target with at most `r`;
   [`proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates`](../../../ECRuntime/RLSStrictMonotoneFixedTargetExact.lean)
   extends this to the stated coordinate-monotone fitness class.
3. **Paper Theorem 4, fixed-rate LeadingOnes uniform-start subcase:**
   [`proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum`](../../../ECRuntime/LeadingOnesFixedTargetCandidate.lean),
   plus target monotonicity and increment/curvature lemmas in
   [`LeadingOnesFixedTargetMeanMonotone.lean`](../../../ECRuntime/LeadingOnesFixedTargetMeanMonotone.lean)
   and [`LeadingOnesFixedTargetIncrement.lean`](../../../ECRuntime/LeadingOnesFixedTargetIncrement.lean).
4. **Additional restricted fixed-target lower bounds:**
   [`proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np`](../../../ECRuntime/OneMaxEAThresholdRuntimeLower.lean)
   and [`proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius`](../../../ECRuntime/UnaryOneMaxThresholdRuntimeLower.lean).
   These do not prove the entire paper's general mutation-operator theorems.

**Not yet verified headline families**

- **Full Theorems 4 and 5** across all operators, initialization classes,
  mutation rates and parameter ranges treated in the source.
- Paper-wide **generic fixed-target fitness-level bounds**, population/
  multi-individual cases, and applications outside the certified OneMax/RLS
  and fixed-rate LeadingOnes subfamilies.
- Matching **all sharp constants, lower and upper bounds and distributional
  conclusions** in the source's broad fixed-target analysis.
