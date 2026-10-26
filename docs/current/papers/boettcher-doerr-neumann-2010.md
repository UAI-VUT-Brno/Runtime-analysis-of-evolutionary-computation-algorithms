---
paper: boettcher-doerr-neumann-2010
aliases: [P01]
roadmap: ../../roadmap/papers/boettcher-doerr-neumann-2010.md
---

# P01 — Böttcher, Doerr and Neumann: LeadingOnes fixed and adaptive rates (~85%)

**Verified headline results**

1. **Exact uniform-initial expected optimization time at a fixed rate
   `0 < p < 1`.**
   [`leadingOnesUniformFirstHittingTimeExpectation_eq_formula`](../../../ECRuntime/LeadingOnesOccupationTotalClosure.lean)
   identifies the genuine first-hitting-time mean with the fixed-rate formula;
   [`leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula`](../../../ECRuntime/LeadingOnesScaledRate.lean)
   gives its scaled-rate version.
2. **Asymptotic fixed-rate leading coefficient and uniquely optimal fixed
   scale.**
   [`leadingOnes_scaled_fixedRate_limit`](../../../ECRuntime/LeadingOnesOptimalRate.lean)
   proves the coefficient `(exp(c)-1)/(2c²)` for `p=c/n`;
   [`leadingOnes_fixedRate_unique_optimum`](../../../ECRuntime/LeadingOnesOptimalRate.lean)
   identifies the unique optimum by `(2-c)exp(c)=2`, `1<c<2`.
3. **Exact expected runtime for genuine level-dependent adaptive mutation.**
   [`proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum`](../../../ECRuntime/AdaptiveLeadingOnesTrajectoryRuntimeAssembly.lean)
   and [`proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum`](../../../ECRuntime/AdaptiveLeadingOnesExactUniformRuntime.lean)
   certify, under the stated interior schedule assumptions,
   `E[T] = (1/2) Σ_{i=0}^{n-1} (p_i(1-p_i)^i)⁻¹`. The historical `proposed_`
   prefix does **not** mean the imported theorem remains conjectural.
4. **Optimal fitness-dependent rate and global schedule comparison.**
   [`proposed_leadingOnes_positiveLevelExit_uniqueMaximizer`](../../../ECRuntime/AdaptiveLeadingOnesUniquePositiveLevelOptimizer.lean)
   identifies `p_i=1/(i+1)` at positive levels;
   [`proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff`](../../../ECRuntime/LeadingOnesStrictPositivePolicyOptimality.lean)
   certifies equality rigidity; see also
   [`proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass`](../../../ECRuntime/AdaptiveLeadingOnesScheduleExitComparison.lean).
5. **Boundary behavior of the optimum.**
   [`proposed_leadingOnes_referenceRuntime_boundaryInfimum`](../../../ECRuntime/LeadingOnesBoundaryRuntimeInfimum.lean)
   and [`proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto`](../../../ECRuntime/LeadingOnesReferenceExitCostBoundaryTendsto.lean)
   give the level-zero boundary infimum and finite reference-cost limit.

**Not yet verified in the same source-paper form**

- An **explicit asymptotic theorem** for the optimized adaptive schedule of
  the form `E[T_opt]/n² → C_adapt` with the paper's approximately `0.68`
  constant, followed by its numerical comparison with the best fixed-rate
  `~0.77 n²` coefficient. The finite-dimensional exact formula and rate
  optimality are certified, but this combined limit/comparison has not been
  identified as a separately exported Lean theorem.
- A version-specific check of **all secondary publication corollaries and
  boundary/initialization conventions**. The certified results are substantial
  but not a literal transcription of every result in the proceedings paper.
