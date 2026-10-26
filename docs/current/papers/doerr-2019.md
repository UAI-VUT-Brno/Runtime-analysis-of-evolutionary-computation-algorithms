---
paper: doerr-2019
aliases: [P06]
roadmap: ../../roadmap/papers/doerr-2019.md
---

# P06 — Doerr (2019): stochastic domination (~35%)

**Verified headline specializations**

1. **Geometric-waiting sum domination via coupling:**
   [`stochasticallyDominated_by_geometricWaitingSum_of_coupling`](../../../ECRuntime/CouplingDomination.lean)
   and [`natTailDominated_by_geometricWaitingSum_of_coupling`](../../../ECRuntime/CouplingDomination.lean).
2. **Fitness-level exit-time stochastic domination:**
   [`natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime`](../../../ECRuntime/LevelExitDomination.lean)
   and [`stochasticallyDominated_refl`](../../../ECRuntime/StochasticDomination.lean).
3. **OneMax unary operator subcase:**
   [`oneMaxUnary_hittingTime_stochasticDomination`](../../../ECRuntime/OneMaxUnaryStochasticDomination.lean).

**Not yet verified headline families**

- The paper's universal **`(μ,p)` mutation-based algorithm versus OneMax**
  stochastic comparison for its full class of objectives/operators.
- The **fastest unbiased LeadingOnes algorithm** in the general and static
  operator classes, as distinct from the P01 bit-mutation-rate optimization.
- The source's **Chernoff-type bound for sums of independent coupon-collector
  runtimes**, additional distributional examples, and all resulting sharp
  tail estimates.
