# Paper-by-paper verification coverage

**Audited checkpoint:** 25 October 2026; Lean 4.32.1 / Mathlib v4.32.1.
The independently certified **source checkpoint** contains **547 public Lean
modules**, 19 retained regression-test source modules, 316 promoted registry
entries, two retired-invalid entries, and no active research candidates. The
present **minimal merge onto main** copies all 547 public Lean modules but
only the three additional regression-test files loaded by that checkpoint's
default test root (six test modules total including the three main-branch tests).
It deliberately does **not** import the source registry or retired-claim
archive, preserving the main branch's development files and governance.
The compilation certification belongs to the source checkpoint; the combined
main checkout needs a separate build. This is a *mathematical correspondence
audit*, not a count of all lemmas or paper pages.

## Meaning of the coverage estimates

The percentages below are **approximate coverage of selected headline result
families of each publication**. They are retained to make progress visible,
not to assert that a given percentage of the paper's pages, lemmas, or lines of
proof has been formalized. Each paper is assessed separately against its own
principal claims. The estimates use the following rule:

- **Verified:** an imported, compiled Lean theorem with a matching conclusion
  and relevant assumptions, or a directly stated stronger theorem implying the
  published claim under explicitly documented specializations.
- **Verified special case / partial:** a published result is matched only for a
  restricted algorithm, initial distribution, operator, dimension, parameter
  range, or conclusion. This receives partial rather than complete credit.
- **Not verified:** no public Lean theorem currently establishes the full
  source claim under its published hypotheses. Having a proof of a supporting
  lemma, numerical experiment, or related theorem is not enough.

We use small, manually selected **claim-family inventories**, rather than a
mechanical count of every numbered lemma. Thus percentages are deliberately
rounded (usually to the nearest five percentage points); uncertainty is at
least **10–15 percentage points** for loosely matched publications. The
*verified and unverified inventories below are authoritative over the number*.
Results can overlap between papers and percentages **must not be summed**.
An exact equality of `runtimeSup`, a real-valued mean, a first-hitting-time
integral, and a bounded finite-horizon expectation are **not interchangeable
without a certified bridge**. An iteration count can also differ from a
fitness-evaluation count by initialization or algorithm conventions.

## Coverage at a glance

| ID | Publication | Approximate headline-family coverage | Crucial qualification |
|---|---|---:|---|
| P01 | [Böttcher, Doerr, Neumann (2010), *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*](https://doi.org/10.1007/978-3-642-15844-5_1) | **~85%** | Fixed and genuine adaptive exact means and optimality are certified; the explicit optimized `~0.68 n²` asymptotic statement is not yet located as a theorem |
| P02 | [Doerr, Doerr (2013), *Collecting Coupons with Random Initial Stake*](https://arxiv.org/abs/1308.6384) | **~95% of headline claims** | Both numbered headline theorems have direct certified counterparts; not every paper-specific auxiliary inequality is audited |
| P02b | [Doerr, Doerr (2016), *The Impact of Random Initialization on the Runtime of Randomized Search Heuristics*](https://doi.org/10.1007/s00453-015-0019-5) | **~25%** | Primarily the RLS/OneMax subcase; not the broader `(1+1)`-EA or LeadingOnes comparison families |
| P03 | [He, Yao (2001), *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*](https://doi.org/10.1016/S0004-3702(01)00058-3) | **~20%** | Finite-state additive-drift upper-bound specialization |
| P04 | [Doerr, Johannsen, Winzen (2012), *Multiplicative Drift Analysis*](https://arxiv.org/abs/1101.0776) | **~30%** | Multiplicative-drift bound and selected linear-function consequences, not all applications and matching lower bounds |
| P05 | [Lehre, Witt (2014), *General Drift Analysis with Tail Bounds*](https://arxiv.org/abs/1307.2559) | **~15%** | Specialized drift/tail bounds, not the general variable-drift two-sided theorem |
| P06 | [Doerr (2019), *Analyzing Randomized Search Heuristics via Stochastic Domination*](https://doi.org/10.1016/j.tcs.2018.09.024) | **~35%** | Geometric-waiting and coupling domination, not the universal mutation-based comparison or all applications |
| P07 | [Buzdalov, Doerr, Doerr, Vinokurov (2020/2022), *Fixed-Target Runtime Analysis*](https://arxiv.org/abs/2004.09613) | **~40%** | Exact harmonic lemma and specified RLS/LeadingOnes subcases; broader fixed-target operator families are open |
| P08 | [Jansen, Zarges (2014), *Performance Analysis of Randomised Search Heuristics Operating with a Fixed Budget*](https://doi.org/10.1016/j.tcs.2013.06.007) | **~20%** | Exact RLS/OneMax-type fixed-budget expectation only |
| P09 | [Doerr, Le, Makhmara, Nguyen (2017), *Fast Genetic Algorithms*](https://arxiv.org/abs/1703.03334) | **~20%** | Jump plateau escape and optimal fixed escape rate; no heavy-tailed full-runtime theorem |
| P10 | [Witt (2013), *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*](https://doi.org/10.1017/S0963548312000600) | **~35%** | Sharp standard-rate upper and restricted scaled-rate tails, not complete sharp lower/optimality claims |
| P11 | [Doerr, Janett, Lengler (2024), *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*](https://doi.org/10.1007/s00453-024-01258-9) | **~20% supporting/special cases; 0% of two unrestricted headline bounds** | Moment, coordinate-marginal and conditional upper-bound infrastructure, not the general sharp upper and lower results |
| P12 | [Droste, Jansen, Wegener (2002), *On the Analysis of the (1+1) Evolutionary Algorithm*](https://doi.org/10.1016/S0304-3975(01)00182-7) | **~15% by overlapping consequence** | Positive-linear `O(n log n)` follows from later certified bounds; most original lower/hardness results are open |

**Indicative coverage denominators:** P01 approximately **5/6** core result
families; P02a **2/2** numbered headline theorems (with a small residual
auxiliary audit); P02b **1/4** algorithm/problem combinations; P03 **1/5**;
P04 **2/6**; P05 **1/6**; P06 **2/6**; P07 approximately **2.5/6** after
partial credit for restricted Theorems 4/5; P08 **1/5**; P09 **1/5**;
P10 **2/6**; P11 roughly **1/6 supporting families but 0/2 unrestricted
headline bounds**; and P12 **1/6 by consequence**. These are *researcher-defined
claim groups*, not counts of all numbered lemmas. In particular, a partially
covered theorem family is not equivalent to a fully proved source theorem.

**Interpretation:** P02a and P02b are *different publications*. P07's
conference and expanded journal versions form one literature family here;
version-specific theorem numbering is only used when already checked against
the indicated source. No row claims a completely certified *whole paper*.

## Detailed correspondence audit

### P01 — Böttcher, Doerr and Neumann: LeadingOnes fixed and adaptive rates (~85%)

**Verified headline results**

1. **Exact uniform-initial expected optimization time at a fixed rate
   `0 < p < 1`.**
   [`leadingOnesUniformFirstHittingTimeExpectation_eq_formula`](../ECRuntime/LeadingOnesOccupationTotalClosure.lean)
   identifies the genuine first-hitting-time mean with the fixed-rate formula;
   [`leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula`](../ECRuntime/LeadingOnesScaledRate.lean)
   gives its scaled-rate version.
2. **Asymptotic fixed-rate leading coefficient and uniquely optimal fixed
   scale.**
   [`leadingOnes_scaled_fixedRate_limit`](../ECRuntime/LeadingOnesOptimalRate.lean)
   proves the coefficient `(exp(c)-1)/(2c²)` for `p=c/n`;
   [`leadingOnes_fixedRate_unique_optimum`](../ECRuntime/LeadingOnesOptimalRate.lean)
   identifies the unique optimum by `(2-c)exp(c)=2`, `1<c<2`.
3. **Exact expected runtime for genuine level-dependent adaptive mutation.**
   [`proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum`](../ECRuntime/AdaptiveLeadingOnesTrajectoryRuntimeAssembly.lean)
   and [`proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum`](../ECRuntime/AdaptiveLeadingOnesExactUniformRuntime.lean)
   certify, under the stated interior schedule assumptions,
   `E[T] = (1/2) Σ_{i=0}^{n-1} (p_i(1-p_i)^i)⁻¹`. The historical `proposed_`
   prefix does **not** mean the imported theorem remains conjectural.
4. **Optimal fitness-dependent rate and global schedule comparison.**
   [`proposed_leadingOnes_positiveLevelExit_uniqueMaximizer`](../ECRuntime/AdaptiveLeadingOnesUniquePositiveLevelOptimizer.lean)
   identifies `p_i=1/(i+1)` at positive levels;
   [`proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff`](../ECRuntime/LeadingOnesStrictPositivePolicyOptimality.lean)
   certifies equality rigidity; see also
   [`proposed_leadingOnesAdaptive_uniformRuntime_antitone_exitMass`](../ECRuntime/AdaptiveLeadingOnesScheduleExitComparison.lean).
5. **Boundary behavior of the optimum.**
   [`proposed_leadingOnes_referenceRuntime_boundaryInfimum`](../ECRuntime/LeadingOnesBoundaryRuntimeInfimum.lean)
   and [`proposed_leadingOnes_referenceExitCost_sum_boundaryTendsto`](../ECRuntime/LeadingOnesReferenceExitCostBoundaryTendsto.lean)
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

### P02a — Doerr and Doerr (2013): random-initial-stake coupon collector (~95%)

**Verified headline results**

1. **Paper Theorem 1: sharp randomly initialized coupon-collector mean.**
   [`proposed_randomStakeCoupon_allDimensionPaperSharpCentered`](../ECRuntime/RandomStakeCouponSharpPaperCentered.lean)
   gives the all-dimension centered `-1/2` limit;
   [`proposed_randomStakeCoupon_finitePaperCenteredExact`](../ECRuntime/RandomStakeCouponFinitePaperCenteredExact.lean)
   gives the finite centered identity.
2. **Paper Theorem 2: random-initial RLS on strictly monotone Boolean
   fitness.**
   [`proposed_strictMonotoneRLS_allDimensionPaperSharpCentered`](../ECRuntime/RLSAllDimensionPaperSharpCentered.lean)
   proves the odd/even-compatible `n H_{n/2} - 1/2 + o(1)` expansion,
   and [`proposed_strictMonotoneRLS_allDimensionPaperCentered_exact`](../ECRuntime/RLSAllDimensionPaperCenteredExact.lean)
   gives the exact centered finite formula under the Lean monotonicity
   hypothesis.
3. **Coupon/RLS process identification, including targets and laws.**
   [`proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS`](../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean),
   [`proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS`](../ECRuntime/RandomStakeCouponArbitraryTargetRuntime.lean),
   and [`proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS`](../ECRuntime/RandomStakeCouponArbitraryTargetFiniteHorizon.lean)
   make the comparison direct, not merely an informal consequence.
4. **Finite harmonic/binomial correction and higher observable transfers.**
   [`proposed_binomialHarmonicAverage_closedForm`](../ECRuntime/BinomialHarmonicAverageClosedForm.lean)
   and [`proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS`](../ECRuntime/RandomStakeCouponWeightedSurvivalTransfer.lean)
   certify exact identities; additional higher-moment and infinite-weighted
   transfers appear in
   [`CouponArbitraryPositiveMomentFiniteMass.lean`](../ECRuntime/CouponArbitraryPositiveMomentFiniteMass.lean)
   and [`CouponInfiniteWeightedSurvival.lean`](../ECRuntime/CouponInfiniteWeightedSurvival.lean).

**Not yet verified / not asserted**

- Exhaustive **one-to-one matching of every auxiliary inequality and proof
  detail** in the six-page source, including its exact error-bound conventions.
  Both main numbered theorems have certified counterparts, but 95% is a
  *headline-claim estimate*, not a guarantee that every auxiliary proposition
  has been formalized.
- Any extension of the source's RLS theorem to **arbitrary fitness functions
  without coordinate monotonicity**, or to a different mutation operator;
  these would be new hypotheses/results, not missing cases of Theorem 2.

### P02b — Doerr and Doerr (2016): random-initialization comparisons (~25%)

**Verified headline subcase**

1. **RLS on OneMax:** the exact uniform-start mean and sharp `-1/2+o(1)`
   correction are certified by
   [`proposed_strictMonotoneRLS_allDimensionPaperSharpCentered`](../ECRuntime/RLSAllDimensionPaperSharpCentered.lean)
   and [`proposed_strictMonotoneRLS_uniformInitial_runtimeFiniteCorrection`](../ECRuntime/DoerrDoerrMonotoneUniformMean.lean).
2. **Related process/coupling calculations for RLS** are certified by
   [`proposed_couponProcess_statewiseRuntime_eq_strictMonotoneRLS`](../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean).
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

### P03 — He and Yao (2001): average-time drift analysis (~20%)

**Verified related headline specialization**

1. **Finite-state additive drift upper bound on hitting/optimization time:**
   [`additiveDrift_runtimeSup_le`](../ECRuntime/AdditiveDrift.lean)
   and [`additiveDrift_finiteHorizonBound`](../ECRuntime/AdditiveDrift.lean).
2. **Drift formulation for finite Markov kernels:**
   [`expectedValueAfter_mono`](../ECRuntime/Drift.lean)
   and [`additiveDrift_superSolution`](../ECRuntime/AdditiveDrift.lean).

**Not yet verified headline families**

- General **exponential lower-time conditions** in the original formulation.
- The source's **population-based selection/crossover/mutation** EA framework
  and examples, beyond a finite transition kernel used in the library.
- The complete range of **polynomial versus exponential complexity
  classifications and concrete problem constructions** under the paper's
  original hypotheses. A finite-state additive upper theorem is not a full
  re-formalization of the 2001 paper.

### P04 — Doerr, Johannsen and Winzen (2012): multiplicative drift (~30%)

**Verified headline specializations**

1. **Finite-state multiplicative-drift expected-time theorem:**
   [`multiplicativeDrift_runtimeSup_le`](../ECRuntime/MultiplicativeDrift.lean)
   and [`multiplicativeDrift_finiteHorizonBound`](../ECRuntime/MultiplicativeDrift.lean)
   yield the logarithmic-potential runtime certificate.
2. **Associated hitting-time tail/survival bound:**
   [`multiplicativeDrift_firstHittingTime_tailMass_le`](../ECRuntime/MultiplicativeDriftTail.lean).
3. **Linear objective special case** via positive-linear mutation
   certificates, including
   [`wittStandard_runtimeSup_le_asymptotic_upperBound`](../ECRuntime/WittStandardRuntimeAsymptotics.lean).
   This is mathematical overlap with the drift paper, not a separate proof of
   its originally published constant `1.39e` argument.

**Not yet verified headline families**

- The paper's **specific `(1.39+o(1))e n ln n`** proof in its own
  parameterization and its **matching lower `e n ln n`** result.
- Complete **minimum-spanning-tree, shortest-path, and Euler-tour**
  applications and their problem-specific constants.
- Any **general-state-process formulation** beyond the finite Markov-state
  assumptions actually used by the certified modules.

### P05 — Lehre and Witt (2014): general drift and two-sided tails (~15%)

**Verified related specializations**

1. [`multiplicativeDrift_firstHittingTime_tailMass_le`](../ECRuntime/MultiplicativeDriftTail.lean)
   gives a specific upper-tail estimate for a finite-state multiplicative
   drift process.
2. [`additiveDrift_runtimeSup_le`](../ECRuntime/AdditiveDrift.lean)
   and [`proposed_genericFixedTarget_additiveDrift_runtimeLower`](../ECRuntime/GenericFixedTargetAdditiveDriftLower.lean)
   cover expectation-side special cases under explicit potential and drift
   assumptions.

**Not yet verified headline families**

- The paper's **general variable-drift theorem with both upper and lower
  hitting-time tails**, including its overshoot and filtration hypotheses.
- The **sharp concentration applications** to the `(1+1)` EA on general
  linear functions, LeadingOnes, and the other benchmark functions.
- Its **random-permutation cycle** application and general-process
  specializations. The generic drift modules do not imply all these claims.

### P06 — Doerr (2019): stochastic domination (~35%)

**Verified headline specializations**

1. **Geometric-waiting sum domination via coupling:**
   [`stochasticallyDominated_by_geometricWaitingSum_of_coupling`](../ECRuntime/CouplingDomination.lean)
   and [`natTailDominated_by_geometricWaitingSum_of_coupling`](../ECRuntime/CouplingDomination.lean).
2. **Fitness-level exit-time stochastic domination:**
   [`natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime`](../ECRuntime/LevelExitDomination.lean)
   and [`stochasticallyDominated_refl`](../ECRuntime/StochasticDomination.lean).
3. **OneMax unary operator subcase:**
   [`oneMaxUnary_hittingTime_stochasticDomination`](../ECRuntime/OneMaxUnaryStochasticDomination.lean).

**Not yet verified headline families**

- The paper's universal **`(μ,p)` mutation-based algorithm versus OneMax**
  stochastic comparison for its full class of objectives/operators.
- The **fastest unbiased LeadingOnes algorithm** in the general and static
  operator classes, as distinct from the P01 bit-mutation-rate optimization.
- The source's **Chernoff-type bound for sums of independent coupon-collector
  runtimes**, additional distributional examples, and all resulting sharp
  tail estimates.

### P07 — Buzdalov, Doerr, Doerr and Vinokurov: fixed targets (~40%)

**Verified headline results and subcases**

1. **Paper Lemma 3 (binomial/harmonic identity):**
   [`proposed_binomialHarmonicAverage_closedForm`](../ECRuntime/BinomialHarmonicAverageClosedForm.lean)
   proves `2⁻ⁿ Σ_k binom(n,k) H_k = H_n - Σ_{j=1}^n 1/(j2^j)`.
2. **Paper Theorem 5, RLS/OneMax subcase:**
   [`rlsLinear_fixedTarget_runtimeSup_eq`](../ECRuntime/RLSFixedTarget.lean)
   proves `n(H_d - H_r)` from `d` zero bits to a target with at most `r`;
   [`proposed_strictMonotoneRLS_fixedTarget_runtimeReal_allInitialStates`](../ECRuntime/RLSStrictMonotoneFixedTargetExact.lean)
   extends this to the stated coordinate-monotone fitness class.
3. **Paper Theorem 4, fixed-rate LeadingOnes uniform-start subcase:**
   [`proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum`](../ECRuntime/LeadingOnesFixedTargetCandidate.lean),
   plus target monotonicity and increment/curvature lemmas in
   [`LeadingOnesFixedTargetMeanMonotone.lean`](../ECRuntime/LeadingOnesFixedTargetMeanMonotone.lean)
   and [`LeadingOnesFixedTargetIncrement.lean`](../ECRuntime/LeadingOnesFixedTargetIncrement.lean).
4. **Additional restricted fixed-target lower bounds:**
   [`proposed_oneMaxEA_thresholdRuntime_ge_excessZeroCount_div_np`](../ECRuntime/OneMaxEAThresholdRuntimeLower.lean)
   and [`proposed_unaryOneMax_thresholdRuntime_ge_excessZeroCount_div_meanRadius`](../ECRuntime/UnaryOneMaxThresholdRuntimeLower.lean).
   These do not prove the entire paper's general mutation-operator theorems.

**Not yet verified headline families**

- **Full Theorems 4 and 5** across all operators, initialization classes,
  mutation rates and parameter ranges treated in the source.
- Paper-wide **generic fixed-target fitness-level bounds**, population/
  multi-individual cases, and applications outside the certified OneMax/RLS
  and fixed-rate LeadingOnes subfamilies.
- Matching **all sharp constants, lower and upper bounds and distributional
  conclusions** in the source's broad fixed-target analysis.

### P08 — Jansen and Zarges (2014): fixed-budget performance (~20%)

**Verified headline special case**

1. **One-bit RLS expected remaining zero count** after budget `t`,
   `E[Z_t | Z_0=d] = d(1-1/n)^t`:
   [`rlsLinear_fixedBudget_expectedZeros_eq`](../ECRuntime/RLSFixedBudget.lean).
2. **Uniform-start fixed-budget mean** as a special case:
   [`proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros`](../ECRuntime/RLSUniformInitialFixedBudgetMean.lean).
3. Related **one-bit/unary expected-zero upper bounds** appear in
   [`RLSFixedBudget.lean`](../ECRuntime/RLSFixedBudget.lean) but do not by
   themselves establish the original paper's other fixed-budget theorems.

**Not yet verified headline families**

- The source's **`(1+1)` EA fixed-budget** expected-quality upper and lower
  bounds.
- **LeadingOnes, Jump, Ridge** and other test-function regimes, including
  the corresponding budget-dependent comparisons.
- The full set of source-specific **fixed-budget lower bounds and tight
  quality tradeoffs**; only an RLS/OneMax-type slice is matched here.

### P09 — Doerr, Le, Makhmara and Nguyen (2017): fast genetic algorithms (~20%)

**Verified supporting results / subcases**

1. **Jump plateau one-step escape probability and geometric residence:**
   [`jump_plateau_oneStepSuccessMass`](../ECRuntime/JumpPlateauEscape.lean),
   [`jump_plateau_runtimeSup_eq_geometricMean`](../ECRuntime/JumpPlateauEscape.lean),
   and [`jump_plateau_runtimeTail_eq_geometric`](../ECRuntime/JumpPlateauEscape.lean).
2. **Best fixed mutation rate for plateau escape:**
   [`candidateJumpEscape_fixedRate_optimal`](../ECRuntime/JumpEscapeOptimalRate.lean)
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

### P10 — Witt (2013): linear-function runtime bounds (~35%)

**Verified headline subcases**

1. **Standard-rate upper bound with the sharp leading `e n log n` term
   and `O(n)` correction:**
   [`wittStandard_runtimeSup_le_asymptotic_upperBound`](../ECRuntime/WittStandardRuntimeAsymptotics.lean)
   and [`wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n`](../ECRuntime/WittStandardRuntimeAsymptotics.lean).
2. **First-hitting-time upper/tail bounds** under the stated positive and
   nonincreasing weight restrictions:
   [`wittStandard_firstHittingTime_tailMass_le_geometric`](../ECRuntime/WittStandardRuntimeTail.lean).
3. **Scaled fixed rate `p=c/n` in the certified `0<c≤log 3` regime:**
   [`wittMutation_runtimeSup_le_exactRate_upperBound_logThreeScale`](../ECRuntime/WittMutationLogThreeRuntime.lean)
   and [`wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale`](../ECRuntime/WittMutationLogThreeRuntime.lean).

**Not yet verified headline families**

- **Matching `e n log n` lower bounds**, including the universal lower
  bound across mutation-based algorithms, with the original source's full
  assumptions.
- **All mutation rates `p`** and the sharp constant/scaling conclusions
  outside the restricted `c≤log 3` range.
- The **unrestricted optimality of `p=1/n`** across the stated linear-function
  class and full tight high-probability/tail theorem under the original
  weight-ordering and algorithmic hypotheses.

### P11 — Doerr, Janett and Lengler (2024): static unary unbiased mutation (~20% support; 0% unrestricted headline bounds)

**Verified supporting theorems and restricted consequences**

1. **Coordinate-flip marginal (paper Lemma 2-type statement):**
   [`coordinateFlipMass_eq_meanRadius_div`](../ECRuntime/StaticUnaryUnbiasedFlipMarginals.lean)
   proves uniform coordinate mass `E[K]/n` for the certified symmetric-radius
   mutation-law model.
2. **Mutation-radius moment and pair-marginal inequalities:**
   [`proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius`](../ECRuntime/StaticUnarySecondFactorialRadiusBound.lean)
   and related bounds in
   [`StaticUnaryUnbiasedPairMarginals.lean`](../ECRuntime/StaticUnaryUnbiasedPairMarginals.lean).
3. **Restricted corrected-potential upper estimates:**
   [`correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments`](../ECRuntime/StaticUnaryUnbiasedSharpMomentUpper.lean)
   and [`correctedLinearPotential_runtimeSup_le`](../ECRuntime/StaticUnaryUnbiasedCorrectedRuntime.lean).
   The former has explicit *extra uniform moment requirements*; it is not
   automatically the paper's full general-linear upper theorem.
4. **Separate OneMax/unary lower-drift special cases**, e.g.
   [`proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap`](../ECRuntime/UnaryOneMaxHarmonicLowerScaled.lean),
   address the stated drift-cap subclass, not arbitrary accepted-event
   behavior on positive linear functions.

**Not yet verified headline results**

- **General sharp upper** `(1+o(1)) n ln n / p₁` for the original source's
  full permitted static unary-unbiased operator class, mean-radius bounds
  and assumptions *without strengthening them to second-moment conditions*.
- **General matching lower** bound under the original (potentially different)
  constraints on `p₁`, mean radius `χ` and the initial distribution.
- **Unbounded-mean-radius contrasting examples** and their source-specific
  qualitative trajectory/runtime conclusions.

**Do not count the two unrestricted headline theorems as proved.** The
accepted-event radius and size-bias issues are not discharged by a coordinate
marginal identity alone. The percentage refers to selected supporting and
restricted result families only.

### P12 — Droste, Jansen and Wegener (2002): `(1+1)` EA (~15% overlapping consequence)

**Verified mathematical overlap**

1. **Positive-linear `O(n log n)` expected runtime at the standard
   `p=1/n` rate**, as a consequence of the *later, sharper*
   [`wittStandard_runtimeSup_le_asymptotic_upperBound`](../ECRuntime/WittStandardRuntimeAsymptotics.lean)
   and [`wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n`](../ECRuntime/WittStandardRuntimeAsymptotics.lean).
   This is a consequence under the Lean weight assumptions, **not** a
   standalone re-formalization of the 2002 paper's proof.

**Not yet verified headline families**

- The paper's **necessary mutation-rate regime** claims and large-rate
  examples showing that the `O(n log n)` behavior need not persist.
- **Exponential-time examples for a degree-two polynomial and a unimodal
  function**.
- The source's **hierarchy theorem and remaining complexity separations**.
  No certified source theorem is currently mapped to those claims.

## Important distinctions and next audit actions

1. **No false 100% claims.** P02a's two numbered headline theorems have direct
   counterparts, but no exhaustive formal theorem-by-theorem transcription
   of the publication is asserted. Every other paper has substantial missing
   headline families. In particular, P11 has **zero** unrestricted sharp
   upper/lower theorems.
2. **Research queue closure is not publication completeness.** The audited
   source checkpoint's registry had no active candidates; this minimal merge
   does not copy that registry. This does not imply that unformalized source
   theorems have disappeared. A new paper-level target needs its own approved
   Lean statement under matched published hypotheses.
3. **Some source-related results are stronger or different, not duplicates.**
   Higher moments, arbitrary-target coupon transfers, boundary-rate
   LeadingOnes lemmas and generic drift infrastructure deserve citation as
   independently certified mathematics, but they do not automatically
   increase coverage of every source paper.
4. **For a future 100% certification claim:** fix the particular published
   version, enumerate its numbered results and substantial corollaries, record
   assumptions and initial distributions verbatim, and link each to an
   imported Lean statement or explicitly mark it absent.

For the exact Lean hypotheses and theorem interfaces, follow the source links
above. The main branch's [historical literature frontier](FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md)
and [historical roadmap](LITERATURE_ROADMAP.md) remain for context, but predate
the 547-module checkpoint. The merge preserves the main verification workflow except for an explicit
extension of the public-facade list in `scripts/audit.lean`; see `README.md`
for verification instructions and the outstanding local Lean build requirement. See
[`P02_THEOREM_TO_PAPER_AUDIT.md`](P02_THEOREM_TO_PAPER_AUDIT.md) for the
separate P02a/P02b interpretation and verified coupon/RLS declarations.
