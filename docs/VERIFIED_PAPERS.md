# Verified source-paper claims: whole-repository catalogue

**Audit checkpoint:** Stage 130, Round 56 (23 October 2026), with the
user-run **full eight-gate verification passed** after Stage 166 promotion
integration. **Lean / Mathlib:** 4.32.1 / v4.32.1. **Certified selected
stages:** 60 (107–166), plus earlier foundations. **Public modules:** 249;
**approved-open candidates:** none. No public theorem statement or proof body
was modified during consolidation.

> **Scope and integrity.** This lists *paper-associated claims with verified
> Lean counterparts*, not a complete mechanization of any publication. Some
> certified theorems start with `proposed_` for historical reasons; their
> status is determined by their compiled public proofs, not their names.
> The Stage 166 source has been promoted, and its original approved header
> remains SHA-256 protected. Where source-paper numbering is unverified,
> the exact Lean declaration is given without inventing a theorem number.

## How to interpret percentages

1. The denominator is a **manual partition into the paper's main claim families**, informed by the publication's abstract/results and the maintained proof frontier. A family can contain several lemmas. It is not a mechanically extracted count of numbered lemmas and is **not a bibliometric statistic**.
2. A family counts as covered only where a public Lean theorem expresses it under the corresponding assumptions. **Restricted special cases** count as partial and do not justify claiming the full source theorem. Derivable but unstated consequences are labelled accordingly. A paper may share a claim with another paper; coverage percentages are **not additive** across publications.
3. Approximate percentages are rounded to five-percent increments; uncertainty is roughly **±10–15 percentage points** for the less directly matched papers. The detailed covered/missing groups below are authoritative over any percentage.
4. **No source paper is audited as 100% covered.** A full-paper claim would require a version-specific theorem-by-theorem comparison, including all assumptions, upper and lower bounds, parameter regimes, variants and substantial corollaries.
5. Runtimes in this repository generally count **mutation iterations** rather than an initial fitness evaluation; `runtimeSup` and finite-survival quantities are not automatically identical to other published cost conventions. The positive-linear RLS setting is narrower than the class of **all strictly monotone** pseudo-Boolean functions. The finite-state versions of generic drift theorems are narrower than unrestricted stochastic-process statements.

## Overview (all literature families with an identified certified counterpart)

| ID | Source publication | Main covered family, exact Lean entrypoints | Estimated coverage of selected claim families | Entire paper? |
|---|---|---|---:|---|
| P01 | [Böttcher–Doerr–Neumann (2010), *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*](https://doi.org/10.1007/978-3-642-15844-5_1) | Exact fixed-rate LeadingOnes expected time, scaled limit, optimal fixed rate | **~50%** | No |
| P02 | [Doerr–Doerr (2016; preprint 2013), *Collecting Coupons with Random Initial Stake*](https://arxiv.org/abs/1308.6384) | Exact binomial/harmonic RLS mean, finite `log 2` correction, first/second-order limits, tail envelope; a new exact survival-distribution extension | **~65%** | No |
| P03 | [He–Yao (2001), *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*](https://doi.org/10.1016/S0004-3702(01)00058-3) | Finite-state additive-drift upper certificates | **~20%** | No |
| P04 | [Doerr–Johannsen–Winzen (2012), *Multiplicative Drift Analysis*](https://arxiv.org/abs/1101.0776) | Finite-state multiplicative drift, harmonic/log runtime certificates | **~30%** | No |
| P05 | [Lehre–Witt (2014), *General Drift Analysis with Tail Bounds*](https://arxiv.org/abs/1307.2559) | Special-case first-hitting-time tail and additive/multiplicative bounds | **~15%** | No |
| P06 | [Doerr (2019), *Analyzing Randomized Search Heuristics via Stochastic Domination*](https://doi.org/10.1016/j.tcs.2018.09.024) | Geometric waiting and fitness-level domination, OneMax specialization | **~35%** | No |
| P07 | [Buzdalov–Doerr–Doerr–Vinokurov (2020 conference / 2022 journal), *Fixed-Target Runtime Analysis*](https://arxiv.org/abs/2004.09613) | Binomial/harmonic lemma, special fixed-target RLS and full-target LeadingOnes cases | **~30%** | No |
| P08 | [Jansen–Zarges (2014), *Performance Analysis of Randomised Search Heuristics Operating with a Fixed Budget*](https://doi.org/10.1016/j.tcs.2013.06.007) | Exact one-bit RLS/OneMax fixed-budget zero-count expectation | **~20%** | No |
| P09 | [Doerr–Le–Makhmara–Nguyen (2017), *Fast Genetic Algorithms*](https://arxiv.org/abs/1703.03334) | Jump plateau escape and best fixed escape rate | **~20%** | No |
| P10 | [Witt (2013), *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*](https://doi.org/10.1017/S0963548312000600) | Sharp standard-rate expected-time upper, restricted scaled-rate/tail bounds | **~35%** | No |
| P11 | [Doerr–Janett–Lengler (2024), *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*](https://doi.org/10.1007/s00453-024-01258-9) | Coordinate-flip marginals, moments, restricted potential/drift bounds | **~15% support; 0% of unrestricted headline bounds** | No |
| P12 | [Droste–Jansen–Wegener (2002), *On the Analysis of the (1+1) Evolutionary Algorithm*](https://doi.org/10.1016/S0304-3975(01)00182-7) | Positive-linear `O(n log n)` implication at standard rate, via a later sharp bound | **~15% (overlapping consequence)** | No |

**Notes on literature identity:** P07 includes the GECCO 2020 proceedings work and its expanded version (arXiv v3, 2021; Algorithmica 2022), not two independently counted publications. P04 uses theorem numbering from the accessible arXiv version of *Multiplicative Drift Analysis*; the published version may differ. For P02 the specific source numbering below refers to the accessible 2013 arXiv version. These caveats matter when comparing numbered claims.

### Coverage numerator/denominator guide

These are deliberately *small, explicitly chosen* headline-family inventories, not a count of every numbered statement in a source PDF. The approximations in the table above round these ratios (with adjustments for partially matched source theorem hypotheses): **P01 3/6**, **P02 approximately 4/6**, **P03 1/5**, **P04 approximately 2/6**, **P05 roughly 1/6**, **P06 roughly 2/6**, **P07 approximately 2/6**, **P08 1/5**, **P09 1/5**, **P10 approximately 2/6**, **P11 about 1/6 supporting groups but 0/2 main claims**, and **P12 approximately 1/6 by consequence**. The corresponding verified and unverified groups are itemized in each section below. In particular, an implication of a theorem is not counted again as a newly formalized source proof.

## Detailed claim-to-theorem correspondences

### P01 — Böttcher, Doerr and Neumann (2010): LeadingOnes

**Verified (three of six selected claim groups):**

- **Exact mean for any fixed independent bit-mutation probability `0 < p < 1`.** `leadingOnesUniformFirstHittingTimeExpectation_eq_formula` in [`LeadingOnesOccupationTotalClosure.lean`](../ECRuntime/LeadingOnesOccupationTotalClosure.lean), supported by [`LeadingOnesMainResults.lean`](../ECRuntime/LeadingOnesMainResults.lean). Closed form: `leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm` in [`LeadingOnesStandardRateClosedForm.lean`](../ECRuntime/LeadingOnesStandardRateClosedForm.lean). Corresponds to the paper's exact fixed-`p` result (the formula proportional to `((1-p)^(-n+1)-(1-p))/(2p²)`).
- **Fixed scaled mutation probability `p=c/n` and asymptotic leading coefficient.** `leadingOnes_scaled_fixedRate_limit` in [`LeadingOnesOptimalRate.lean`](../ECRuntime/LeadingOnesOptimalRate.lean); `leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula` in [`LeadingOnesScaledRate.lean`](../ECRuntime/LeadingOnesScaledRate.lean). The coefficient is `F(c)=(exp(c)-1)/(2c²)`.
- **Optimal asymptotic *fixed* rate.** `leadingOnes_fixedRate_unique_optimum` (same module), with `proposed_leadingOnes_stationaryRoot_exists` in [`LeadingOnesStationaryRootExists.lean`](../ECRuntime/LeadingOnesStationaryRootExists.lean) and `proposed_leadingOnes_uniqueStationaryRoot_Ioo` in [`LeadingOnesUniqueStationaryRoot.lean`](../ECRuntime/LeadingOnesUniqueStationaryRoot.lean). The optimizer lies in `(1,2)` and satisfies `(2-c) exp(c)=2`; **not** an optimizer over fitness-dependent policies.

**Missing:** exact adaptive level-dependent mean; proof of optimal schedule; optimal adaptive constant (around `0.68 n²`) and its lower-bound/optimality comparison. Paper theorem-number mapping for its PPSN version has **not** been independently established, so the precise Lean declaration names above are the stable identifiers. **Coverage: ~50%.**

### P02 — Benjamin and Carola Doerr (2016): random initial coupon stake

**Source numbering (2013 preprint):** **Theorem 1** gives `n H_{n/2}-1/2±o(1)` for coupon collection with random initial stake; **Theorem 2** transfers this to RLS on **all strictly monotone functions**. The version-specific odd-`n` definition of `H_{n/2}` matters. The Lean statements listed here do **not** directly certify either complete theorem in that printed form.

**Verified (four of six selected claim groups, with restrictions):**

- **Fixed initial zero count.** `rlsLinear_runtimeSup_eq_harmonic` in [`RLSLinearExact.lean`](../ECRuntime/RLSLinearExact.lean): `E[T|Z₀=d]=n H_d` for strictly positive linear objectives.
- **Uniform random initial stake and binomial averaging.** `proposed_rlsLinear_uniformInitial_runtimeAverage` in [`RLSUniformInitialExact.lean`](../ECRuntime/RLSUniformInitialExact.lean), reduced to an exact finite harmonic identity by `proposed_rlsLinear_uniformInitial_runtimeFiniteCorrection` in [`RLSUniformInitialRuntimeFiniteCorrection.lean`](../ECRuntime/RLSUniformInitialRuntimeFiniteCorrection.lean).
- **First/second-order `log 2` behavior.** `proposed_rlsLinear_uniformStart_runtime_secondOrder` in [`RLSUniformInitialRuntimeSecondOrder.lean`](../ECRuntime/RLSUniformInitialRuntimeSecondOrder.lean), `proposed_rlsUniformInitial_harmonic_secondOrderCorrection` in [`RLSUniformInitialHarmonicSecondOrder.lean`](../ECRuntime/RLSUniformInitialHarmonicSecondOrder.lean), and `proposed_rlsLinear_uniformInitial_firstOrder_runtime` in [`RLSUniformFirstOrderRuntimeLaw.lean`](../ECRuntime/RLSUniformFirstOrderRuntimeLaw.lean).
- **Stronger finite approximation and a survival *upper bound*.** `proposed_rlsLinear_uniformInitial_logTwoFiniteRuntimeEnvelope` in [`RLSUniformInitialRuntimeLogTwoFiniteError.lean`](../ECRuntime/RLSUniformInitialRuntimeLogTwoFiniteError.lean) certifies `n(H_n-log 2) ≤ E[T_n] ≤ n(H_n-log 2)+n 2^(-n)`. `proposed_rlsLinear_uniformInitial_couponSurvivalCapped` in [`RLSUniformInitialCouponSurvivalCapped.lean`](../ECRuntime/RLSUniformInitialCouponSurvivalCapped.lean) adds a finite-time bound; it does **not** give the exact distribution.

**Missing or only partially matched:** (a) the precise parity-adjusted `-1/2+o(1)` result of paper **Theorem 1**; (b) its extension to **every strictly monotone objective** in **Theorem 2**, since the current uniform-start equalities assume *positive linear weights*. **Additional certified distributional theorem (Stage 166):**
`proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion` in
[`RLSUniformInitialCouponSurvivalInclusionExclusion.lean`](../ECRuntime/RLSUniformInitialCouponSurvivalInclusionExclusion.lean)
proves the **exact finite-time survival formula** under positive weights,
uniform initial state and one-bit mutation:
`Σ_{j=1}^n (-1)^(j+1) binom(n,j) 2^(-j) (1-j/n)^t`.
The complete public proof, concrete one-bit witness and strict axiom checks
passed the Round 55 gate. This is a *new distributional strengthening* in
the source's setting, **not** a claim that an otherwise missing numbered
theorem of the cited paper was thereby proved. **Coverage of selected
original-paper claims remains ~65%; neither original headline theorem has
been reproduced in full.**

### P03 — He and Yao (2001): additive drift

**Verified:** finite absorbing-chain additive-drift super-solution and hitting-time upper bounds, notably `additiveDrift_superSolution`, `additiveDrift_finiteHorizonBound`, `additiveDrift_runtimeSup_le` in [`AdditiveDrift.lean`](../ECRuntime/AdditiveDrift.lean) and `runtimeSup_le_of_superSolution` in [`UnrestrictedRuntime.lean`](../ECRuntime/UnrestrictedRuntime.lean). These realize an **upper-drift certificate in the repository's finite-state Markov setting**, not the paper's entire EA model.

**Not established:** the full lower-drift/polynomial–exponential dichotomy as presented for the paper's broader random sequences, population/crossover setting, and all examples. These are different obligations from an additive upper certificate. **Coverage: ~20% (roughly one of five main families).** Do not attach a specific paper theorem number without checking the version-specific original text.

### P04 — Doerr, Johannsen and Winzen (2012): multiplicative drift

**Source numbering:** **Theorem 3 (Multiplicative Drift)** in the accessible arXiv version, with upper bound `(1+log(s₀/s_min))/δ`.

**Verified:** `multiplicativeDrift_runtimeSup_le`, `multiplicativeDrift_finiteHorizonBound`, `multiplicativeDrift_superSolution` in [`MultiplicativeDrift.lean`](../ECRuntime/MultiplicativeDrift.lean), corresponding to the **finite-state specialization** of paper Theorem 3. The repository also proves positive-linear `O(n log n)` upper consequences under its concrete mutation hypotheses, e.g. [`WittStandardRuntimeAsymptotics.lean`](../ECRuntime/WittStandardRuntimeAsymptotics.lean); this is not a separate mechanization of all the paper's original linear-function analysis.

**Missing:** published constant-optimized `(1.39+o(1))e n log n` argument in its own parameterization, matching lower bounds, and minimum-spanning-tree/shortest-path/Euler-tour applications; general-process scope has not been checked for equivalence. **Coverage: ~30%.**

### P05 — Lehre and Witt (2014): general drift analysis with tails

**Verified-related specializations:** `multiplicativeDrift_firstHittingTime_tailMass_le` in [`MultiplicativeDriftTail.lean`](../ECRuntime/MultiplicativeDriftTail.lean), plus finite-state additive and multiplicative expectation bounds. These give a **special-case tail/expectation interface related to** the later general variable-drift framework; they do not by themselves establish the paper's general theorem.

**Missing:** the general variable-drift expectation and both-sided tail theorem with its full filtration/overshoot conditions; the specific sharp-concentration applications to the (1+1) EA, linear functions, LeadingOnes and permutations. **Coverage: ~15% (specialization only).** No publication theorem number is asserted here.

### P06 — Benjamin Doerr (2019): stochastic domination

**Verified:** product-coupling and geometric-waiting domination, including `stochasticallyDominated_by_geometricWaitingSum_of_coupling` and `natTailDominated_by_geometricWaitingSum_of_coupling` in [`CouplingDomination.lean`](../ECRuntime/CouplingDomination.lean); `oneMaxUnary_hittingTime_stochasticDomination` in [`OneMaxUnaryStochasticDomination.lean`](../ECRuntime/OneMaxUnaryStochasticDomination.lean); supporting tail and fitness-level results in [`LevelExitDomination.lean`](../ECRuntime/LevelExitDomination.lean) and [`StochasticDomination.lean`](../ECRuntime/StochasticDomination.lean).

**Missing:** universal `(μ,p)`-algorithm comparison under the full paper assumptions, fastest unbiased LeadingOnes operators, Chernoff-type tail bounds for sums of coupon-collector runtimes, and the other paper-wide distributional examples. **Coverage: ~35% (selected families).** No unverified paper theorem number is assigned; the precise Lean declarations above are the anchors.

### P07 — Buzdalov, Doerr, Doerr and Vinokurov (2020/2022): fixed target

**Source numbering checked against arXiv v3:** **Lemma 3** states the exact binomial/harmonic average `2^{-n} Σ_k binom(n,k) H_k = H_n - Σ_{j=1}^n 1/(j 2^j)`. **Theorem 4** gives full LeadingOnes fixed-target formulas for several algorithms; **Theorem 5** gives OneMax fixed-target bounds for a broader family of mutation operators.

**Verified matches:**

- **Paper Lemma 3, exact equality:** `proposed_binomialHarmonicAverage_closedForm` in [`BinomialHarmonicAverageClosedForm.lean`](../ECRuntime/BinomialHarmonicAverageClosedForm.lean); the one-step recurrence is `proposed_binomialHarmonicAverage_oneStep` in [`BinomialHarmonicAverageOneStep.lean`](../ECRuntime/BinomialHarmonicAverageOneStep.lean).
- **Paper Theorem 5, one-bit RLS subcase:** `rlsLinear_fixedTarget_runtimeSup_eq` in [`RLSFixedTarget.lean`](../ECRuntime/RLSFixedTarget.lean) proves `n(H_d-H_r)` from `d` zero bits to `r`; the paper covers additional rates/algorithms and initializations, not claimed here.
- **Paper Theorem 4, full-target (`k=n`) fixed-rate LeadingOnes subcase:** `leadingOnesUniformFirstHittingTimeExpectation_eq_formula` in [`LeadingOnesOccupationTotalClosure.lean`](../ECRuntime/LeadingOnesOccupationTotalClosure.lean). This does not prove its formula for *each intermediate target* and all listed algorithms.

**Missing:** the general fixed-target fitness-level statements and other applications/variants in their paper, including mutation-operator and multi-individual cases. **Coverage: ~30%; the Lemma 3 claim is fully certified, but paper Theorems 4 and 5 only in specified cases.**

### P08 — Jansen and Zarges (2014): fixed-budget analysis

**Verified overlap:** `rlsLinear_fixedBudget_expectedZeros_eq` in [`RLSFixedBudget.lean`](../ECRuntime/RLSFixedBudget.lean) proves `E[Z_t|Z₀=d]=d(1-1/n)^t` for one-bit RLS on positive linear functions; `proposed_rlsLinear_uniformInitial_fixedBudgetExpectedZeros` in [`RLSUniformInitialFixedBudgetMean.lean`](../ECRuntime/RLSUniformInitialFixedBudgetMean.lean) specializes uniform initialization. These are explicit **OneMax/RLS-type fixed-budget results** matching the theme, not a proof of every statement in the paper.

**Missing:** fixed-budget analysis for the paper's other algorithms and test functions (including (1+1) EA, LeadingOnes, Jump and Ridge), its general lower bounds and regime comparisons. **Coverage: ~20%.** Publication theorem numbering for the matched finite-budget case was not verified.

### P09 — Doerr, Le, Makhmara and Nguyen (2017): Fast Genetic Algorithms

**Source numbering:** **Theorem 1** (arXiv v2) gives two-sided bounds on the *full* `(1+1)` EA optimization time of Jump, using the plateau-escape term as a dominant component.

**Verified supporting part, not the theorem in full:** `jump_plateau_oneStepSuccessMass`, `jump_plateau_runtimeSup_eq_geometricMean`, `jump_plateau_runtimeTail_eq_geometric` in [`JumpPlateauEscape.lean`](../ECRuntime/JumpPlateauEscape.lean), and `candidateJumpEscape_fixedRate_optimal` in [`JumpEscapeOptimalRate.lean`](../ECRuntime/JumpEscapeOptimalRate.lean), proving the conditional plateau-escape probability, geometric waiting and optimal fixed escape probability. **This is not a certified full-runtime version of paper Theorem 1.**

**Missing:** time to reach the plateau, the corresponding global upper/lower bounds, heavy-tailed mutation runtime for Jump, sensitivity lower bounds, and graph-optimization applications. **Coverage: ~20%.**

### P10 — Carsten Witt (2013): tight linear-function optimization

**Verified:** standard mutation rate `p=1/n` sharp upper envelope and linear correction, including `wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n` and `wittStandard_runtimeSup_le_asymptotic_upperBound` in [`WittStandardRuntimeAsymptotics.lean`](../ECRuntime/WittStandardRuntimeAsymptotics.lean); exponential-tail machinery in [`WittStandardRuntimeTail.lean`](../ECRuntime/WittStandardRuntimeTail.lean); restricted fixed-scale `p=c/n` upper and tail bounds for `0<c≤log 3` in [`WittMutationLogThreeRuntime.lean`](../ECRuntime/WittMutationLogThreeRuntime.lean).

**Scope restriction:** theorem statements must be read with their **weight-ordering/positivity** and dimension hypotheses. These results are not automatically the paper's unrestricted uniform-in-weights assertion. **Missing:** matching lower bounds (including universal `e n log n` lower bounds), all mutation-rate regimes, universal optimality across all mutation-based algorithms, and the full sharp tail conclusions. **Coverage: ~35%.**

### P11 — Doerr, Janett and Lengler (2024): static unary unbiased mutation

**Source-paper support, not its main theorem:** `coordinateFlipMass_eq_meanRadius_div` in [`StaticUnaryUnbiasedFlipMarginals.lean`](../ECRuntime/StaticUnaryUnbiasedFlipMarginals.lean) is explicitly marked as the paper's **Lemma 2** (uniform coordinate-flip marginal), within the repository's Hamming-radius-invariant mutation model. Further certified supporting results: `correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments` in [`StaticUnaryUnbiasedSharpMomentUpper.lean`](../ECRuntime/StaticUnaryUnbiasedSharpMomentUpper.lean) and restricted results in [`StaticUnaryUnbiasedCorrectedRuntime.lean`](../ECRuntime/StaticUnaryUnbiasedCorrectedRuntime.lean), [`StaticUnaryUnbiasedLinearAcceptedEvents.lean`](../ECRuntime/StaticUnaryUnbiasedLinearAcceptedEvents.lean).

**CRITICAL NONCOVERAGE:** neither unrestricted general-linear sharp upper nor lower runtime theorem is formally proved. A mean mutation radius alone does not resolve the accepted-event size-bias/second-factorial-moment gap. **Coverage: ~15% of selected supporting/partial clusters; 0 of 2 unrestricted headline upper/lower claims.**

### P12 — Droste, Jansen and Wegener (2002): early (1+1) EA analysis

**Verified mathematical overlap, not a recreated original proof:** the positive-linear `O(n log n)` statement at `p=1/n` follows from the stronger standard-rate certificate in [`WittStandardRuntimeAsymptotics.lean`](../ECRuntime/WittStandardRuntimeAsymptotics.lean), together with its finite upper bound and asymptotic regime. This is a *derived and overlapping* implication; the original paper uses different techniques.

**Missing:** necessity/large-rate counterexamples, exponential-time hard nonlinear examples, hierarchy results, and all original case-specific methods. **Coverage: ~15%.** Not an independently reconstructed source-theorem proof or an additional promoted Lean stage.

## Certified results not attributed to one specific paper

The following reusable theorems are certified but are not assigned artificial paper-level coverage percentages: [`FiniteTrajectory.lean`](../ECRuntime/FiniteTrajectory.lean), [`HittingTime.lean`](../ECRuntime/HittingTime.lean), [`BellmanFiniteExactRuntime.lean`](../ECRuntime/BellmanFiniteExactRuntime.lean), [`FiniteRuntimeSurvivalSupport.lean`](../ECRuntime/FiniteRuntimeSurvivalSupport.lean), [`UniformMutationExact.lean`](../ECRuntime/UniformMutationExact.lean), [`StochasticDomination.lean`](../ECRuntime/StochasticDomination.lean), and the foundational bitstring, transition and first-entry interfaces. Some are useful **new specializations or stronger statements**, not verbatim theorems from any one cited paper.

## Full coverage / remaining research frontier

**Source papers with 100% audited coverage: none (0).** In particular, a proof of P01's optimal *fixed* rate does not cover adaptive rates; P02's `-log 2` finite-mean result does not supply its parity-sensitive `-1/2` expansion or the full monotone-function hypothesis; P09's plateau escape is not total Jump runtime; and P11 has no unrestricted headline theorem.

Priority research pathways are maintained in [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md). At the present checkpoint: parity-corrected P02 `-1/2` refinement; adaptive P01 policy; broader fixed-target/fixed-budget and stochastic domination; and the separate Witt/DJL open frontier. A future editor should update this catalogue **only after** a compiler-gated theorem promotion *and* a fresh source-paper scope comparison.

## Source and audit links

- Full verified local import graph: [`../ECRuntime.lean`](../ECRuntime.lean). Compiler gate and axiom checker: [`../scripts/verify.ps1`](../scripts/verify.ps1), [`../scripts/audit.lean`](../scripts/audit.lean).
- Specific source numbers checked from **P02**: [Doerr–Doerr, arXiv:1308.6384, Theorems 1–2](https://arxiv.org/pdf/1308.6384); **P04**: [Doerr–Johannsen–Winzen, arXiv:1101.0776, Theorem 3](https://arxiv.org/pdf/1101.0776); **P07**: [Buzdalov et al., arXiv:2004.09613, Lemma 3 and Theorems 4–5](https://arxiv.org/pdf/2004.09613); **P09**: [Fast Genetic Algorithms, arXiv:1703.03334, Theorem 1](https://arxiv.org/pdf/1703.03334).
- Other publication links appear in the overview. This is an evidence-oriented, deliberately conservative source mapping. In particular, **the absence of an independently verified paper theorem number is not repaired by inventing one**.
