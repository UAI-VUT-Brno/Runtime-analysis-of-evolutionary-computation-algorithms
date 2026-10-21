# Formalized results and research status

This document indexes the main formalized results, relates them to the
original research literature, and distinguishes the completed
superincreasing-function proof from the unfinished Doerr--Janett--Lengler
(2024) general-linear program.

The finite-horizon and unrestricted superincreasing-runtime modules are
imported by the public root. The combined Stage 106 root and non-vacuity
regressions passed strict Lean verification on 21 October 2026; the
hypotheses in the Lean theorem declarations remain authoritative.
The repository does **not** prove the headline asymptotic general-linear
upper and lower bounds of Doerr--Janett--Lengler.

## 1. Mathematical setting and result scope

The project works primarily with pseudo-Boolean search spaces `BitString n`,
mutation-generated finite-state Markov kernels and hitting times of target
sets. Expectations are expressed using finite-horizon recurrences, the
supremum of those recurrences (`runtimeSup`), and integral representations
of the sample-path first-hitting time.

The word **formalized** below means that Lean accepted the corresponding
proof in the pinned environment, *with the qualifications of its Lean
statement*. It does **not** mean that all results of the cited paper have
been formalized, nor that every classical asymptotic statement is present.

## 2. Main proven theorem families and literature connections

| Formalized result | Representative Lean entrypoints | Related source paper |
| --- | --- | --- |
| Stochastic transitions, trajectory measures, finite/infinite hitting-time semantics, occupation and stochastic-domination infrastructure | [`ECRuntime/TransitionKernel.lean`](../ECRuntime/TransitionKernel.lean), [`FiniteTrajectory.lean`](../ECRuntime/FiniteTrajectory.lean), [`UnrestrictedRuntime.lean`](../ECRuntime/UnrestrictedRuntime.lean), [`TrajectoryFirstHittingTime.lean`](../ECRuntime/TrajectoryFirstHittingTime.lean), [`StochasticDomination.lean`](../ECRuntime/StochasticDomination.lean) | [He & Yao (2001), *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*](https://doi.org/10.1016/S0004-3702(01)00058-3); [Doerr (2019), *Analyzing Randomized Search Heuristics via Stochastic Domination*](https://doi.org/10.1016/j.tcs.2018.09.024) |
| Additive and multiplicative drift inequalities, runtime super-solutions and finite-horizon bounds | [`ECRuntime/AdditiveDrift.lean`](../ECRuntime/AdditiveDrift.lean), [`MultiplicativeDrift.lean`](../ECRuntime/MultiplicativeDrift.lean) | [He & Yao (2001)](https://doi.org/10.1016/S0004-3702(01)00058-3); [Doerr, Johannsen & Winzen (2012), *Multiplicative Drift Analysis*](https://doi.org/10.1007/s00453-012-9622-x) |
| Fitness-level, geometric waiting-time and stochastic-domination methods | [`ECRuntime/FitnessLevel.lean`](../ECRuntime/FitnessLevel.lean), [`GeometricRuntime.lean`](../ECRuntime/GeometricRuntime.lean), [`GeometricTail.lean`](../ECRuntime/GeometricTail.lean), [`LevelExitDomination.lean`](../ECRuntime/LevelExitDomination.lean) | [Doerr (2019)](https://doi.org/10.1016/j.tcs.2018.09.024) |
| Exact uniformly initialized `(1+1)` EA **LeadingOnes** expected runtime for arbitrary fixed `0 < p < 1`, including standard and scaled mutation-rate corollaries | `leadingOnesUniformFirstHittingTimeExpectation_eq_formula` in [`ECRuntime/LeadingOnesOccupationTotalClosure.lean`](../ECRuntime/LeadingOnesOccupationTotalClosure.lean); [`ECRuntime/LeadingOnesMainResults.lean`](../ECRuntime/LeadingOnesMainResults.lean) | [Böttcher, Doerr & Neumann (2010), *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*](https://doi.org/10.1007/978-3-642-15844-5_1). The exact-runtime formula is formalized; this does not certify every optimization result in the paper. |
| Positive linear objectives: a **standard-rate upper bound** with leading envelope `e n log n + O(n)` for the explicitly constrained weight and dimension regime; mutation rate `p=c/n` on the certified interval `0 < c <= log 3`, with auxiliary tail bounds | `wittStandard_runtimeSup_le_asymptotic_upperBound` in [`ECRuntime/WittStandardRuntimeAsymptotics.lean`](../ECRuntime/WittStandardRuntimeAsymptotics.lean); `wittMutation_runtimeSup_le_logThreeScale_log_bound` in [`ECRuntime/WittMutationLogThreeRuntime.lean`](../ECRuntime/WittMutationLogThreeRuntime.lean) | [Witt (2013), *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*](https://doi.org/10.1017/S0963548312000600). These are upper-bound branches, not the whole paper's matched upper/lower theory. |
| Static unary-unbiased mutation distribution laws; singleton and coordinate-marginal probabilities, pair-event and moment formulas; accepted-pivot and potential/difference inequalities | [`ECRuntime/StaticUnaryUnbiasedMutation.lean`](../ECRuntime/StaticUnaryUnbiasedMutation.lean) and `ECRuntime/StaticUnaryUnbiased*` modules, especially [`StaticUnaryUnbiasedMomentFamilies.lean`](../ECRuntime/StaticUnaryUnbiasedMomentFamilies.lean), [`StaticUnaryUnbiasedCorrectedRuntime.lean`](../ECRuntime/StaticUnaryUnbiasedCorrectedRuntime.lean) | Motivated by [Doerr, Janett & Lengler (2024), *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*](https://doi.org/10.1007/s00453-024-01258-9). These are supporting lemmas, not the general-linear conclusion. |
| Superincreasing/BinVal-specialized exact first-zero exit, renewal, occupation and visitation identities | [`ECRuntime/StaticUnaryUnbiasedFirstZeroResidence.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroResidence.lean), [`ECRuntime/StaticUnaryUnbiasedFirstZeroOccupationRenewal.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroOccupationRenewal.lean), [`ECRuntime/StaticUnaryUnbiasedFirstZeroWeightedVisits.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroWeightedVisits.lean), [`ECRuntime/StaticUnaryUnbiasedFirstZeroPathVisits.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroPathVisits.lean) | Restricted proof route motivated by [Doerr, Janett & Lengler (2024)](https://doi.org/10.1007/s00453-024-01258-9); not itself a theorem for arbitrary linear functions. |
| Superincreasing/BinVal **finite-horizon** expected hitting time and hazard-weighted visitation upper bounds | `firstZeroFiniteRuntimeMass_eq_hittingRuntime`, `firstZeroFiniteRuntimeMass_le_hazardCap` in [`ECRuntime/StaticUnaryUnbiasedFirstZeroFiniteRuntime.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroFiniteRuntime.lean) | Restricted consequence of the static unary-unbiased model; connection to [Doerr, Janett & Lengler (2024)](https://doi.org/10.1007/s00453-024-01258-9). |
| **Unrestricted** expected first-hitting time, finiteness and hazard-cap bound for superincreasing weights and positive singleton mutation mass | `firstZeroRuntimeSup_le_hazardCap`, `firstZeroFirstHittingTime_lintegral_le_hazardCap`, `firstZeroFirstHittingTime_lintegral_ne_top` in [`ECRuntime/StaticUnaryUnbiasedFirstZeroUnrestrictedRuntime.lean`](../ECRuntime/StaticUnaryUnbiasedFirstZeroUnrestrictedRuntime.lean) | Specialized extension of the prior chain; related to [Doerr, Janett & Lengler (2024)](https://doi.org/10.1007/s00453-024-01258-9). **Included in the public root and strictly compiler-verified after integration.** |

### Exact interpretation of the latest bounds

For superincreasing positive linear weights, a static unary-unbiased
mutation law with **positive one-bit mass** `p_1 > 0`, and a first-zero level
`L_i`, let `q_i` be the exact probability of the corresponding lowest-index
mutation event (in Lean, `law.maskEventMass (lowestMaskEvent i)`). The
finite-runtime chain proves a finite-horizon bound of the form

\[
  \mathbb E_x[\min(\tau,T)]
   \;\le\; \sum_{i=0}^{n-1}
        \frac{\Pr_x(\text{visit }L_i\text{ by }T)}{q_i}
   \;\le\;\sum_{i=0}^{n-1}\frac{1}{q_i}.
\]

The unrestricted-runtime module then identifies the supremum of these finite
expectations with the sample-path hitting-time expectation and verifies the corresponding
unrestricted bound and finiteness. The exact endpoint formula is stated in
`ENNReal` in Lean. In this model, the level-exit hazard is related to the
singleton mass, yielding the familiar `n/p_1` bound per level when needed.
Neither the hazard sum nor the proof transfers automatically to arbitrary
positive linear weights: monotone first-zero progress depends essentially
on superincreasing weights.

## 3. What the repository does *not* establish

The main theorem of [Doerr, Janett & Lengler (2024)](https://doi.org/10.1007/s00453-024-01258-9)
concerns sharp `(1+o(1)) n ln(n)/p_1`-type behavior for **general positive
linear functions** under specific lower bounds on singleton probability and
a bounded mean mutation radius. Its matching lower bound is logically
independent from its upper-bound argument.

The repository does **not** yet contain:

1. The sharp asymptotic *upper bound* for every positive linear objective
   under the original bounded-**first**-moment assumptions.
2. The matching general-linear *lower bound* under the paper's stated
   hypotheses, including the necessary initialization and uniformity claims.
3. A complete proof that the specialized first-zero/BinVal argument extends
   to general linear weights.

The conditional, higher-moment variants already formalized are not a
substitute for (1). Do not cite their existence as proof of the full theorem.

## 4. Why a different Doerr--Janett--Lengler proof strategy is needed

The central challenge is a **size-biased conditioning issue** in a proposed
way to control multi-bit mutations. For a static unary-unbiased operator, let
`K` be the sampled mutation radius (number of flipped coordinates), and let
`i` be a fixed coordinate. Uniform choice of `K`-subsets gives

\[
  \Pr(i\text{ flipped}\mid K=k)=\frac{k}{n},\qquad
  \mathbb E[K-1\mid i\text{ flipped}]
      =\frac{\mathbb E[K(K-1)]}{\mathbb E[K]}
\]

whenever the denominator is positive. Therefore merely assuming
`E[K] <= C` **does not** bound the expected number of other flips
conditional on flipping a specific coordinate.

For example, let `K=n` with probability `1/n`, and `K=1` otherwise. Then
`E[K] < 2`, but `E[K(K-1)] = n-1`, so the conditional expectation above
is of order `n`. This refutes a *generic inference from a bounded first
moment to a bounded size-biased conditional tail*; it does not, by itself,
refute the published overall runtime theorem. The repository's proof audit
flagged this conditioning step as requiring a new argument or more careful
hypotheses. We do not claim a new counterexample to the paper's main result.

### A plausible completion route (research plan, **not** a proof)

1. **General-linear upper bound, bounded mean only.** Split short and
   long-radius accepted events by a carefully chosen truncation threshold.
   Use the existing exact singleton gain and accepted-event decomposition
   for short steps. Control long steps through an amortized potential or
   temporal occupation argument using the *unconditional* bound on
   `E[K]`, rather than replacing it by a nonexistent conditional bound.
2. **Alternative upper route.** Use weight blocks and an adaptive potential
   to charge rare accepted long-radius excursions across multiple
   iterations. Show the leading coefficient depends on `p_1` and that all
   error terms are `o(n log n/p_1)` under the paper's actual hypotheses.
3. **Matching lower bound.** Develop an independent level/visitation
   argument robust to multi-bit flips and starting configurations. The
   standard OneMax stochastic-domination reduction cannot simply be copied
   for arbitrary static unbiased operators. Establish uniform estimates,
   initialization effects, and the asymptotic matching coefficient.
4. **Assembly.** Verify all limit exchanges, uniformity statements, and
   coupling/drift prerequisites in Lean *before* asserting the sharp general
   theorem. Maintain separate upper and lower proof obligations.

The formalized superincreasing analysis provides rigorous occupation and
visit-counting tools for a restricted case, but its no-return property is
precisely what fails to be automatic on arbitrary linear objectives. It is
therefore a supporting demonstration, **not** the missing general-linear
amortization lemma.

## 5. Reproducibility and proof-status notes

- Both finite- and unrestricted-horizon superincreasing modules are imported
  by `ECRuntime.lean`; their non-vacuity examples are included in
  `ECRuntimeTest.lean`. To verify the **exact published checkout**, run
  `bash scripts/verify_release.sh`. The verifier checks the integrated
  root, the tests, and proof hygiene in Lean 4.32.1 with Mathlib v4.32.1.
- The unrestricted module was first verified in isolation and then passed
  strict integrated-root verification (21 October 2026). Checks of isolated
  modules must not be confused with certification of a later changed checkout;
  rely on the strict result archive produced from the exact release source.
- Historical `StatementPins` and stage-specific `AxiomAudit` files were
  deliberately omitted from the public repository. The generic
  compiled-environment audit and non-vacuity examples remain; frozen
  theorem-interface comparisons are **not** performed.
- Bibliographic links attribute the original results and motivation, not
  a claim that every theorem from any cited paper has been formalized.
