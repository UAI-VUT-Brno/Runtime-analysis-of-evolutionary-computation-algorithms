---
paper: doerr-doerr-2013
aliases: [P02a]
---

# P02a — Doerr and Doerr (2013): random-initial-stake coupon collector (~95%)

**Verified headline results**

1. **Paper Theorem 1: sharp randomly initialized coupon-collector mean.**
   [`proposed_randomStakeCoupon_allDimensionPaperSharpCentered`](../../../ECRuntime/RandomStakeCouponSharpPaperCentered.lean)
   gives the all-dimension centered `-1/2` limit;
   [`proposed_randomStakeCoupon_finitePaperCenteredExact`](../../../ECRuntime/RandomStakeCouponFinitePaperCenteredExact.lean)
   gives the finite centered identity.
2. **Paper Theorem 2: random-initial RLS on strictly monotone Boolean
   fitness.**
   [`proposed_strictMonotoneRLS_allDimensionPaperSharpCentered`](../../../ECRuntime/RLSAllDimensionPaperSharpCentered.lean)
   proves the odd/even-compatible `n H_{n/2} - 1/2 + o(1)` expansion,
   and [`proposed_strictMonotoneRLS_allDimensionPaperCentered_exact`](../../../ECRuntime/RLSAllDimensionPaperCenteredExact.lean)
   gives the exact centered finite formula under the Lean monotonicity
   hypothesis.
3. **Coupon/RLS process identification, including targets and laws.**
   [`proposed_couponProcess_statewiseSurvival_eq_strictMonotoneRLS`](../../../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean),
   [`proposed_couponProcess_arbitraryTarget_runtimeSup_eq_strictMonotoneRLS`](../../../ECRuntime/RandomStakeCouponArbitraryTargetRuntime.lean),
   and [`proposed_couponProcess_arbitraryTarget_survival_eq_strictMonotoneRLS`](../../../ECRuntime/RandomStakeCouponArbitraryTargetFiniteHorizon.lean)
   make the comparison direct, not merely an informal consequence.
4. **Finite harmonic/binomial correction and higher observable transfers.**
   [`proposed_binomialHarmonicAverage_closedForm`](../../../ECRuntime/BinomialHarmonicAverageClosedForm.lean)
   and [`proposed_couponProcess_arbitraryTarget_weightedSurvival_eq_strictMonotoneRLS`](../../../ECRuntime/RandomStakeCouponWeightedSurvivalTransfer.lean)
   certify exact identities; additional higher-moment and infinite-weighted
   transfers appear in
   [`CouponArbitraryPositiveMomentFiniteMass.lean`](../../../ECRuntime/CouponArbitraryPositiveMomentFiniteMass.lean)
   and [`CouponInfiniteWeightedSurvival.lean`](../../../ECRuntime/CouponInfiniteWeightedSurvival.lean).

**Not yet verified / not asserted**

- Exhaustive **one-to-one matching of every auxiliary inequality and proof
  detail** in the six-page source, including its exact error-bound conventions.
  Both main numbered theorems have certified counterparts, but 95% is a
  *headline-claim estimate*, not a guarantee that every auxiliary proposition
  has been formalized.
- Any extension of the source's RLS theorem to **arbitrary fitness functions
  without coordinate monotonicity**, or to a different mutation operator;
  these would be new hypotheses/results, not missing cases of Theorem 2.

## P02: coupon/RLS theorem-to-paper audit

**Current certified baseline:** 547 public Lean modules (25 October 2026).
This document distinguishes two **different** Doerr–Doerr publications; the
coverage estimates and complete per-paper inventories are in
[the coverage table](../README.md#paper-by-paper-coverage).

### Source identities

- **P02a (2013):** Benjamin Doerr and Carola Doerr,
  [*Collecting Coupons with Random Initial Stake*](https://arxiv.org/abs/1308.6384),
  six-page preprint. Its headline **Theorem 1** analyzes the coupon collector
  with an independently, uniformly random initial coupon set. **Theorem 2**
  applies the sharp correction to RLS on monotone Boolean fitness functions.
- **P02b (2016):** Benjamin Doerr and Carola Doerr,
  [*The Impact of Random Initialization on the Runtime of Randomized Search
  Heuristics*](https://doi.org/10.1007/s00453-015-0019-5),
  *Algorithmica* 75, 529–553. This article compares uniform initialization
  with starting from average fitness for **RLS and the `(1+1)` EA**, on
  **OneMax and LeadingOnes**. It includes the RLS/OneMax sharp correction,
  but is broader than the 2013 preprint.

These publications must **not share one coverage percentage**. The associated
2014 conference precursor to P02b is also not a synonym for P02a.

### P02a — nearly complete headline coverage (~95%)

| Original claim | Current certification | Lean entry point |
|---|---|---|
| Coupon theorem: random-stake exact/centered mean and `-1/2` asymptotic correction | **Verified** | [`RandomStakeCouponFinitePaperCenteredExact.lean`](../../../ECRuntime/RandomStakeCouponFinitePaperCenteredExact.lean); [`RandomStakeCouponSharpPaperCentered.lean`](../../../ECRuntime/RandomStakeCouponSharpPaperCentered.lean) |
| RLS theorem: strictly monotone fitness under uniform initial point, including even/odd dimensions | **Verified** under the declared coordinate-strict-monotonicity assumption | [`RLSAllDimensionPaperCenteredExact.lean`](../../../ECRuntime/RLSAllDimensionPaperCenteredExact.lean); [`RLSAllDimensionPaperSharpCentered.lean`](../../../ECRuntime/RLSAllDimensionPaperSharpCentered.lean) |
| Direct coupon/RLS statewise, finite-time, and expected-runtime law correspondence | **Verified**, beyond the two headline means | [`RandomStakeCouponStatewiseSurvivalCorrespondence.lean`](../../../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean); [`RandomStakeCouponArbitraryTargetRuntime.lean`](../../../ECRuntime/RandomStakeCouponArbitraryTargetRuntime.lean) |
| Exact binomial/harmonic identity and arbitrary nonnegative weighted expectations | **Verified** | [`BinomialHarmonicAverageClosedForm.lean`](../../../ECRuntime/BinomialHarmonicAverageClosedForm.lean); [`CouponInfiniteWeightedSurvival.lean`](../../../ECRuntime/CouponInfiniteWeightedSurvival.lean) |
| Every auxiliary paper inequality and finite-error convention, with a literal statement-by-statement formal manuscript audit | **Not asserted** | Requires checking the exact source version, conventions and all supporting propositions |

The centered result is expressed for even and odd dimensions; the odd-
`n/2` harmonic convention is an average of its adjacent integer harmonic
numbers. The Lean theorem addresses the claimed `-1/2` correction rather
than just the leading `n log n` term. As with all paper mappings, the
stochastic kernel, definition of time and initial distribution matter.

### P02b — RLS/OneMax subfamily, not the full paper (~25%)

**Verified:** the RLS/OneMax exact centered correction and associated
coupon/RLS survival/expectation identities, through the same certified
modules used for P02a.

**Not verified:** the separate `(1+1)`-EA/OneMax comparison; the
RLS/LeadingOnes and `(1+1)`-EA/LeadingOnes initialization discrepancies;
the latter paper's precise level-zero/one exit-time reduction; the full
four-combination theorem and its source-specific additive constants.
A formal adaptive LeadingOnes runtime formula from P01 does **not** itself
establish an initialization-discrepancy theorem for P02b.

### Audit policy

This is a **claim-level mathematical audit**, not a count of promoted files.
A result is counted as a full paper counterpart only if its public Lean
statement covers the relevant hypothesis class and conclusion. Supporting
lemmas and special cases are shown separately. The complete list of verified
and missing headline families, including all other literature targets, is in
[the coverage table](../README.md#paper-by-paper-coverage).
