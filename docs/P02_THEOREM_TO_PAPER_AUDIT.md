# P02: coupon/RLS theorem-to-paper audit

**Current certified baseline:** 547 public Lean modules (25 October 2026).
This document distinguishes two **different** Doerr–Doerr publications; the
coverage estimates and complete per-paper inventories are in
[`VERIFIED_PAPERS.md`](VERIFIED_PAPERS.md).

## Source identities

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

## P02a — nearly complete headline coverage (~95%)

| Original claim | Current certification | Lean entry point |
|---|---|---|
| Coupon theorem: random-stake exact/centered mean and `-1/2` asymptotic correction | **Verified** | [`RandomStakeCouponFinitePaperCenteredExact.lean`](../ECRuntime/RandomStakeCouponFinitePaperCenteredExact.lean); [`RandomStakeCouponSharpPaperCentered.lean`](../ECRuntime/RandomStakeCouponSharpPaperCentered.lean) |
| RLS theorem: strictly monotone fitness under uniform initial point, including even/odd dimensions | **Verified** under the declared coordinate-strict-monotonicity assumption | [`RLSAllDimensionPaperCenteredExact.lean`](../ECRuntime/RLSAllDimensionPaperCenteredExact.lean); [`RLSAllDimensionPaperSharpCentered.lean`](../ECRuntime/RLSAllDimensionPaperSharpCentered.lean) |
| Direct coupon/RLS statewise, finite-time, and expected-runtime law correspondence | **Verified**, beyond the two headline means | [`RandomStakeCouponStatewiseSurvivalCorrespondence.lean`](../ECRuntime/RandomStakeCouponStatewiseSurvivalCorrespondence.lean); [`RandomStakeCouponArbitraryTargetRuntime.lean`](../ECRuntime/RandomStakeCouponArbitraryTargetRuntime.lean) |
| Exact binomial/harmonic identity and arbitrary nonnegative weighted expectations | **Verified** | [`BinomialHarmonicAverageClosedForm.lean`](../ECRuntime/BinomialHarmonicAverageClosedForm.lean); [`CouponInfiniteWeightedSurvival.lean`](../ECRuntime/CouponInfiniteWeightedSurvival.lean) |
| Every auxiliary paper inequality and finite-error convention, with a literal statement-by-statement formal manuscript audit | **Not asserted** | Requires checking the exact source version, conventions and all supporting propositions |

The centered result is expressed for even and odd dimensions; the odd-
`n/2` harmonic convention is an average of its adjacent integer harmonic
numbers. The Lean theorem addresses the claimed `-1/2` correction rather
than just the leading `n log n` term. As with all paper mappings, the
stochastic kernel, definition of time and initial distribution matter.

## P02b — RLS/OneMax subfamily, not the full paper (~25%)

**Verified:** the RLS/OneMax exact centered correction and associated
coupon/RLS survival/expectation identities, through the same certified
modules used for P02a.

**Not verified:** the separate `(1+1)`-EA/OneMax comparison; the
RLS/LeadingOnes and `(1+1)`-EA/LeadingOnes initialization discrepancies;
the latter paper's precise level-zero/one exit-time reduction; the full
four-combination theorem and its source-specific additive constants.
A formal adaptive LeadingOnes runtime formula from P01 does **not** itself
establish an initialization-discrepancy theorem for P02b.

## Audit policy

This is a **claim-level mathematical audit**, not a count of promoted files.
A result is counted as a full paper counterpart only if its public Lean
statement covers the relevant hypothesis class and conclusion. Supporting
lemmas and special cases are shown separately. The complete list of verified
and missing headline families, including all other literature targets, is in
[`VERIFIED_PAPERS.md`](VERIFIED_PAPERS.md).
