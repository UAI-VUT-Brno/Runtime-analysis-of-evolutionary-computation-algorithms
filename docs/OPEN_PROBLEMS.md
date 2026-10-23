# Research frontier and constructive proof strategies

**Certified checkpoint (23 October 2026):** the user-run Round 56
verification passed all eight gates *after* promotion and cleanup of the exact
Stage 166 finite survival distribution. Its concrete one-bit witness and
standard-axiom audit passed. **60 selected stages (107–166) are certified.**
There are no approved-open candidates. Future directions below are not yet
approved new Lean theorem statements.

This file lists **unfinished paper-level claims**, not tactics and Lean
elaboration tasks for completed claims. Iterations count one patch + user
Lean build + feedback cycle; estimates are planning ranges, not guarantees.

## A. Adaptive LeadingOnes: Bottcher--Doerr--Neumann (2010)

**Current certificate:** exact fixed-`p` mean, scaled-rate coefficient
`F(c)=(e^c-1)/(2c^2)`, and unique optimal fixed `c` in `(1,2)`.
**Paper-level gap:** exact fitness-dependent policy and its approximately `0.68 n^2`
asymptotic expected runtime/optimality; this is different from fixed-rate
optimization (approximately `0.77 n^2`).

### Proof path

1. Model a policy `p : Fin n -> Real` / rate as function of current
   LeadingOnes level. Prove that the upper-bit distribution at level entry
   retains the needed symmetry under the specified initialization and
   accepted moves; avoid an unjustified independence assertion.
2. Prove an exact *level-residence time* or occupation formula for each
   adaptive rate `p_i` using existing `LeadingOnesMainResults` and
   `StaticUnaryUnbiasedFirstZeroOccupationRenewal` infrastructure.
3. Minimize each level-specific reciprocal success probability over `p_i`;
   handle boundaries and uniqueness carefully. The minimizer will depend
   on the current level and the admissible rate interval.
4. Sum the optimal level costs. Derive the asymptotic constant with a
   quantified Riemann-sum / integral approximation, not numerical fitting.
5. Show a matching lower bound for *all* policies in the stated adaptive
   class, not just the candidate policy.

**Estimated 12--35 rounds**. First 3--6 rounds: formal level-residence
interface and proofs for small dimensions; stop and reassess if the
symmetry/invariance lemma fails.

## B. Random initial stake, Doerr--Doerr (2013)

**Current certificate:** exact binomial/harmonic expectation, `-log 2`
normalized correction, finite `n 2^(-n)` mean-error bound, capped geometric
survival upper bound.

### B1. Original finer expectation claim

The source abstract's precise result is, with its parity-adjusted definition
of `H_{n/2}`, `E[T_n] = n H_{n/2} - 1/2 +/- o(1)`. The current certified
`n(H_n-log 2) + O(n 2^(-n))` does **not literally state this claim**. A
plausible route is to prove

`n (H_n - log 2 - H_{n/2}) -> -1/2`, using even/odd harmonic-sum
asymptotics or a bounded Euler--Maclaurin/trapezoid remainder. Then use
the already certified finite error bound.

**Estimated 3--10 rounds**, conditional on the requisite Mathlib harmonic
remainder API and accurate handling of odd `n`.

### B2. Completed: exact finite survival distribution (Stage 166)

**Certified theorem:**
`ECRuntime.proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion`
in [`RLSUniformInitialCouponSurvivalInclusionExclusion.lean`](../ECRuntime/RLSUniformInitialCouponSurvivalInclusionExclusion.lean),
with the approved statement unchanged. For each `n>0`, strictly positive
weight vector and `t : Nat`, it states

`P(T_n>t) = Σ_(j=1)^n (-1)^(j+1) * choose(n,j) * 2^(-j) * (1-j/n)^t`.

**Proof mechanism:** finite joint-zero Markov eigenfunctions, a powerset
bijection for uniform-start counting, Boolean inclusion–exclusion,
finite-state survival transport and grouping subsets by cardinality.
No unjustified coordinate independence is assumed. Round 55 compiled the
public proof and concrete dimension-one regression witness through all
eight gates; transitive axioms are exactly the permitted standard axioms.
This completes the **finite distributional extension**, not the cited
paper's parity-adjusted mean claim or its general monotone-function
hypothesis. The subsequent limiting distribution below remains open.

### B3. Optional distributional extension beyond verified paper claims

Starting from the certified Stage 166 theorem, analyze `t ~= n(log(n/2)+x)` and asymptotic finite alternating
sums to obtain an appropriately centered coupon-collector limit law;
handle integer rounding and the law at continuity points. This is a
*separately scoped extension*, not presumed to be a theorem of the cited
paper without an explicit audit. **Estimated 10--25 additional rounds**.

## C. Drift, stochastic domination, fixed target and fixed budget

- He--Yao (2001): add the population and crossover model and test the
  polynomial/exponential drift conditions in the original applications.
  The current generic one-individual model is insufficient to claim full
  coverage. **15--40+ rounds** for even a selected comparable cluster.
- Multiplicative drift and stochastic domination: write an itemized
  statement-to-source map first; generalize only where current
  abstractions are insufficient. **8--25 rounds per family**.
- Fixed target/budget: develop hitting-time law and higher moments for
  algorithms beyond one-bit RLS, then tests on at least one different
  objective. **8--22 rounds per branch**.
- Jump and fast heavy-tailed mutation: prove progress to the plateau,
  combine via strong Markov/renewal with the plateau-escape law; do not
  conflate plateau-only time with total runtime. **12--30+ rounds**.

## D. Separate difficult frontier

- Witt (2013): unrestricted positive-linear mutation-rate regimes and
  matched lower bounds; intermediate `c<=log 3` already certified.
- Doerr--Janett--Lengler (2024): the general-linear headline theorem is
  **not** covered. An accepted-event conditional distribution size-biases
  the mutation radius, and the corresponding second factorial moment is
  not controlled by the mean alone. A new mathematically valid argument
  is required before pursuing Lean tactic repair.

These two are intentionally **excluded** from the main iteration totals.

## Sequencing, estimated iterations

| Priority | Next task | Remaining cycles |
|---|---|---:|
| 1 | Doerr--Doerr `-1/2` parity-adjusted mean expansion | 3--10 |
| 2 | Adaptive LeadingOnes level-residence and optimal policy | 12--35 |
| 3 | Optional centered completion-time limit distribution | 10--25 new rounds |
| 4 | Full Jump progress-plus-escape runtime | 12--30+ |

For all currently linked papers and approximate claim coverage, see
[VERIFIED_PAPERS.md](VERIFIED_PAPERS.md).

No fully covered source paper has yet been established by an exhaustive
claim-by-claim audit; certified central theorem families must not be
misidentified as complete-paper coverage.
