# ECRuntime: certified results, source-paper coverage and research frontier

**Verified checkpoint:** 23 October 2026, user-run Stage 130 Round 56.
**Verified environment:** Lean 4.32.1 and Mathlib v4.32.1.
**Evidence:** `stage130_round56_results.zip`: all eight official gates
passed *after* promotion cleanup, **60 selected stages (107–166)**,
**249 public Lean modules**, zero new hygiene warnings and no active approved
candidates. Stage 166's public exact survival theorem, axiom probe and
concrete one-bit witness compiled; the approved theorem signature is guarded.

**Consolidation catalogue:** For a whole-repository, paper-by-paper table of
exact Lean theorem names, checked original theorem numbers, caveats and
approximate coverage percentages, see **[VERIFIED_PAPERS.md](VERIFIED_PAPERS.md)**.
That catalogue is the authoritative source for a paper-level coverage claim.

## Status definitions and full-paper coverage

- **Certified theorem:** its stated Lean interface and proof were accepted by the user's Lean compiler. Its actual hypotheses and quantified scope matter.
- **Covered claim family:** specified main results of a source paper have Lean proofs under the documented matching assumptions; this does not mean every claim of the publication is mechanized.
- **Fully covered paper:** each relevant original theorem, technical assumption, substantial corollary, and application family has been audited against the paper and accounted for by equivalent Lean results. This is a *much stronger* standard than having its central mean-runtime theorem.

**Papers verified as fully covered: none.** No source paper in the maintained catalogue currently has a complete theorem-by-theorem correspondence audit. In particular, the two deepest completed *theorem families* are (i) fixed-rate LeadingOnes and its optimal asymptotic fixed rate, and (ii) expected runtime for uniformly initialized one-bit RLS on positive linear functions, including its finite log-two error and the separately certified exact survival distribution. Neither constitutes full paper coverage.

The percentage figures below, where given, are **rough coverage of a deliberately selected set of headline claim families**, not fractions of all formal results in the papers. They must not be cited as exact coverage of a publication.

## A. Paper-by-paper assessment

| Paper or closely connected result family | Important machine-checked statements (representative modules) | Claims or assumptions not yet covered | Paper fully covered? |
| --- | --- | --- | --- |
| [Bottcher, Doerr, Neumann (2010), *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*](https://doi.org/10.1007/978-3-642-15844-5_1) | Exact mean optimization time at fixed `p`; scaled `p=c/n` limit; existence/uniqueness and global optimality of fixed `c` (`LeadingOnesMainResults`, `LeadingOnesOptimalRate`, `LeadingOnesStationaryRootExists`, `LeadingOnesUniqueStationaryRoot`) | Exact expected time for fitness-dependent `p_i`, minimization over adaptive schedules, resulting approximately `0.68 n^2` constant; treatment of all paper variants | **No** (2/4 selected clusters) |
| [Doerr, Doerr (2013/2016), *Collecting Coupons with Random Initial Stake*](https://arxiv.org/abs/1308.6384) | Exact positive-linear RLS mean, binomial averaging, harmonic correction, `-log 2` normalized offset, exponentially accurate finite error, capped survival upper bound (`RLSUniformInitialExact`, `RLSUniformInitialRuntimeFiniteCorrection`, `RLSUniformInitialRuntimeLogTwoFiniteError`, `RLSUniformInitialCouponSurvivalCapped`) | The source's *finer* mean identity `n H_{n/2} - 1/2 +/- o(1)` in its parity-adjusted definition of `H_{n/2}`; full original monotone-function scope if different from positive linear; arbitrary random initial stakes and all paper variants. The exact finite survival distribution is a **certified extension**; a Gumbel-type limit remains a proposal. Neither is automatically a named claim of the source paper | **No** (central mean-runtime family strongly covered, not paper complete) |
| [He, Yao (2001), *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*](https://doi.org/10.1016/S0004-3702(01)00058-3) | Reusable finite-horizon hitting-time, additive-drift and expected-runtime results (`AdditiveDrift`, `Drift`, `UnrestrictedRuntime`) | Paper's population/crossover model, full polynomial-vs-exponential conditions and original problem examples | **No** |
| [Doerr, Johannsen, Winzen (2012), multiplicative drift](https://doi.org/10.1007/s00453-012-9622-x) | Multiplicative drift expectation and tail framework (`MultiplicativeDrift`, `MultiplicativeDriftTail`) | Match each theorem variant and all original applications | **No** |
| [Doerr (2019), stochastic domination](https://doi.org/10.1016/j.tcs.2018.09.024) | Geometric-sum domination, level-charge/coupling machinery and OneMax specialization (`StochasticDomination`, `CouplingDomination`, `OneMaxUnaryStochasticDomination`) | Other applications and general distributional assertions of the paper | **No** |
| Fixed-target runtime literature (including Buzdalov et al.) | Exact RLS-to-zero-count target and first-level Bellman identities (`RLSFixedTarget`, `BellmanFiniteExactRuntime`) | General fixed-target framework for other functions, algorithms, initial-state laws | **No** |
| Fixed-budget analysis literature | Exact zero-count mean after `t` one-bit RLS steps (`RLSFixedBudget`, `RLSUniformInitialFixedBudgetMean`) | General fixed-budget theory, distributional budgets, other algorithms and objectives | **No** |
| [Doerr et al. (2017), *Fast Genetic Algorithms*](https://doi.org/10.1145/3067695) / Jump-related results | Exact Jump plateau exit event, its geometric escape time and tail (`JumpPlateauEscape`) | Time to reach the plateau and full-runtime heavy-tailed algorithm analysis | **No** |
| [Witt (2013), *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*](https://doi.org/10.1017/S0963548312000600) | Standard-rate and restricted `c <= log 3` expected-time upper bounds and tails (`WittStandardRuntimeAsymptotics`, `WittMutationLogThreeRuntime`) | Unrestricted-rate sharpness, original matching lower bounds, complete parameter regimes | **No** |
| [Doerr, Janett, Lengler (2024)](https://doi.org/10.1007/s00453-024-01258-9) | General static mutation-mask formalism, factorial moments, corrected accepted-event inequalities, restricted superincreasing/BinVal drift/runtime (`StaticUnaryUnbiased*`) | General-linear sharp upper/lower bound claims; the event conditioning requires second-moment control not furnished by a mean-radius assumption alone | **No** |

Coverage estimates previously circulated (for instance 2/4 LeadingOnes clusters and 3/6 coupon-collector clusters) refer to *selected* theorem themes and should never be interpreted as objective percentages of all the paper's mathematical claims.

## B. Main certified results and executable entrypoints

### 1. General runtime machinery

- Finite mutation kernels, finite/infinite trajectories, hitting times and Bellman equations: `TransitionKernel.lean`, `FiniteTrajectory.lean`, `TrajectoryFirstHittingTime.lean`, `UnrestrictedRuntime.lean`, `BellmanFiniteExactRuntime.lean`.
- Additive and multiplicative drift, tails and geometric domination: `AdditiveDrift.lean`, `MultiplicativeDrift.lean`, `StochasticDomination.lean`, `CouplingDomination.lean`.

### 2. LeadingOnes under fixed independent-bit mutation

For `0 < p < 1` and uniform initialization, the exact expected time and the scaling `p=c/n` are formalized. The leading coefficient is

`F(c) = (exp(c)-1)/(2 c^2)`, for `c>0`,

with a unique global minimizer `c*` in `(1,2)` satisfying `(2-c*) exp(c*) = 2`.
Representative theorems: `leadingOnesUniformFirstHittingTimeExpectation_eq_formula`, `leadingOnes_scaled_fixedRate_limit`, `leadingOnes_fixedRate_unique_optimum`.

### 3. One-bit RLS on positive linear functions

Let `H_d=sum_{j=1}^d 1/j`, `Z_t` be the zero count and `T_n` the optimization time. Under **strictly positive weights**, elitist one-bit RLS behaves as a zero-bit coupon collector:

- Initial zero count `d`: `E[T | d]=n H_d`, and reaching at most `r` zeros has mean `n(H_d-H_r)`.
- Fixed budget: `E[Z_t | d] = d(1-1/n)^t`; uniform start gives `E[Z_t]=(n/2)(1-1/n)^t`.
- Uniform start: `E[T_n] = (n/2^n) sum_{k=0}^n binom(n,k) H_k = n(H_n-C_n)`, `C_n=sum_{j=1}^n 1/(j2^j)`.
- `E[T_n]/(n log n) -> 1` and `E[T_n]/n-H_n -> -log 2`.
- **Strong finite estimate:** `n(H_n-log 2) <= E[T_n] <= n(H_n-log 2)+n 2^(-n)`.
- **Stage 165 capped upper bound:** `P(T_n>t) <= min(1,(n/2)(1-1/n)^t)` for `n>0`.
- **Stage 166 exact law, certified by Round 55:**
  `P(T_n>t) = Σ_(j=1)^n (-1)^(j+1) choose(n,j) 2^(-j) (1-j/n)^t`,
  with the distribution computed under uniform initial states.

Primary public theorem modules: `RLSLinearExact.lean`, `RLSFixedTarget.lean`, `RLSUniformInitialExact.lean`, `RLSUniformInitialRuntimeFiniteCorrection.lean`, `RLSUniformInitialRuntimeSecondOrder.lean`, `RLSUniformInitialRuntimeLogTwoFiniteError.lean`, `RLSUniformInitialCouponSurvivalCapped.lean`, `RLSUniformInitialCouponSurvivalInclusionExclusion.lean`.

### 4. Other application families

- Unary OneMax harmonic upper bound and geometric domination (`OneMaxUnaryHarmonic`, `OneMaxUnaryStochasticDomination`).
- Exact Jump plateau escape and tail, *conditional on being at the plateau* (`JumpPlateauEscape`).
- Static unary unbiased mutation: supported moment/pivot/event theorems but not the unrestricted published main theorem (`StaticUnaryUnbiased*`).

## C. Outstanding publication-level claim groups

The definitive frontier and proof plans are in [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md). Short version:

1. **LeadingOnes adaptive mutation:** level-residence formula with state-dependent rates; pointwise rate optimization; sum-to-integral limit and adaptive lower bound. The rate should depend on current fitness, not merely `n`.
2. **Doerr--Doerr finer `-1/2` additive expansion:** from exact binomial-harmonic formula and parity-adjusted harmonic asymptotics; distinguish this from our already certified `-n log 2` shift.
3. **Centered completion-time distribution:** derive the proper scaling
   and limiting CDF from the now certified Stage 166 formula, with strict
   attention to discretization and tail control. This is a future extension.
4. **Fixed-budget/target and Jump:** extend beyond the current zero-count setting and local plateau departure.
5. **Witt and DJL:** tracked separately, with no implied solution of the DJL conditioning obstruction.

## D. Verification and limitations

- The **60** selected stages comprise the consecutive Stage IDs **107–166**,
  explicitly approved and compiled through the Round 55 full gate. They are
  **not** 60 distinct main theorems from the source literature.
- The compact public library contains **249 maintained Lean modules**.
  Round 56 had zero new hygiene warnings (233 grandfathered messages against
  a 282-warning historical baseline). The new exact survival theorem depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- Promotion cleanup in Round 56 removed only the redundant private Stage 166
  candidate. The certified public proof, root imports and regression witness
  remained unchanged and passed the complete verification gate.
- **Complete source papers covered by claim-by-claim audit: none.** The
  Stage 166 result extends the available certified finite-distributional
  theory, but does not close the source's parity-adjusted asymptotic constant
  or full monotone-function generality.

The intermediate Round 47–55 candidate proof diary was retired during final
consolidation; `HISTORY.md` retains the milestone record and
`CONSOLIDATION.md` records the final compiler evidence.
