# Current state

**Checkpoint:** 26 October 2026 · Lean 4.32.1 / Mathlib v4.32.1

## The library

- **547 Lean modules**: the 158 original main-branch modules and 389 added by the merge
  (see [`history/repository.md`](../history/repository.md)).
- **2951 own declarations.** None depends on `sorry` or a non-standard axiom
  (`scripts/audit.lean strict`: 0 errors).
- **153 public facades**: 6 original and 147 merged, listed in [`facades.md`](facades.md).

## Last full gate

`pwsh -File scripts/verify.ps1 -Stage merge-547-cleanup`, 26 October 2026: every gate 0,
zero `error:` and `warning:` lines. The gate tables are in
[`history/repository.md`](../history/repository.md).

## What the tests guarantee

- Statement pins and axiom tests cover the original facades and every theorem cited in
  [`papers/`](papers/).
- Not covered: the other merged facades (133 of 147) have no pins, and the merged
  theorems cited in `papers/` have no non-vacuity witnesses yet.

## Scope and limits

What the library does **not** claim:

- **No publication is completely formalized.** The project separates a *certified
  paper-level result* from a *certified supporting chain* and from *reusable
  infrastructure*, and records which is which for every entry; the levels are defined in
  [Status vocabulary](#status-vocabulary) below.
- **Linear-function results assume positive, nonincreasing weights**
  (`NonincreasingLinearWeights`). The reduction from arbitrary positive weights to sorted
  ones is not formalized, so no result is claimed for all linear functions.
- **Doerr, Janett and Lengler (2024):** the general sharp upper and lower bounds are not
  proved; the certified upper envelope needs an additional uniform factorial-moment
  bound. Details in [`papers/doerr-janett-lengler-2024.md`](papers/doerr-janett-lengler-2024.md).
- Several further headline theorems are deliberately not claimed, and the hypotheses in
  force are stated explicitly; [`papers/`](papers/) lists what is missing paper by paper.
  The original
  [`FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md)
  is preserved in the archive as a historical checkpoint, not as the current inventory.

## Known open items

- **Statements without recorded approval.** The doc comments of 52 merged modules record
  their statement as unapproved or only proposed, and no later approval is recorded on
  `main`. 18 are public facades; two are cited as paper evidence
  (`RLSAllDimensionPaperCenteredExact`, `RLSStrictMonotoneFixedTargetExact`).
- `HasUniformExactLevelExitBounds` appears at 76 sites, always as a hypothesis, and is
  never discharged.
- Audit warnings: 280 declarations without a doc comment (73 of them compiler-generated),
  8 unused signature hypotheses, and one grandfathered orphan module
  (`LevelChargeExactResidence`).

## Status vocabulary

> Copied verbatim from section 1 of the frozen Stage-79 frontier document,
> [`FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).
> This copy is the authoritative definition from now on; "this document" below refers
> to the original.

This document deliberately distinguishes three different relationships between the repository and a paper.

- **Certified paper-level result:** the repository proves the mathematical statement (possibly in an equivalent convention or with a slightly stronger finite-dimensional interface) and the relevant source tree has passed the pinned compiler with no warnings or errors.
- **Certified supporting chain / paper theorem not yet closed:** substantial lemmas from a paper's proof have been formalized, but the repository does **not** claim the paper's headline theorem yet.
- **Reusable infrastructure:** the repository proves a general theorem from the same methodological lineage, but it is not intended as a line-by-line mechanization of a particular paper.

This distinction is especially important for the 2024 static unary-unbiased linear-function paper: the repository has found a conditioning issue in an intermediate displayed step and has therefore built a corrected factorial-moment route instead of certifying the published proof verbatim.

## Paper-by-paper coverage

One file per paper in [`papers/`](papers/); the status levels are defined in
[Status vocabulary](#status-vocabulary) above. No paper is claimed as
completely certified; the unrestricted headline bounds of Doerr, Janett and Lengler (2024)
are **not** proved.

**Audited checkpoint:** 25 October 2026; Lean 4.32.1 / Mathlib v4.32.1.
The independently certified **source checkpoint** contains **547 public Lean
modules**, 19 retained regression-test source modules, 316 promoted registry
entries, two retired-invalid entries, and no active research candidates. The
present **minimal merge onto main** copies all 547 public Lean modules but
only the three additional regression-test files loaded by that checkpoint's
default test root (six test modules total including the three main-branch tests).
It deliberately does **not** import the source registry or retired-claim
archive, preserving the main branch's development files and governance.
The combined main checkout was compiled separately on 26 October 2026: the full
`scripts/verify.ps1` gate passed with zero errors and warnings (see
[`history/repository.md`](../history/repository.md), merge verification). Every Lean theorem cited below has a statement pin and an
axiom test in `ECRuntimeTest` (`VerifiedPapersStatementPins`,
`VerifiedPapersAxiomAudit`, or the original `StatementPins` and `AxiomAudit`); a
newly cited theorem must be pinned in the same change. Non-vacuity witnesses for
them are not yet added. This is a *mathematical correspondence
audit*, not a count of all lemmas or paper pages.

### Meaning of the coverage estimates

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

### Coverage at a glance

| ID | Publication | Approximate headline-family coverage | Crucial qualification |
|---|---|---:|---|
| [P01](papers/boettcher-doerr-neumann-2010.md) | [Böttcher, Doerr, Neumann (2010), *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*](https://doi.org/10.1007/978-3-642-15844-5_1) | **~85%** | Fixed and genuine adaptive exact means and optimality are certified; the explicit optimized `~0.68 n²` asymptotic statement is not yet located as a theorem |
| [P02](papers/doerr-doerr-2013.md) | [Doerr, Doerr (2013), *Collecting Coupons with Random Initial Stake*](https://arxiv.org/abs/1308.6384) | **~95% of headline claims** | Both numbered headline theorems have direct certified counterparts; not every paper-specific auxiliary inequality is audited |
| [P02b](papers/doerr-doerr-2016.md) | [Doerr, Doerr (2016), *The Impact of Random Initialization on the Runtime of Randomized Search Heuristics*](https://doi.org/10.1007/s00453-015-0019-5) | **~25%** | Primarily the RLS/OneMax subcase; not the broader `(1+1)`-EA or LeadingOnes comparison families |
| [P03](papers/he-yao-2001.md) | [He, Yao (2001), *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*](https://doi.org/10.1016/S0004-3702(01)00058-3) | **~20%** | Finite-state additive-drift upper-bound specialization |
| [P04](papers/doerr-johannsen-winzen-2012.md) | [Doerr, Johannsen, Winzen (2012), *Multiplicative Drift Analysis*](https://arxiv.org/abs/1101.0776) | **~30%** | Multiplicative-drift bound and selected linear-function consequences, not all applications and matching lower bounds |
| [P05](papers/lehre-witt-2014.md) | [Lehre, Witt (2014), *General Drift Analysis with Tail Bounds*](https://arxiv.org/abs/1307.2559) | **~15%** | Specialized drift/tail bounds, not the general variable-drift two-sided theorem |
| [P06](papers/doerr-2019.md) | [Doerr (2019), *Analyzing Randomized Search Heuristics via Stochastic Domination*](https://doi.org/10.1016/j.tcs.2018.09.024) | **~35%** | Geometric-waiting and coupling domination, not the universal mutation-based comparison or all applications |
| [P07](papers/buzdalov-et-al-2020.md) | [Buzdalov, Doerr, Doerr, Vinokurov (2020/2022), *Fixed-Target Runtime Analysis*](https://arxiv.org/abs/2004.09613) | **~40%** | Exact harmonic lemma and specified RLS/LeadingOnes subcases; broader fixed-target operator families are open |
| [P08](papers/jansen-zarges-2014.md) | [Jansen, Zarges (2014), *Performance Analysis of Randomised Search Heuristics Operating with a Fixed Budget*](https://doi.org/10.1016/j.tcs.2013.06.007) | **~20%** | Exact RLS/OneMax-type fixed-budget expectation only |
| [P09](papers/doerr-et-al-2017.md) | [Doerr, Le, Makhmara, Nguyen (2017), *Fast Genetic Algorithms*](https://arxiv.org/abs/1703.03334) | **~20%** | Jump plateau escape and optimal fixed escape rate; no heavy-tailed full-runtime theorem |
| [P10](papers/witt-2013.md) | [Witt (2013), *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*](https://doi.org/10.1017/S0963548312000600) | **~35%** | Sharp standard-rate upper and restricted scaled-rate tails, not complete sharp lower/optimality claims |
| [P11](papers/doerr-janett-lengler-2024.md) | [Doerr, Janett, Lengler (2024), *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*](https://doi.org/10.1007/s00453-024-01258-9) | **~20% supporting/special cases; 0% of two unrestricted headline bounds** | Moment, coordinate-marginal and conditional upper-bound infrastructure, not the general sharp upper and lower results |
| [P12](papers/droste-jansen-wegener-2002.md) | [Droste, Jansen, Wegener (2002), *On the Analysis of the (1+1) Evolutionary Algorithm*](https://doi.org/10.1016/S0304-3975(01)00182-7) | **~15% by overlapping consequence** | Positive-linear `O(n log n)` follows from later certified bounds; most original lower/hardness results are open |

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

### Detailed correspondence audit

One file per paper in [`papers/`](papers); each gives the verified headline results with their Lean declarations and what is not yet verified.

### Important distinctions and next audit actions

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
above. The main branch's [literature frontier](../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md)
is frozen at Stage 79 and archived; its status vocabulary now lives in
[Status vocabulary](#status-vocabulary) and its frontier entries in
[`roadmap/papers/`](../roadmap/papers/README.md). The [roadmap](../roadmap/README.md) and
`frontier.toml` are live and were reconciled with the 547-module checkpoint on
26 October 2026. The merge preserves the main verification workflow except for an explicit
extension of the public-facade list in `scripts/audit.lean`; see `README.md`
for verification instructions. See
the annex of [`papers/doerr-doerr-2013.md`](papers/doerr-doerr-2013.md) for the
separate P02a/P02b interpretation and verified coupon/RLS declarations.

What comes next is in [`roadmap/`](../roadmap/README.md).
