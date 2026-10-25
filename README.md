# ECRuntime

**Runtime analysis of evolutionary algorithms, machine-checked in Lean 4.**

How many evaluations does a `(1+1)` evolutionary algorithm need to optimize OneMax,
LeadingOnes, or a linear function? The evolutionary-computation literature answers this
with delicate probabilistic arguments. ECRuntime rebuilds those arguments from first
principles and has a proof assistant check every step.

**547 public Lean modules · Lean 4.32.1 / Mathlib v4.32.1**

This merge adds 389 certified mathematical modules to the original 158 and
retains all existing mathematical source files unchanged. The resulting root
import graph is that of the consolidated, previously verified repository.
The original main-branch development instructions and build configuration
remain unchanged. The only verification-script update is `scripts/audit.lean`,
which explicitly recognizes the new public result families.

The added public modules were independently certified without admitted proofs or
nonstandard axioms in the source checkpoint. Main's statement-pin and other
verification scripts remain unchanged; the reachability portion of the source
hygiene audit has been extended to the merged proof graph.

## Quick start

```bash
lake exe cache get   # pinned Mathlib build cache
lake build           # builds the library and runs the regression suite
```

## Highlights

**Exact expected runtime for LeadingOnes.** For uniform initialization and any mutation
probability `0 < p < 1`:

$$
\mathbb{E}[T] = \frac{1}{2}\sum_{i=0}^{n-1}\frac{1}{p(1-p)^i}
$$

algebraically equivalent to the Böttcher–Doerr–Neumann (2010) closed form. The public
facade is `ECRuntime.LeadingOnesMainResults`.

**Witt's sharp upper bound for linear functions.** At the standard rate `p = 1/n`, for
positive nonincreasing weights, the explicit finite envelope `e·n·log n + 2·e·n`. For the
scaled rate `p = c/n`, a dimension-uniform certificate on

$$
0 \le c \le \log 3, \qquad n \ge 4
$$

carrying the sharp leading factor `e^c/c`, which is minimized at `c = 1`.

**A gap found in a 2024 paper.** While formalizing Doerr–Janett–Lengler (2024), the
project found a conditioning issue in an intermediate displayed step. Rather than certify
the published proof verbatim, the repository builds a corrected factorial-moment route.
Discovering that a published argument does not survive formalization is a result in its
own right.

**Reusable infrastructure.** Markov-kernel / Ionescu–Tulcea trajectory semantics, additive
and multiplicative drift, fitness levels, stochastic domination, geometric waiting times
and first-hitting-time theory — stated for general stochastic processes rather than for a
single algorithm.

**Merged mathematical checkpoint:** 547 public Lean modules. The source repository
completed its verification gates before this merge; the combined main-branch
checkout still requires its own `lake build` and complete verification run.

## Additional verified results

- **Adaptive LeadingOnes:** exact uniform-initial trajectory-level runtime for
  interior level-dependent rates; optimal positive-level mutation rates,
  equality/uniqueness statements, and an unattained level-zero boundary infimum.
- **RLS and coupon collection:** sharp random-initialization corrections,
  arbitrary-target survival and hitting-time correspondences, and finite/infinite
  weighted moment transfers.
- **OneMax and unary unbiased mutation:** fixed-target and fixed-budget bounds,
  mean-radius identities, harmonic runtime formulas, and drift-cap results under
  their stated assumptions.
- **Linear functions:** additional standard-bit-mutation and static unary
  unbiased analysis, while the unrestricted headline bounds of the 2024
  Doerr–Janett–Lengler paper remain **unverified**.

The paper-by-paper verified and missing headline theorems, including approximate
coverage percentages, are in [`docs/VERIFIED_PAPERS.md`](docs/VERIFIED_PAPERS.md).

## How the claims are kept honest

Compilation is necessary but does not by itself establish absence of added axioms,
non-vacuity, or faithful paper-level coverage. The existing main-branch test
infrastructure is retained, and the three additional regression witnesses
imported by the certified source test root are included:

| Check | What it catches |
|---|---|
| **Axiom / source-hygiene audit** | The updated main audit checks 6 historical and 147 new explicit public facade roots, transitive admitted/nonstandard-axiom dependencies, documentation, and unused signature binders. |
| **Statement pins** | The original main-branch theorem statements remain guarded; new declarations were checked in the source checkpoint and are not yet added to main's pin system. |
| **Non-vacuity witnesses** | Original witnesses and three verified new witness modules are imported; this is not a universal automatic non-vacuity proof. |

The existing main-branch promotion command remains:

```
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<Module>
```

Warnings count as failures in the promotion workflow. The updated
`scripts/audit.lean` tests import reachability from an explicit, maintained set
of 153 public facades, rather than treating the umbrella root as a facade.
The pre-existing `LevelChargeExactResidence` grandfathered-orphan warning is
retained; any newly disconnected module remains an error. Run the audit with:

```bash
lake env lean --run scripts/audit.lean strict
```

Also run `lake build ECRuntime ECRuntimeTest` and the main-branch verification
workflow on the pinned toolchain. The combined checkout has not been independently
Lean-compiled in the merge-preparation environment; successful static source
checks do not substitute for the full compiler and promotion gates.

## What this does *not* claim

The project separates a *certified paper-level result* from a *certified supporting chain*
and from *reusable infrastructure*, and records which is which for every entry. Several
headline theorems from the literature are deliberately not claimed, and the hypotheses in
force are stated explicitly. The **current** paper-level assessment is
[`docs/VERIFIED_PAPERS.md`](docs/VERIFIED_PAPERS.md). The original
[`docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md)
is preserved as a historical main-branch checkpoint and is not the current
coverage inventory.

## Documentation

| File | What it holds |
|---|---|
| [`DEVELOPMENT.md`](DEVELOPMENT.md) | Invariant workflow rules: promotion criterion, proof architecture, verification runners, export discipline. |
| [`HISTORY.md`](HISTORY.md) | Main-branch history with the new consolidated mathematical checkpoint at the top. |
| [`docs/VERIFIED_PAPERS.md`](docs/VERIFIED_PAPERS.md) | Current per-paper percentages, certified declarations, and missing headline results. |
| [`docs/P02_THEOREM_TO_PAPER_AUDIT.md`](docs/P02_THEOREM_TO_PAPER_AUDIT.md) | Separate correspondence audit for the 2013 and 2016 Doerr–Doerr papers. |
| [`docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md) | Historical main-branch catalogue (prior to the 547-module merge). |
| [`docs/LITERATURE_ROADMAP.md`](docs/LITERATURE_ROADMAP.md) | Historical literature roadmap (not the new coverage audit). |
| [`docs/PROJECT_STATE.tex`](docs/PROJECT_STATE.tex) | Historical mathematical state before this merge. |
