# ECRuntime

**Runtime analysis of evolutionary algorithms, machine-checked in Lean 4.**

How many evaluations does a `(1+1)` evolutionary algorithm need to optimize OneMax,
LeadingOnes, or a linear function? The evolutionary-computation literature answers this
with delicate probabilistic arguments. ECRuntime rebuilds those arguments from first
principles and has a proof assistant check every step.

**158 modules · 41,980 lines · 1,398 theorems · Lean 4.32.1 / Mathlib v4.32.1**

No `sorry`, no added axioms, no `native_decide`, no `set_option` — enforced by an axiom
audit that fails the build if any of them ever slips in.

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

Current promoted checkpoint: **Stage 79 fix 1**. No active Stage-80 candidate.

## How the claims are kept honest

A green build is not a true theorem. `lake build` therefore also runs `ECRuntimeTest/`:

| Check | What it catches |
|---|---|
| **Axiom audit** | Every facade theorem must depend on exactly `propext`, `Classical.choice`, `Quot.sound` — a `sorry` laundered through a helper lemma still fails. |
| **Statement pins** | The elaborated type of each promoted theorem is frozen, so a statement cannot be quietly weakened to make a proof close. |
| **Non-vacuity witnesses** | Concrete witnesses discharge every hypothesis, so no theorem can be vacuously true. |

The full promotion gate — root aggregator, hygiene, cache, focused build, complete root
build, zero-diagnostics scan, test suite, export — runs via:

```
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<Module>
```

Warnings count as failures.

## What this does *not* claim

The project separates a *certified paper-level result* from a *certified supporting chain*
and from *reusable infrastructure*, and records which is which for every entry. Several
headline theorems from the literature are deliberately not claimed, and the hypotheses in
force are stated explicitly. The list is in
[`docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md)
§3.15.

## Documentation

| File | What it holds |
|---|---|
| [`DEVELOPMENT.md`](DEVELOPMENT.md) | Invariant workflow rules: promotion criterion, proof architecture, verification runners, export discipline. |
| [`HISTORY.md`](HISTORY.md) | Chronological stage and fix milestones. |
| [`docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md) | Full catalogue of what is proved, with provenance, status vocabulary, and the next-paper frontier. |
| [`docs/LITERATURE_ROADMAP.md`](docs/LITERATURE_ROADMAP.md) | Literature mapping, proof order, and the near-term plan. |
| [`docs/PROJECT_STATE.tex`](docs/PROJECT_STATE.tex) | Current mathematical state and promoted boundary, with display equations. |
