# ECRuntime

Lean 4 formalization of runtime analysis for evolutionary computation (EC), with an emphasis on reusable stochastic-process infrastructure and machine-checked proofs of classical runtime theorems.

## Verification status

The repository is pinned to **Lean 4.32.1 / Mathlib v4.32.1**.

**Latest compiler-promoted checkpoint: Stage 79 fix 1 (2026-09-25).** The corrected-left-gain module and the complete root build both succeeded warning/error-free, together with repository export and source-hygiene checks. Stage 79 fix 1 therefore promotes the corrected suffix-ratio geometry, pointwise nonnegativity of the accepted left contribution, the exact singleton left gain, and the event-weighted lower bound `(p₁/n) g_i`.

The promoted finite Witt interval is therefore

\[
0 \le c \le \log 3, \qquad n\ge4,
\]

with final expectation and high-probability runtime interfaces on `0 < c <= log 3`. The fixed-scale exact singleton-rate asymptotic remains

\[
(n q_n(c))^{-1}\longrightarrow \frac{e^c}{c},
\qquad
q_n(c)=\frac cn\left(1-\frac cn\right)^{n-1},
\]

with `e^c/c` minimized at `c=1`.

There is currently **no active theorem candidate**. The repository is intentionally paused at the promoted Stage-79-fix-1 boundary while the certified theorem inventory and literature frontier are consolidated. The exact current catalogue and the literature-derived next-paper list are in `docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`.

To reproduce the promoted checkpoint, run:

```bash
bash scripts/verify.sh --stage 79 --focus ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain
```

The runner is stage-agnostic: the stage is an argument, not part of the filename. Gates are
root aggregator, source hygiene, dependency cache, the focused target, the complete root
build, a zero-diagnostics scan, the `ECRuntimeTest` regression suite, and the source export.
Warnings count as failures.

## Main formalized layers

### Stochastic-process semantics

The repository contains finite and infinite trajectory semantics for stochastic transition systems, including finite path weights, projective consistency, Markov-kernel/Ionescu--Tulcea trajectories, finite-marginal identification, first-hitting-time semantics, and unrestricted-runtime bridges.

### Generic runtime tools

The reusable analysis layer contains additive and multiplicative drift, fitness levels, stochastic domination, geometric waiting times and sums, coupling/residence infrastructure, and geometric/shifted-exponential tail bounds.

### LeadingOnes

The LeadingOnes development contains exact first-entry, residence, occupation, and renewal arguments and culminates in exact expected-runtime results with standard/scaled mutation-rate interfaces. The public entry point is `ECRuntime.LeadingOnesMainResults`.

### Linear functions / Witt analysis

The linear-function development formalizes the Witt-style potential argument and separates potential/drift decomposition, C2/C3 and strict-tail analysis, exact-singleton-rate multiplicative drift, generic expectation/tail consequences, and fixed-scale asymptotics.

**Hypothesis in force.** These results assume *positive nonincreasing* weights
(`PositiveLinearWeights` and `NonincreasingLinearWeights`). The reduction of an arbitrary
positive linear function to a sorted one is routine on paper but is **not** formalized here,
so the certified statements cover sorted weight vectors rather than all linear functions.

The finite-boundary branch is now frozen at the exact natural boundary `c <= log 3`. Important maintained modules include:

- `WittMutationPotential.lean`
- `WittMutationDrift.lean`
- `WittMutationCaseC3.lean`
- `WittMutationC3Envelope.lean`
- `WittMutationStrictTail.lean`
- `WittMutationCertifiedRuntime.lean`
- `WittMutationC3LogThreeRegime.lean`
- `WittMutationLogThreeRuntime.lean`
- `WittMutationRateAsymptotics.lean`
- `WittMutationSharpRuntimeAsymptotics.lean`

`WittMutationC3ExtendedRegime.lean` and `WittMutationExtendedRuntime.lean` remain only as the older `21/20` compatibility/public API layer used by existing asymptotic presentation modules.

### Static unary-unbiased mutation

Stage 68 promotes the operator-level abstraction intended for the next linear-function theorem family. A `StaticUnaryUnbiasedMutation n` is a probability law on mutation masks that is invariant under mask cardinality. Its derived quantities include:

- `radiusMass law k`: probability of flipping exactly `k` bits;
- `oneBitMass law`: the literature parameter `p₁`;
- `meanRadius law`: the expected mutation strength `χ`;
- `singleZeroFlipWeight law x`: aggregate mass of elementary one-bit improvements.

The independent-bit `(1+1)` EA is embedded as `independentBitLaw`, so the new abstraction extends rather than forks the existing mutation semantics.

## Repository design

The intended theorem architecture is:

```text
algorithm-independent probability/runtime lemma
        -> operator-specific transition/kernel facts
        -> objective/potential-specific progress theorem
        -> generic expectation/tail consequence
        -> literature-facing asymptotic corollary
```

Development-history endpoints should not become permanent dependencies. Once a natural theorem boundary is proved, serial numerical endpoint modules are removed in favor of generic certificates and final specializations.

## Development workflow

See `DEVELOPMENT.md`. In particular:

- the pinned user build is authoritative for promotion;
- warnings fail promotion;
- every substantive round returns a full repository ZIP plus a safe overlay/patch;
- generated logs/build products are not retained in the source tree;
- the verification runner performs focused candidate builds, one complete root build, diagnostics, and a whitelist-based source export.

## Next research step

Stage 79 fix 1 is the latest promoted checkpoint. No Stage-80 theorem is introduced in this repository-state update. The immediate proof boundary remains to uncondition the promoted right-loss proxy into the actual event-weighted right contribution and combine it with the promoted Stage-79 singleton left contribution to obtain the corrected per-pivot drift inequality. A broader, literature-derived menu of subsequent targets is recorded in `docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`; the shorter proof-order roadmap remains in `docs/LITERATURE_ROADMAP.md`.
