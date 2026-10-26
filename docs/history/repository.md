---
line: repository
order: 6
---

# History: Repository events

Merge, verification, cleanup and tooling events that belong to no single research line.

## Current merged mathematical checkpoint (25 October 2026)

The main branch's original 158 public modules are preserved byte-for-byte and
389 independently certified public modules are added, producing a 547-module
Lean root library. The root aggregator imports the complete consolidated proof
graph, eight modules transitively rather than directly; the development instructions, `.claude` configuration, `lakefile.toml`
and unrelated main-branch files remain unchanged. The sole script adjustment is
`scripts/audit.lean`, whose explicit public-facade list now covers the merged
formalization.

The principal additions include exact adaptive LeadingOnes runtime and policy
optimality, sharp RLS/coupon random-initialization results, fixed-target/fixed-budget
runtime theory, and conditional static-unary/OneMax bounds. A historically false
unrestricted mutation-rate claim was replaced in the new Lean library by a
certified theorem assuming `0 ≤ p ≤ 1`. The source checkpoint closed its active
approved research queue; full source-paper formalization is not asserted.

See [the verified-paper audit](../current/README.md#paper-by-paper-coverage) for coverage percentages,
certified Lean declarations, and the important missing theorems. The original
stage history below is retained as a record of earlier development; its old
"current" milestones do not supersede this checkpoint. The main branch's
historical verification scripts are deliberately preserved except for the
minimal reachability-list update in `scripts/audit.lean`.

## Provenance of the merged modules — no per-stage record

The merged modules entered `main` as one bulk merge (pull request #1, merge commit
`f363b04`), not through the stage workflow recorded below. This file therefore has
no candidate, fix or promotion entries for them, and none will be reconstructed. The
merged branch's own traces remain in git:

- commits `55391b7` (21 October), `e3ad5cc` (23 October) and `a20e19f`
  (25 October 2026);
- the source checkpoint's chronology documents `docs/RESEARCH.md`,
  `docs/OPEN_PROBLEMS.md` and `docs/CONSOLIDATION.md`, deleted in `a20e19f` and
  readable as `git show a20e19f^:docs/<file>`. They record source stages 107–166 up
  to the 23 October checkpoint, not the final 547-module state;
- the source checkpoint's promotion registry (316 promoted entries, two
  retired-invalid) was not imported; `docs/VERIFIED_PAPERS.md` summarizes it.

The 389 added modules include the Stage 80 candidate
`StaticUnaryUnbiasedEventWeightedRightLoss`, which `main` held with `sorry`
(`2ae28ba`) and the merged branch completed. Stage numbers cited in the merged
modules' doc comments (up to 460) belong to the source checkpoint's own sequence: they
overlap this file's numbering from 80 onward and do not continue it. Stages
on `main` therefore resume at 461. Status words in
those comments ("open", "proposed") are the source's labels when written, not the
current status; `docs/VERIFIED_PAPERS.md` is authoritative.

Deliberately deferred: a full-gate `scripts/verify.ps1` record for the merged state,
statement pins and axiom tests for the merged facades, and regeneration of
`docs/graphs` to include them.

Lean modules: [`StaticUnaryUnbiasedEventWeightedRightLoss`](../../ECRuntime/StaticUnaryUnbiasedEventWeightedRightLoss.lean)

## Merge verification — full gate green (26 October 2026)

The first build of the merged state in this checkout. Before it, the local build tree
held only the 159 pre-merge modules; the merged modules' compilation certificate
belonged to the source checkpoint alone.
`pwsh -File scripts/verify.ps1 -Stage merge-547`, run on a clean tree at `c30f035`:

```
root_aggregator=0  hygiene=0  cache_get=0  focused_build=0  full_build=0
test_build=0  diagnostics_clean=0  graphs=0  export=0  overall=0
```

- The full build (9203 jobs) and the test build (8830 jobs) have zero `error:` and
  zero `warning:` lines. `focused_build` was vacuous: the merge has no single new
  module, so the run passed no `-Focus`.
- `scripts/audit.lean strict`: 2951 declarations, 0 errors, 289 warnings — 280 missing
  doc comments, 8 unused signature binders, and the one remaining grandfathered orphan.
  No declaration depends on `sorry` or a non-standard axiom.
- Fifteen of the sixteen grandfathered orphans became reachable from the merged
  facades and were removed from `orphanAllowlist` (`c30f035`).
- The graphs gate regenerated `docs/graphs` for 547 modules and 3391 proof edges
  (`9666e8f`). The export gate wrote the local repository archive.

Deliberately deferred: statement pins and axiom tests for the merged facades; six
`ring` calls that close only through the `ring_nf` fallback (reported as `info:`, not
a gate failure); `familyOf` prefixes for the merged families, without which the
architecture view files most merged modules under "Generic runtime theory"; the
missing doc comments and unused binders listed above.

## Pins for the paper-audit citations (26 October 2026)

`ECRuntimeTest/VerifiedPapersAxiomAudit.lean` and `VerifiedPapersStatementPins.lean`
pin the 50 theorems that `docs/VERIFIED_PAPERS.md` cites and the original pins did not
already cover. Both files are generated from compiler output; all 50 depend on exactly
`propext`, `Classical.choice` and `Quot.sound`. Altering one expected statement or
axiom list in a scratch copy fails compilation at that entry. The full build passes
with zero errors and warnings.

Deliberately deferred: pins for the merged facades the audit does not cite (133 of
147), and non-vacuity witnesses for the merged theorems.

## Generated facade index (26 October 2026)

`scripts/facade_index.ps1` generates `docs/FACADE_INDEX.md` from the facade lists in
`audit.lean json`: for each of the 153 public facades its `VERIFIED_PAPERS.md` section,
the paper label from its own doc comment (unaudited), its theorems, its pins and a
one-sentence summary from the first theorem doc comment. Regeneration is deterministic
and is not part of the `verify.ps1` gate.

Open, not deferred as cosmetic: merged module doc comments record two kinds of source
state. Build states ("pending promotion", "provisional", "candidate until checked") are
outdated, since the modules compile without `sorry` in the gate-green library.
Statement-approval states ("unapproved", "NOT APPROVED", "awaiting statement approval",
"new proposal") cannot be checked: the source registry was not imported, and git
history holds no approval record. 52 modules carry such a state, 18 of them public
facades, and two are cited by `docs/VERIFIED_PAPERS.md`
(`RLSAllDimensionPaperCenteredExact`, `RLSStrictMonotoneFixedTargetExact`). Their
statements have no recorded human approval on `main`; the phrases stay until they do.

Lean modules: [`RLSAllDimensionPaperCenteredExact`](../../ECRuntime/RLSAllDimensionPaperCenteredExact.lean), [`RLSStrictMonotoneFixedTargetExact`](../../ECRuntime/RLSStrictMonotoneFixedTargetExact.lean)

## Merge cleanup — full gate green (26 October 2026)

Two items deferred by the merge verification are resolved. The six `ring` calls that
closed only through the `ring_nf` fallback now call `ring_nf` directly; the build has
no `info:` lines left, and every statement pin is unchanged. `familyOf` in
`scripts/audit.lean` now recognises the merged families (`AdaptiveLeadingOnes*`,
`StaticUnary*`, `UnaryOneMax*`, `Jump*` and a new "RLS & coupon collector" family), so
the architecture view no longer files 370 modules under "Generic runtime theory"
(now 129). `verify.ps1 -Stage merge-547-cleanup`: every gate 0.

## Literature-roadmap snapshot: verified baseline at Stage 79

> The "Current verified baseline" section of the literature roadmap, moved verbatim on 2026-10-26. It describes the state before the merge.

### Generic stochastic/runtime infrastructure

The repository covers finite/infinite trajectories, hitting times, additive and multiplicative drift, fitness levels, stochastic domination, geometric waiting-time comparisons, and high-probability tails. This infrastructure is intended for reuse across EC algorithms.

### LeadingOnes

The completed LeadingOnes line formalizes exact entry/residence/occupation structure and exact expected runtime. The public façade is `LeadingOnesMainResults.lean`.

A useful modern reference for the broader fitness-level context is:

- Benjamin Doerr and Timo Kötzing, *Lower Bounds from Fitness Levels Made Easy*, Algorithmica 86 (2024), 367--395, DOI 10.1007/s00453-022-00952-w.

### Linear functions and Witt's theorem

The main linear-function line follows:

- Carsten Witt, *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*, Combinatorics, Probability and Computing 22(2) (2013), 294--318, DOI 10.1017/S0963548312000600.

The repository formalizes a Witt-style potential for positive nonincreasing linear weights, the C2/C3 decomposition, exact-singleton-rate multiplicative drift, finite expectation/tail bounds, the scaled rate `p=c/n`, and fixed-scale singleton-rate asymptotics with normalized factor `exp(c)/c`.

**Stage 66 fix 6 closes the finite C3 interval exactly:**

```text
0 <= c <= log 3,    n >= 4.
```

**Stage 67 is compiler promoted.** It factors the C3-based expectation/tail consequences into `WittMutationCertifiedRuntime.lean`, exposes the final `0 < c <= log 3` runtime/tail adapter, and removes superseded numerical endpoint modules. The finite-boundary Witt branch is now frozen.

The maintained modules on this line are `WittMutationPotential.lean`,
`WittMutationDrift.lean`, `WittMutationCaseC3.lean`, `WittMutationC3Envelope.lean`,
`WittMutationStrictTail.lean`, `WittMutationCertifiedRuntime.lean`,
`WittMutationC3LogThreeRegime.lean`, `WittMutationLogThreeRuntime.lean`,
`WittMutationRateAsymptotics.lean`, and `WittMutationSharpRuntimeAsymptotics.lean`.

`WittMutationC3ExtendedRegime.lean` and `WittMutationExtendedRuntime.lean` remain only as
the older `21/20` compatibility/public API layer used by existing asymptotic presentation
modules.

## Literature-roadmap snapshot: merged results (26 October 2026)

> The "Merged results" section of the literature roadmap, moved verbatim on 2026-10-26.

The merge certified results outside the stage workflow; [`docs/current/papers/`](../current/papers) lists, paper by paper, the declarations and the missing headline families for each. Relative to this roadmap:

- **Priority A, ingredient 10** is closed under `NonincreasingLinearWeights`: `StaticUnaryUnbiasedEventWeightedRightLoss`, `StaticUnaryUnbiasedPivotDrift`, `StaticUnaryUnbiasedGlobalDrift`, `StaticUnaryUnbiasedCorrectedRuntime` and `StaticUnaryUnbiasedSharpMomentUpper`. The sharp upper envelope needs a uniform factorial-moment ratio bound; no mean-only estimate and no lower bound are claimed.
- **LeadingOnes:** the optimal static rate (frontier B1) is certified as an exact characterization; the adaptive exact runtime and optimal schedule are certified, while the `~0.68 n²` asymptotic of B2 is not.
- **New lines** not planned here: the random-initial-stake coupon collector and RLS on monotone functions, fixed-target and fixed-budget RLS results, Jump plateau escape, and OneMax lower bounds. Their open headline results are frontier Tier M.
