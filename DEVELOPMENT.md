# Development practices

This file records invariant development rules for ECRuntime. Historical compiler-fix chronology belongs in `HISTORY.md` and version control, not here.

## 1. Verification authority

- The project is pinned to **Lean 4.32.1** and **Mathlib v4.32.1**.
- A build in the pinned project environment is the authority for promotion. That build may
  now be run locally by whoever prepared the change: `scripts/verify.sh` executes the full
  gate, so work is presented already verified rather than handed over for verification.
- **Promotion remains a human decision.** A green gate makes a stage *promotable*; it does
  not promote it. Separating who produces from who promotes is the point of this section,
  and it survives the change above.
- New or refactored source is a **candidate** until a clean gate run says otherwise. A run
  with `--candidate` (which permits `sorry`) is never promotable, however green.
- Local/static inspection may guide development but never substitutes for the pinned build.

The latest promoted checkpoint is **Stage 79 fix 1**. It compiler-promotes the corrected suffix-ratio geometry, pointwise nonnegative accepted left contribution, exact singleton left gain, and event-weighted lower bound `(p₁/n) g_i`. There is currently **no active theorem candidate**; the repository is paused at this clean boundary for theorem-inventory and literature-frontier consolidation.

## 2. Promotion criterion

A stage is promoted only when all required checks succeed:

1. root aggregator present;
2. source hygiene (`scripts/hygiene.py`);
3. dependency/cache setup;
4. each designated focused target;
5. complete root `lake build`;
6. the `ECRuntimeTest` regression suite;
7. no `error:` or `warning:` diagnostics;
8. repository export, source ZIP and manifest generation.

Warnings count as failures. A focused build alone is insufficient.

`scripts/verify.sh --stage <N> --focus <module>` runs all eight and prints the gate table.

Gate 6 is what a plain `lake build` cannot give you. `ECRuntimeTest` pins, for every facade
theorem, both its axiom dependencies and its elaborated statement. It therefore rejects a
`sorry` reached through an intermediate lemma whose own text is clean, and it rejects a
silently weakened hypothesis. Section 5's rule that a fix round changes no theorem statement
is enforced there rather than merely asserted in `HISTORY.md`.

Pins are generated from compiler output and never hand-written. A pin edited to make the
build pass defeats the mechanism entirely.

## 3. Candidate versus promoted source

- Keep the promoted/candidate boundary explicit in code and documentation.
- Preserve promoted mathematical interfaces during compiler-driven repairs when practical.
- Do not weaken a theorem merely to obtain compilation without documenting the mathematical change.
- Once a stronger theorem subsumes endpoint-only modules, remove those modules unless they contain independent reusable mathematics.

## 4. Proof architecture

Prefer reusable theorem boundaries over stage-specific wrappers.

- Generic stochastic-process, drift, tail, and asymptotic infrastructure belongs in generic modules.
- Operator semantics should be separated from objective-specific progress arguments.
- Problem-specific modules should provide only the semantic/potential facts needed to instantiate generic results.
- Numerical endpoint modules should be temporary proof-discovery devices, not permanent dependency chains.
- Avoid duplicating expectation/tail proofs for every certified parameter regime.

For the completed Witt mutation line, the generic boundaries are `WittMutationC3Envelope.lean` and `WittMutationCertifiedRuntime.lean`, with final specialization through `WittMutationC3LogThreeRegime.lean` and `WittMutationLogThreeRuntime.lean`.

For the unary-unbiased line, `StaticUnaryUnbiasedMutation.lean` owns only the operator law, radius/one-bit/mean-strength quantities, and induced transition facts. `StaticUnaryUnbiasedLinearDrift.lean` owns the exact singleton drift/decomposition layer. `StaticUnaryUnbiasedFlipMarginals.lean` owns coordinate-marginal and radius-moment facts. `StaticUnaryUnbiasedPairMarginals.lean` owns pair-event symmetry and the first two-coordinate bounds. `StaticUnaryUnbiasedPairNormalization.lean` owns the exact ordered-pair double count and normalization. `StaticUnaryUnbiasedAcceptedEventBridge.lean` owns the generic event-mass/Bayes bookkeeping needed to turn that exact pair law into a corrected conditional coefficient. `StaticUnaryUnbiasedLinearAcceptedEvents.lean` owns the concrete positive-linear accepted pivot events, their singleton/support/disjointness facts, and the direct Stage-73 instantiation. `StaticUnaryUnbiasedLinearLossDecomposition.lean` owns the generic accepted-event left/right coordinate split, exact pointwise `Delta_L + Delta_R` identity, and corrected region-wide right-loss proxy. `StaticUnaryUnbiasedCorrectedPotential.lean` owns the corrected penalty ratio, geometric baseline, suffix-min objective clipping, and concrete reversed anchor. `StaticUnaryUnbiasedCorrectedPotentialEnvelope.lean` owns the anchor-candidate representation, anchor gamma lower envelope, corrected-potential `L/R` instantiation, and the reduction of the whole right-region loss to a pure geometric gamma tail. `StaticUnaryUnbiasedCorrectedGammaTail.lean` owns the finite geometric-tail reindexing/closed identity and the singleton-rate-scaled right-loss envelope. `StaticUnaryUnbiasedCorrectedLeftGain.lean` owns the suffix ratio geometry, pointwise nonnegativity of the accepted left contribution, and the event-weighted singleton lower bound. Actual unconditioning of the right-loss proxy and per-pivot drift assembly remain in later modules. Do not encode a literature conditional probability step until the corresponding conditioning measure has been formalized correctly.

## 5. Compiler-feedback discipline

When a pinned build fails:

1. identify the first genuine diagnostic;
2. distinguish mathematical failure from elaboration/simplification/API issues;
3. make the smallest justified repair;
4. avoid unrelated cleanup in a repair-only round;
5. keep proof comments synchronized with the actual argument;
6. update the research state when the mathematical boundary changes.

Do not increase heartbeats or add broad automation merely to conceal avoidable proof-structure problems.

## 6. Repository hygiene

The maintained repository should contain source, configuration, current documentation, and current verification/export tooling only.

Do not retain generated build trees, build-result directories, logs, review summaries, exported ZIPs/checksum sidecars, obsolete patch archives, obsolete runners/exporters, editor artifacts, or historical theorem modules that no longer contribute to the maintained API/proof graph.

The root `ECRuntime.lean` should import the maintained integration graph. Before delivery, statically verify that every `import ECRuntime.*` resolves and every maintained module is reachable from the root aggregator.

## 7. Documentation roles

- `README.md`: current repository overview and build command;
- `DEVELOPMENT.md`: invariant workflow rules;
- `docs/PROJECT_STATE.tex`: current verified theorem inventory, promoted boundary, and next mathematical step;
- `docs/LITERATURE_ROADMAP.md`: literature mapping and prioritized future theorem families;
- `HISTORY.md`: compact milestone history.

Do not duplicate per-fix chronology across all documents.

## 8. Verification runners

There is **one** runner, `scripts/verify.sh`, and it is stage-agnostic. The stage is an
argument. Promoting a stage no longer means copying the runner to a new filename and
updating it, the exporter's `VERSION`, and `README.md` in lockstep.

It performs:

1. root/source-hygiene preflight (`scripts/hygiene.py`);
2. environment capture;
3. `lake exe cache get`;
4. the designated focused target (`--focus`);
5. complete `lake build`;
6. the `ECRuntimeTest` regression suite;
7. warning/error scan;
8. whitelist source export and manifest;
9. compact review summary under `.verify/stage-<N>/`.

Do not explicitly rebuild historical targets before the full root build.

Results are written inside the repository under the ignored `.verify/` directory. Nothing
is written outside the repository root.

The hygiene preflight measures reachability from the **public facades**, not from
`ECRuntime.lean`. The root aggregator imports almost every module directly, so a
root-reachability check passes by construction and can never detect a module nothing
consumes. Facades are listed in `scripts/hygiene.py`; add one when a stage promotes one.

## 9. Export discipline

Exports are source-only and reproducible. The exporter must produce a repository ZIP, SHA-256 sidecar, and deterministic source manifest. Unexpected files in the manifest are a hygiene failure.

## 10. Deliverables for iterative rounds

For each substantive modification return:

- the gate table from `scripts/verify.sh`, verbatim, including any gate that failed;
- what the stage promotes, and what it deliberately defers;
- the `HISTORY.md` entry;
- the source export when an archival snapshot is wanted (`scripts/export_repository.py`).

The export remains a reproducibility and hygiene check — a whitelist plus a deterministic
manifest, so an unexpected file in the tree is a failure. It is no longer the mechanism by
which a change is transported or reviewed.

Patch applicators must handle deletions explicitly.

## 11. Current mathematical frontier

Compiler-promoted at Stage 67:

- exact finite Witt C3/drift boundary `0 <= c <= log 3`, `n >= 4`;
- finite expectation, geometric-tail, and shifted-exponential runtime interfaces on `0 < c <= log 3`;
- fixed-scale singleton-rate asymptotics with normalized factor `exp(c)/c` for every fixed `c > 0`.

The finite-boundary Witt branch is frozen.

Compiler-promoted at Stage 68 fix 1:

- static unary-unbiased mutation laws on masks;
- derived mutation-radius distribution;
- exact one-bit mass `p₁` and mean radius `χ` interfaces;
- exact specified-singleton and aggregate single-zero-flip weights;
- independent bit mutation as an instance;
- induced elitist stochastic transition.

Compiler-promoted at Stage 69 fix 1:

- generic drift-as-mask-sum for static unary-unbiased transitions;
- per-coordinate singleton rate `p₁/n`;
- exact singleton contribution for arbitrary linear-error coefficients;
- rank-potential singleton specialization;
- exact rank-drift split into singleton term plus non-singleton remainder;
- coefficient-sensitive objective-error multiplicative drift at rate `p₁/n`.

Stage 70 fix 1 promoted:

- actual coordinate-flip event mass and coordinate-swap invariance;
- exact `Pr[i flips] = χ/n`;
- unconditional shifted radius moment and its `<= χ` bound;
- second factorial radius moment as the correct quantity for pair-flip analysis.

Compiler-promoted through Stage 79 fix 1:

- exact pair normalization and size-biased second-coordinate law;
- generic accepted-event bridge with coefficient `E[K(K-1)]/(p₁(n-1))`;
- concrete accepted leftmost-error pivot events for positive ordered linear functions;
- exact accepted-step `Delta_L + Delta_R` decomposition and corrected region-wide right-loss proxy bound;
- corrected calibration `rho = chi E[K(K-1)] / ((n-1)p₁^2)`, geometric baseline, suffix-min objective clipping, concrete reversed anchor, and corrected linear potential;
- anchor envelope, closed corrected gamma-tail identity, and singleton-rate-scaled right-loss envelope.

Stage 79 fix 1 is promoted. It adds the corrected suffix-ratio geometry, pointwise nonnegative accepted left contribution, exact singleton left gain, and event-weighted lower bound `(p₁/n) g_i`. Its first pinned build exposed only three local proof-engineering diagnostics; Fix 1 repaired those points without changing the theorem surface, and the focused plus complete root builds then verified warning/error-free. Event-weighted right-loss unconditioning remains the next research boundary; no Stage-80 theorem candidate is introduced in the current literature-checkpoint update.
