---
paper: doerr-lengler-2016
targets: [C4]
---

# Doerr & Lengler (2016)

> Queue status for C4 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C4. Doerr & Lengler (2016): `(1+1)` elitist black-box complexity of LeadingOnes

**Paper:** C. Doerr, J. Lengler, GECCO 2016, 1131--1138, DOI `10.1145/2908812.2908922`.

**Result:** `Omega(n^2)` `(1+1)` elitist black-box complexity for LeadingOnes, matched by `(1+1)`-type EAs.

**Why reachable:** unlike unrestricted higher-arity results, this stays close to the repository's existing elitist transition semantics. The main missing tool is information-theoretic adversarial reasoning over a function class.
