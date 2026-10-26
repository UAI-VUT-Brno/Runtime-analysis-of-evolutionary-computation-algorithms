---
paper: doerr-kelley-2024
targets: [D2]
---

# Doerr & Kelley (2024)

> Queue status for D2 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D2. Doerr & Kelley (2024): Fourier Analysis Meets Runtime Analysis -- Precise Runtimes on Plateaus

**Paper:** B. Doerr, A. J. Kelley, Algorithmica 86(8), 2479--2518, DOI `10.1007/s00453-024-01232-5`.

**Result:** precise plateau runtimes via discrete Fourier analysis, including a LeadingOnes-style sequence of plateaus and optimal static/fitness-dependent mutation rates.

**Why reachable:** the repository's LeadingOnes occupation machinery and arbitrary-rate formulas provide the sequential-level side. The genuinely new ingredient is finite-group Fourier analysis.
