---
paper: friedrich-et-al-2025
targets: [D6]
---

# Friedrich, Kötzing, Neumann, Neumann & Radhakrishnan (2025)

> Queue status for D6 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## D6. Friedrich, Kötzing, Neumann, Neumann & Radhakrishnan (2025): LeadingOnes with Constraints

**Paper:** Algorithmica 87, 661--689, DOI `10.1007/s00453-025-01298-9`.

**Result:** tight `Theta(nB + n(n-B) log B)` runtime for a cardinality-constrained LeadingOnes instance, plus study of stochastic constraints.

**Why reachable:** the unconstrained exact LeadingOnes chain is already one of the most mature parts of the repository. The new work is feasible-state/constraint semantics and the additional Markov-chain analysis induced by neutral bits.
