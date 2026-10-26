---
paper: doerr-et-al-2011
targets: [C2]
---

# Doerr et al. (2011)

> Queue status for C2 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C2. Doerr et al. (2011): Faster Black-Box Algorithms Through Higher Arity Operators

**Paper:** B. Doerr, D. Johannsen, T. Kötzing, P. K. Lehre, M. Wagner, C. Winzen, FOGA 2011, 163--172, DOI `10.1145/1967654.1967669`.

**Result:** binary unbiased operators reduce LeadingOnes complexity to `O(n log n)` and OneMax to `O(n)`; higher arity further improves OneMax.

**Why reachable:** it is a natural extension after formalizing the unary black-box model. The current bit-string/permutation symmetry infrastructure should transfer, but higher-arity operator invariance is genuinely new.
