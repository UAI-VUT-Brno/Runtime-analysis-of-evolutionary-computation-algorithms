---
paper: doerr-janett-lengler-2024
targets: [A1]
current: ../../current/papers/doerr-janett-lengler-2024.md
---

# Doerr, Janett & Lengler (2024)

> Queue status for A1 is in [`frontier.toml`](../frontier.toml).
> What is already certified for this paper: [`current/papers/doerr-janett-lengler-2024.md`](../../current/papers/doerr-janett-lengler-2024.md).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## A1. Doerr, Janett & Lengler (2024): finish the static unary-unbiased linear theorem

**Paper:** C. Doerr, D. A. Janett, J. Lengler, *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*, Algorithmica 86(10), 3115--3152, DOI `10.1007/s00453-024-01258-9`.

**Paper result:** asymptotically tight `n log n / p_1` runtime under conditions on `p_1` and expected mutation strength `chi`, with distinct upper- and lower-bound arguments.

**Why reachable:** this is the exact chain currently being reconstructed. Operator semantics, exact pair moments, accepted pivot events, `L/R` decomposition, corrected potential, gamma-tail closure, and left gain are already promoted.

**Remaining formal gap:** event-weighted right-loss unconditioning, per-pivot drift, global multiplicative drift, then reassessment of which published hypotheses suffice with the corrected factorial-moment coefficient. The lower bound remains a separate later task.

## Dependency audit for the 2024 upper bound

> Moved verbatim from the literature roadmap on 2026-10-26; written during stages 70–79, before the 547-module merge.

Reusable without independent-bit factorization:

- finite transition / push-forward expectation semantics;
- accepted-versus-rejected linear potential drops;
- specified singleton mass `p_1/n`;
- multiplicative-drift and runtime/tail infrastructure;
- finite-sum decomposition into a singleton branch and a remainder.

Independent-bit-specific machinery that should **not** be reused as if it were generic:

- Bernoulli mask factorization and erase-balance identities involving `p` and `1-p`;
- survival-power identities used by the Witt `p=c/n` potential;
- C2/C3 estimates whose coefficients are calibrated to independent coordinate survival.

New unary-unbiased ingredients required next:

1. Stage 71 fix 1 promoted: pair-event symmetry and the mask-expectation form of `E[K(K-1)]`;
2. Stage 72 fix 1 promoted: exact ordered-distinct-pair double count, specified-pair normalization, and size-biased pair/coordinate ratio;
3. Stage 73 promoted: generic finite-event bridge yielding `E[K(K-1)]/(p_1(n-1))` for the second-coordinate conditional coefficient;
4. Stage 74 fix 1 promoted: objective-specific accepted/leftmost-error pivot events, singleton/support/disjointness facts, and direct bridge instantiation;
5. Stage 75 fix 1 promoted: generic accepted-event `L/R` coordinate split, exact pointwise potential-drop decomposition, and region-wide corrected factorial-moment right-loss bound;
6. Stage 76 fix 1 promoted: corrected penalty ratio, geometric `gamma_i`, finite suffix-min objective clipping `g_i`, concrete reversed anchor, and corrected linear potential;
7. Stage 77 fix 1 promoted: anchor-candidate representation, `gamma_anchor <= g_i`, corrected-potential `L/R` instantiation, and reduction of the right-region loss to a pure gamma suffix tail;
8. Stage 78 fix 2 promoted: exact finite geometric-tail identity, anchor-scaled tail bound, and singleton-rate-scaled corrected right-loss envelope;
9. Stage 79 fix 1 promoted: corrected suffix ratio geometry, pointwise nonnegative accepted left contribution, exact singleton left gain, and event-weighted lower bound `(p_1/n) g_i`; the focused module and complete root build verified warning/error-free;
10. certified by the 547-module merge, not through a recorded stage: event-weighted right-loss unconditioning, per-pivot drift assembly, the global multiplicative-drift lower bound for the actual transition, the runtime certificate, and a sharp `1/p_1` upper envelope under a uniform bound on `χ E[K(K-1)]/p_1²` (see "Merged results").

The lower-bound half should remain postponed: the paper explicitly shows that the standard stochastic-domination route does not transfer to arbitrary static unary-unbiased operators.
