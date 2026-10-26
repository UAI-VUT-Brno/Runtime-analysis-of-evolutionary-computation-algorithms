---
paper: buzdalov-doerr-2021
targets: [C9]
---

# Buzdalov & Doerr (2021)

> Queue status for C9 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C9. Buzdalov & Doerr (2021): Optimal Static Mutation Strength Distributions for `(1+lambda)` EA on OneMax

**Paper:** M. Buzdalov, C. Doerr, *Optimal Static Mutation Strength Distributions for the (1+lambda) Evolutionary Algorithm on OneMax*, GECCO 2021, 660--668, DOI `10.1145/3449639.3459389`; arXiv:2102.04944.

**Result:** computes optimal *static distributions* over mutation strengths and shows that these distributions can be structurally nontrivial.

**Why reachable:** the repository already represents an arbitrary static unary-unbiased radius distribution. Extending from one offspring to `lambda` offspring would make this an unusually natural target.
