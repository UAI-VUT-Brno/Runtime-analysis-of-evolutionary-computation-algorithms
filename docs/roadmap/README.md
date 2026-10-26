# Literature roadmap

> **Priorities and the near-term plan.** The queue of targets is
> [`frontier.toml`](frontier.toml), one file per candidate paper is in
> [`papers/`](papers/README.md), the current coverage is in
> [`current/`](../current/README.md), and the stage chronology is in
> [`history/`](../history/README.md).

For the comprehensive compiler-certified theorem catalogue, source-paper mapping, search methodology, and the 2026-09-25 survey of more than twenty reachable next papers, see the archived [`FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`](../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md); its per-paper frontier entries now live in [`papers/`](papers/README.md). This file remains the shorter proof-order roadmap.

## Purpose

This document maps the maintained ECRuntime proof layers to literature-facing theorem families and records the next research priorities. Compiler-fix chronology is intentionally omitted.

## Active priority A: static unary-unbiased mutation on linear functions

Principal target:

- Carola Doerr, Duri Andrea Janett, and Johannes Lengler, *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*, Algorithmica 86(10) (2024), 3115--3152, DOI 10.1007/s00453-024-01258-9.

The literature characterizes a static unary-unbiased operator by a distribution on the number of flipped bits followed by a uniform choice of that many coordinates. The central runtime scale is

```text
(1 ± o(1)) n log n / p_1,
```

where `p_1` is the probability of flipping exactly one bit. The theorem also places conditions on `p_1` and on the expected mutation strength `χ`; the upper- and lower-bound assumptions are not identical.

The stage-by-stage notes for this priority (stages 68–79) are in [`history/doerr-janett-lengler-2024.md`](../history/doerr-janett-lengler-2024.md); the dependency audit and ingredient list for the 2024 upper bound are in [`papers/doerr-janett-lengler-2024.md`](papers/doerr-janett-lengler-2024.md).

## Priority B: general drift theorems driven by a concrete application

Candidates include variable drift with explicit integral bounds, lower-bound drift theorems, stronger concentration variants, and phase/restart interfaces. Add these when a selected EC theorem requires them rather than speculatively.

## Priority C: unary-unbiased black-box complexity

This would broaden the repository from fixed-algorithm runtime analysis to complexity of algorithm classes. It requires new machinery for randomized query algorithms, information histories, admissible operator classes, and lower-bound/minimax arguments, so it should follow the nearer-term static unary-unbiased mutation extension.

## Priority D: monotone/dynamic functions

These objective classes would stress-test the current fixed-objective semantics and likely require environment/state extensions.

## Priority E: population and crossover algorithms

Algorithms such as the `(1+(lambda,lambda))` GA are high-value but structurally expensive because they require population states, multi-stage iterations, crossover kernels, and more elaborate cost accounting.

## Near-term plan

The previous plan (steps 1–3 of ingredient 10) is certified by the merge. Open:

1. Define the next Priority-A ingredient. Step 4 of the old plan still stands: only if an additional argument recovers a mean-only estimate should the original `χ`-only statement be reinstated.
2. Alternatively, choose a target from `frontier.toml`. The recommended order there predates the merge, and Tier M is not yet ranked.
