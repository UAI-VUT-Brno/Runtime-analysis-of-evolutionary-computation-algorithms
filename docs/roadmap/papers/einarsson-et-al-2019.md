---
paper: einarsson-et-al-2019
targets: [A8]
---

# Einarsson et al. (2019)

> Queue status for A8 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## A8. Einarsson et al. (2019): Linear Hidden Subset with scheduled/adaptive mutation rates

**Paper:** H. Einarsson, M. M. Gauy, J. Lengler, F. Meier, A. Mujika, A. Steger, F. Weissenberger, *The Linear Hidden Subset Problem for the (1+1) EA with Scheduled and Adaptive Mutation Rates*, TCS 785, 150--170, DOI `10.1016/j.tcs.2019.05.021`.

**Result:** optimal scheduled runtime with constant `beta≈3.552` and adaptive runtime `(1+o(1)) e n log n` when the number of relevant bits is unknown.

**Why reachable:** current linear-function semantics and `p=c/n` asymptotics can be reused. The substantial new component is a time/history-dependent mutation schedule.
