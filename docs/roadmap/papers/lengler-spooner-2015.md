---
paper: lengler-spooner-2015
targets: [A7]
---

# Lengler & Spooner (2015)

> Queue status for A7 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## A7. Lengler & Spooner (2015): Fixed-Budget Performance on Linear Functions

**Paper:** J. Lengler, N. Spooner, *Fixed Budget Performance of the (1+1) EA on Linear Functions*, FOGA XIII, 52--61, DOI `10.1145/2725494.2725506`.

**Result:** a priori and a posteriori fixed-budget guarantees for general linear functions, with especially precise OneMax statements.

**Why reachable:** the repository already has finite-horizon trajectories and drift. The main new interface is to state expected potential/fitness after a fixed number of steps rather than first-hitting time.
