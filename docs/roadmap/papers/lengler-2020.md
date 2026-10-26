---
paper: lengler-2020
targets: [C11]
---

# Lengler (2018/2020)

> Queue status for C11 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C11. Lengler (2018/2020): A General Dichotomy of Evolutionary Algorithms on Monotone Functions

**Paper:** J. Lengler, *A General Dichotomy of Evolutionary Algorithms on Monotone Functions*, IEEE Transactions on Evolutionary Computation 24(6), 995--1009 (2020), DOI `10.1109/TEVC.2019.2917014`; arXiv:1803.09227.

**Result:** a broad efficient/inefficient dichotomy for monotone functions. For fast mutation algorithms, the key parameter is the ratio `m_2/m_1` of the second and first falling moments of the mutation strength.

**Why reachable:** this is exceptionally close to the new repository interface: `meanRadius` is `m_1`, while `secondFactorialRadiusMoment` is exactly `m_2`. The pair-normalization work from Stages 70--72 therefore supplies the central mutation-distribution statistics already.
