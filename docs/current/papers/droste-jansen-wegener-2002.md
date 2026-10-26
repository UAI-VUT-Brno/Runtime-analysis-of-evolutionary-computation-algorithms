---
paper: droste-jansen-wegener-2002
aliases: [P12]
roadmap: ../../roadmap/papers/droste-jansen-wegener-2002.md
---

# P12 — Droste, Jansen and Wegener (2002): `(1+1)` EA (~15% overlapping consequence)

**Verified mathematical overlap**

1. **Positive-linear `O(n log n)` expected runtime at the standard
   `p=1/n` rate**, as a consequence of the *later, sharper*
   [`wittStandard_runtimeSup_le_asymptotic_upperBound`](../../../ECRuntime/WittStandardRuntimeAsymptotics.lean)
   and [`wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n`](../../../ECRuntime/WittStandardRuntimeAsymptotics.lean).
   This is a consequence under the Lean weight assumptions, **not** a
   standalone re-formalization of the 2002 paper's proof.

**Not yet verified headline families**

- The paper's **necessary mutation-rate regime** claims and large-rate
  examples showing that the `O(n log n)` behavior need not persist.
- **Exponential-time examples for a degree-two polynomial and a unimodal
  function**.
- The source's **hierarchy theorem and remaining complexity separations**.
  No certified source theorem is currently mapped to those claims.
