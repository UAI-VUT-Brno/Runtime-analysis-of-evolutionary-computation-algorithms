---
paper: doerr-johannsen-winzen-2012
aliases: [P04]
roadmap: ../../roadmap/papers/doerr-johannsen-winzen-2012.md
---

# P04 — Doerr, Johannsen and Winzen (2012): multiplicative drift (~30%)

**Verified headline specializations**

1. **Finite-state multiplicative-drift expected-time theorem:**
   [`multiplicativeDrift_runtimeSup_le`](../../../ECRuntime/MultiplicativeDrift.lean)
   and [`multiplicativeDrift_finiteHorizonBound`](../../../ECRuntime/MultiplicativeDrift.lean)
   yield the logarithmic-potential runtime certificate.
2. **Associated hitting-time tail/survival bound:**
   [`multiplicativeDrift_firstHittingTime_tailMass_le`](../../../ECRuntime/MultiplicativeDriftTail.lean).
3. **Linear objective special case** via positive-linear mutation
   certificates, including
   [`wittStandard_runtimeSup_le_asymptotic_upperBound`](../../../ECRuntime/WittStandardRuntimeAsymptotics.lean).
   This is mathematical overlap with the drift paper, not a separate proof of
   its originally published constant `1.39e` argument.

**Not yet verified headline families**

- The paper's **specific `(1.39+o(1))e n ln n`** proof in its own
  parameterization and its **matching lower `e n ln n`** result.
- Complete **minimum-spanning-tree, shortest-path, and Euler-tour**
  applications and their problem-specific constants.
- Any **general-state-process formulation** beyond the finite Markov-state
  assumptions actually used by the certified modules.
