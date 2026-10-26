---
paper: doerr-janett-lengler-2024
aliases: [P11]
roadmap: ../../roadmap/papers/doerr-janett-lengler-2024.md
---

# P11 — Doerr, Janett and Lengler (2024): static unary unbiased mutation (~20% support; 0% unrestricted headline bounds)

**Verified supporting theorems and restricted consequences**

1. **Coordinate-flip marginal (paper Lemma 2-type statement):**
   [`coordinateFlipMass_eq_meanRadius_div`](../../../ECRuntime/StaticUnaryUnbiasedFlipMarginals.lean)
   proves uniform coordinate mass `E[K]/n` for the certified symmetric-radius
   mutation-law model.
2. **Mutation-radius moment and pair-marginal inequalities:**
   [`proposed_secondFactorialRadiusMoment_le_dimPred_mul_meanRadius`](../../../ECRuntime/StaticUnarySecondFactorialRadiusBound.lean)
   and related bounds in
   [`StaticUnaryUnbiasedPairMarginals.lean`](../../../ECRuntime/StaticUnaryUnbiasedPairMarginals.lean).
3. **Restricted corrected-potential upper estimates:**
   [`correctedLinearPotential_runtimeSup_le_sharpUpper_uniform_moments`](../../../ECRuntime/StaticUnaryUnbiasedSharpMomentUpper.lean)
   and [`correctedLinearPotential_runtimeSup_le`](../../../ECRuntime/StaticUnaryUnbiasedCorrectedRuntime.lean).
   The former has explicit *extra uniform moment requirements*; it is not
   automatically the paper's full general-linear upper theorem.
4. **Separate OneMax/unary lower-drift special cases**, e.g.
   [`proposed_unaryOneMax_harmonicRuntime_of_scaledDriftCap`](../../../ECRuntime/UnaryOneMaxHarmonicLowerScaled.lean),
   address the stated drift-cap subclass, not arbitrary accepted-event
   behavior on positive linear functions.

**Not yet verified headline results**

- **General sharp upper** `(1+o(1)) n ln n / p₁` for the original source's
  full permitted static unary-unbiased operator class, mean-radius bounds
  and assumptions *without strengthening them to second-moment conditions*.
- **General matching lower** bound under the original (potentially different)
  constraints on `p₁`, mean radius `χ` and the initial distribution.
- **Unbounded-mean-radius contrasting examples** and their source-specific
  qualitative trajectory/runtime conclusions.

**Do not count the two unrestricted headline theorems as proved.** The
accepted-event radius and size-bias issues are not discharged by a coordinate
marginal identity alone. The percentage refers to selected supporting and
restricted result families only.
