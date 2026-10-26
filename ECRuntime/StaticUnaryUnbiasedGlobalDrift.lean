import ECRuntime.StaticUnaryUnbiasedPivotPartition
import ECRuntime.StaticUnaryUnbiasedLinearDrift
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Global corrected drift for static unary-unbiased mutation

The first result sums the Stage-81 corrected event-restricted lower bound
using the exact signed Stage-82 partition. The second independently identifies
the unnormalized mask-weighted drop with the drift of the finite transition
kernel. The third combines these facts into a global one-step multiplicative
drift inequality.

No probability independence, pointwise nonnegativity of accepted potential
drops, or unproved mean-only conditional loss bounds are assumed. The result
uses the corrected factorial-moment coefficients and positive nonincreasing
objective weights. The rate is strictly positive when alpha > 1 and p1 > 0.

This is a one-step drift result, not a first-hitting-time or paper-level
runtime theorem. It remains a candidate until verified by the pinned compiler.
-/

/-- Summing the corrected event-level estimates over the exact signed pivot
partition bounds the unrestricted mask-weighted expected decrease. This
statement does not require the slack factor to be nonnegative. -/
theorem acceptedEventWeightedPotentialDrop_univ_corrected_lower_bound
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedLinearPotential alpha w x) ≤
      law.acceptedEventWeightedPotentialDrop Finset.univ w
        (law.correctedPotentialWeight alpha w) x := by
  calc
    (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedLinearPotential alpha w x) =
      ∑ i ∈ zeroPositions x,
        (law.oneBitMass / (n : ℝ)) *
          ((1 - 1 / alpha) * law.correctedPotentialWeight alpha w i) := by
        rw [correctedLinearPotential, linearErrorPotential_eq_sum_zeroPositions]
        simp only [Finset.mul_sum]
    _ ≤ ∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (acceptedLeftmostZeroEvent w x i) w
          (law.correctedPotentialWeight alpha w) x := by
        apply Finset.sum_le_sum
        intro i hi
        exact law.acceptedLeftmostZeroEvent_correctedWeightedPotentialDrop_lower_bound
          hn hp1 halpha w hw hmono x i ((mem_zeroPositions x i).mp hi)
    _ = law.acceptedEventWeightedPotentialDrop Finset.univ w
        (law.correctedPotentialWeight alpha w) x :=
      (law.acceptedEventWeightedPotentialDrop_univ_eq_sum_pivots
        w (law.correctedPotentialWeight alpha w) hw x).symm

/-- The corrected finite mask-weighted potential drop is precisely one-step
drift under the induced elitist transition kernel, with no additional
assumption on the mutation distribution or the objective weights. -/
theorem correctedLinearPotential_drift_eq_acceptedEventWeightedPotentialDrop_univ
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (alpha : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    driftAt (law.transition (linearFitness w))
        (law.correctedLinearPotential alpha w) x =
      law.acceptedEventWeightedPotentialDrop Finset.univ w
        (law.correctedPotentialWeight alpha w) x := by
  rw [law.drift_eq_mask_sum]
  rfl

/-- The corrected potential has a global one-step multiplicative drift lower
bound when alpha > 1. The coefficient `(p1/n) * (1 - 1/alpha)` is strictly
positive under these assumptions; hitting-time bounds require separate
process-level hypotheses and are not asserted here. -/
theorem correctedLinearPotential_global_multiplicative_drift_lower_bound
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 1 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) :
    (law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha) *
        law.correctedLinearPotential alpha w x ≤
      driftAt (law.transition (linearFitness w))
        (law.correctedLinearPotential alpha w) x := by
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  calc
    (law.oneBitMass / (n : ℝ)) * (1 - 1 / alpha) *
        law.correctedLinearPotential alpha w x =
      (law.oneBitMass / (n : ℝ)) *
        ((1 - 1 / alpha) * law.correctedLinearPotential alpha w x) := by ring
    _ ≤ law.acceptedEventWeightedPotentialDrop Finset.univ w
        (law.correctedPotentialWeight alpha w) x :=
      law.acceptedEventWeightedPotentialDrop_univ_corrected_lower_bound
        hn hp1 halphaPos w hw hmono x
    _ = driftAt (law.transition (linearFitness w))
        (law.correctedLinearPotential alpha w) x :=
      (law.correctedLinearPotential_drift_eq_acceptedEventWeightedPotentialDrop_univ
        alpha w x).symm

end StaticUnaryUnbiasedMutation
end ECRuntime
