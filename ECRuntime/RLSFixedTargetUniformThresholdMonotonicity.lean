import ECRuntime.RLSFixedTargetThresholdAntitonicity
import ECRuntime.RLSFixedTargetUniformBinomialFormula
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 266 (P07). Monotonicity of the *genuine* uniformly initialized
fixed-target runtime, not merely a numerical binomial formula. The input
is the statewise runtime theorem from Stage 262.
-/

/-- Increasing the allowed number of zero bits never increases the uniform
initialization average of RLS hitting-time expectations. -/
theorem proposed_rlsLinear_fixedTarget_uniformRuntime_antitone_threshold
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (r s : Nat) (hrs : r ≤ s) :
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) (rlsZeroAtMost (n := n) s) x).toReal) ≤
    ((Fintype.card (BitString n) : Real)⁻¹) *
      (∑ x : BitString n,
        (runtimeSup
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal) := by
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro x _hx
  exact proposed_rlsLinear_fixedTarget_runtimeReal_antitone_threshold
    hn w hw r s hrs x

end ECRuntime
