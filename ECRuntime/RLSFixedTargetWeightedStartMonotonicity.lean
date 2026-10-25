import ECRuntime.RLSFixedTargetThresholdAntitonicity
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 269 (P07, proposed). The pointwise fixed-target theorem implies
monotonicity for *any* nonnegative finite initial weighting, not only for
uniform initialization. This is an interface for nonuniform-start
fixed-target analysis.
-/

/-- A nonnegative-weighted initial ensemble inherits fixed-target runtime
antitonicity from the pointwise RLS hitting-time law. Normalization is not
required, so it also applies to unnormalized subprobability weights. -/
theorem proposed_rlsLinear_fixedTarget_weightedRuntime_antitone_threshold
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (r s : Nat) (hrs : r ≤ s)
    (initialWeight : BitString n → Real)
    (hWeight : ∀ x : BitString n, 0 ≤ initialWeight x) :
    (∑ x : BitString n, initialWeight x *
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w)) (rlsZeroAtMost (n := n) s) x).toReal) ≤
    (∑ x : BitString n, initialWeight x *
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w)) (rlsZeroAtMost (n := n) r) x).toReal) := by
  apply Finset.sum_le_sum
  intro x _hx
  exact mul_le_mul_of_nonneg_left
    (proposed_rlsLinear_fixedTarget_runtimeReal_antitone_threshold
      hn w hw r s hrs x) (hWeight x)

end ECRuntime
