import ECRuntime.LeadingOnesFixedTargetCandidate
import Mathlib

namespace ECRuntime

/-!
# Stage 180 pending: monotonicity of the LeadingOnes fixed-target mean

Direction: Buzdalov--Doerr--Doerr--Vinokurov. Raising the target cannot
shorten the expected hitting time. This assertion is proved directly from
the public Stage 169 exact formula, not from an assumed coupling or a
new algorithmic model.

The theorem header is approved after Round 7; admission-free elaboration
alone does not constitute an official promotion.
-/

/-- The uniformly initialized fixed-target expected runtime is
nondecreasing in the target threshold, at fixed nondegenerate rate. -/
theorem proposed_leadingOnes_uniformFixedTarget_mean_monotoneTarget
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k l : Nat) (hkl : k ≤ l) (hl : l ≤ n) :
    leadingOnesUniformFixedTargetMean n p k ≤
      leadingOnesUniformFixedTargetMean n p l := by
  have hk : k ≤ n := hkl.trans hl
  rw [proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 k hk,
      proposed_leadingOnes_uniformFixedTarget_mean_eq_levelSum hp0 hp1 l hl]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : Real) ≤ 1 / 2)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
  intro i hi hnot
  have hp : 0 ≤ 1 - p := by linarith
  exact inv_nonneg.mpr (mul_nonneg hp0.le (pow_nonneg hp i))

end ECRuntime
