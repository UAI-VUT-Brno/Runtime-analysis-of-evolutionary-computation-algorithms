import ECRuntime.LeadingOnesFixedTargetIncrement
import Mathlib

namespace ECRuntime

/-! Stage 236 (pending approval): a target-to-target second finite
difference for uniform-start LeadingOnes at a fixed interior mutation rate.
This goes beyond the discrete-convexity inequality of Stage 230 and remains
an independent candidate of the fixed-target analysis track. -/

/-- The discrete curvature of the uniform-start LeadingOnes fixed-target
expected runtime has an exact, strictly positive geometric closed form. -/
theorem proposed_leadingOnes_uniformFixedTarget_curvatureFormula
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k + 2 ≤ n) :
    (leadingOnesUniformFixedTargetMean n p (k + 2) -
      leadingOnesUniformFixedTargetMean n p (k + 1)) -
      (leadingOnesUniformFixedTargetMean n p (k + 1) -
        leadingOnesUniformFixedTargetMean n p k) =
      (1 / 2 : Real) * ((1 - p) ^ (k + 1))⁻¹ := by
  have hk0 : k < n := by omega
  have hk1 : k + 1 < n := by omega
  have hi0 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 k hk0
  have hi1 := proposed_leadingOnes_uniformFixedTarget_increment hp0 hp1 (k + 1) hk1
  have hq : 1 - p ≠ 0 := ne_of_gt (by linarith : 0 < 1 - p)
  have hp : p ≠ 0 := ne_of_gt hp0
  have hqpow : (1 - p) ^ k ≠ 0 := pow_ne_zero _ hq
  have hqpow1 : (1 - p) ^ (k + 1) ≠ 0 := pow_ne_zero _ hq
  have hfirst :
      leadingOnesUniformFixedTargetMean n p (k + 1) -
        leadingOnesUniformFixedTargetMean n p k =
          (1 / 2 : Real) * (p * (1 - p) ^ k)⁻¹ := by
    rw [hi0]
    ring
  have hsecond :
      leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1) =
          (1 / 2 : Real) * (p * (1 - p) ^ (k + 1))⁻¹ := by
    rw [hi1]
    ring
  rw [hfirst, hsecond, pow_succ]
  field_simp
  ring

end ECRuntime
