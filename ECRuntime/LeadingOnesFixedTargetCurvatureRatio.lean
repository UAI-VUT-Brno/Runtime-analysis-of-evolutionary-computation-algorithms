import ECRuntime.LeadingOnesFixedTargetCurvatureFormula
import Mathlib

namespace ECRuntime

/-! Stage 237 (pending statement approval): the discrete curvature of the
uniform-start LeadingOnes fixed-target runtime grows geometrically in the
target. This is a refinement of the fixed-target structural analysis. -/

/-- Raising the target by one multiplies the discrete curvature by
`(1-p)⁻¹`, as long as both second differences exist. -/
theorem proposed_leadingOnes_uniformFixedTarget_curvatureGeometricRatio
    {n : Nat} {p : Real} (hp0 : 0 < p) (hp1 : p < 1)
    (k : Nat) (hk : k + 3 ≤ n) :
    ((leadingOnesUniformFixedTargetMean n p (k + 3) -
        leadingOnesUniformFixedTargetMean n p (k + 2)) -
      (leadingOnesUniformFixedTargetMean n p (k + 2) -
        leadingOnesUniformFixedTargetMean n p (k + 1))) =
      (1 - p)⁻¹ *
        ((leadingOnesUniformFixedTargetMean n p (k + 2) -
            leadingOnesUniformFixedTargetMean n p (k + 1)) -
          (leadingOnesUniformFixedTargetMean n p (k + 1) -
            leadingOnesUniformFixedTargetMean n p k)) := by
  have hk0 : k + 2 ≤ n := by omega
  have hk1 : k + 1 + 2 ≤ n := by omega
  have h0 := proposed_leadingOnes_uniformFixedTarget_curvatureFormula
    hp0 hp1 k hk0
  have h1 := proposed_leadingOnes_uniformFixedTarget_curvatureFormula
    hp0 hp1 (k + 1) hk1
  rw [h1, h0, pow_succ, mul_inv_rev]
  ring

end ECRuntime
